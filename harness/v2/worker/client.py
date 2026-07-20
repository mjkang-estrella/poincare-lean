"""Pinned Leanstral health and explicit fallback one-shot invocation."""

from __future__ import annotations

import json
import math
import os
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from .artifacts import ArtifactStore, WrittenArtifact, canonical_json_bytes, sha256_bytes
from .binding import BindingError, JobBinding, assert_binding_live, bind_live_job
from .secrets import secret_kind
from .snapshot import (
    PromptSnapshot,
    SnapshotError,
    compute_prompt_snapshot,
    persist_prompt_snapshot,
)


MAX_HEALTH_RESPONSE_BYTES = 1024 * 1024
MAX_COMPLETION_RESPONSE_BYTES = 32 * 1024 * 1024


class LeanstralError(RuntimeError):
    """Raised when configuration, health, identity, or inference fails."""


@dataclass(frozen=True)
class LeanstralConfig:
    base_url: str
    model: str
    api_key: str | None = None
    model_revision: str | None = None
    timeout_seconds: float = 300.0
    max_tokens: int = 32_000
    reasoning_effort: str | None = "high"
    temperature: float = 1.0

    @classmethod
    def from_env(cls, env: Mapping[str, str] | None = None) -> "LeanstralConfig":
        values = os.environ if env is None else env
        base_url = values.get("LEANSTRAL_BASE_URL", "").strip()
        model = values.get("LEANSTRAL_MODEL", "").strip()
        if not base_url:
            raise LeanstralError("LEANSTRAL_BASE_URL is required")
        if not model:
            raise LeanstralError("LEANSTRAL_MODEL is required")
        reasoning = values.get("LEANSTRAL_REASONING_EFFORT", "high").strip()
        config = cls(
            base_url=base_url,
            model=model,
            model_revision=(
                values.get("LEANSTRAL_MODEL_REVISION", "").strip() or None
            ),
            api_key=values.get("LEANSTRAL_API_KEY") or None,
            timeout_seconds=_parse_positive_float(
                values.get("LEANSTRAL_TIMEOUT_SECONDS", "300"), "LEANSTRAL_TIMEOUT_SECONDS"
            ),
            max_tokens=_parse_positive_int(
                values.get("LEANSTRAL_MAX_TOKENS", "32000"), "LEANSTRAL_MAX_TOKENS"
            ),
            reasoning_effort=reasoning or None,
            temperature=_parse_temperature(
                values.get("LEANSTRAL_TEMPERATURE", "1.0"), "LEANSTRAL_TEMPERATURE"
            ),
        )
        config.normalized_base_url()
        return config

    def normalized_base_url(self) -> str:
        raw = self.base_url.rstrip("/")
        parsed = urllib.parse.urlsplit(raw)
        if parsed.scheme not in {"http", "https"} or not parsed.netloc:
            raise LeanstralError("LEANSTRAL_BASE_URL must be an http(s) URL")
        if parsed.username or parsed.password:
            raise LeanstralError("LEANSTRAL_BASE_URL must not contain credentials")
        if parsed.query or parsed.fragment:
            raise LeanstralError("LEANSTRAL_BASE_URL must not contain a query or fragment")
        path = parsed.path.rstrip("/")
        if not path.endswith("/v1"):
            path += "/v1"
        return urllib.parse.urlunsplit((parsed.scheme, parsed.netloc, path, "", ""))


@dataclass(frozen=True)
class HealthResult:
    model: str
    served_model_ids: tuple[str, ...]
    status_code: int


@dataclass(frozen=True)
class RunResult:
    job_id: str
    request_id: str
    snapshot: PromptSnapshot
    health: HealthResult
    response_artifact: str
    response_sha256: str
    assistant_artifact: str
    assistant_sha256: str
    evidence_artifact: str
    evidence_sha256: str
    finish_reason: str | None


@dataclass(frozen=True)
class _HttpResult:
    status_code: int
    body: bytes
    content_type: str | None


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Fail redirects closed so credentials never migrate to another origin."""

    def redirect_request(
        self,
        req: urllib.request.Request,
        fp: Any,
        code: int,
        msg: str,
        headers: Any,
        newurl: str,
    ) -> None:
        return None


def _parse_positive_int(value: str, name: str) -> int:
    try:
        parsed = int(value)
    except ValueError as exc:
        raise LeanstralError(f"{name} must be an integer") from exc
    if parsed <= 0:
        raise LeanstralError(f"{name} must be positive")
    return parsed


def _parse_positive_float(value: str, name: str) -> float:
    try:
        parsed = float(value)
    except ValueError as exc:
        raise LeanstralError(f"{name} must be numeric") from exc
    if not math.isfinite(parsed) or parsed <= 0:
        raise LeanstralError(f"{name} must be a finite positive number")
    return parsed


def _parse_temperature(value: str, name: str) -> float:
    try:
        parsed = float(value)
    except ValueError as exc:
        raise LeanstralError(f"{name} must be numeric") from exc
    if not math.isfinite(parsed) or parsed < 0 or parsed > 2:
        raise LeanstralError(f"{name} must be between 0 and 2")
    return parsed


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _headers(config: LeanstralConfig) -> dict[str, str]:
    headers = {"Accept": "application/json", "Content-Type": "application/json"}
    if config.api_key:
        if "\r" in config.api_key or "\n" in config.api_key:
            raise LeanstralError("LEANSTRAL_API_KEY must not contain line breaks")
        headers["Authorization"] = f"Bearer {config.api_key}"
    return headers


def _redacted_headers(headers: Mapping[str, str]) -> dict[str, str]:
    return {
        key: "<redacted>" if key.lower() == "authorization" else value
        for key, value in headers.items()
    }


def _exact_secrets(config: LeanstralConfig) -> tuple[str, ...]:
    return () if not config.api_key else (config.api_key,)


def _record_unsafe_response(
    store: ArtifactStore,
    *,
    route: str,
    status_code: int,
    content_type: str | None,
    body: bytes,
    secret_label: str,
    component: str,
) -> None:
    store.append_event(
        {
            "at": _utc_now(),
            "event": "unsafe_response_rejected",
            "route": route,
            "status_code": status_code,
            "content_type": content_type,
            "component": component,
            "reason": secret_label,
            "raw_sha256": sha256_bytes(body),
            "raw_size_bytes": len(body),
            "raw_persisted": False,
        }
    )


def _reject_unsafe_body(
    body: bytes,
    *,
    config: LeanstralConfig,
    store: ArtifactStore | None,
    route: str,
    status_code: int,
    content_type: str | None,
    component: str = "raw_response",
) -> None:
    label = secret_kind(body, exact_values=_exact_secrets(config))
    if label is None:
        return
    if store is not None:
        _record_unsafe_response(
            store,
            route=route,
            status_code=status_code,
            content_type=content_type,
            body=body,
            secret_label=label,
            component=component,
        )
    raise LeanstralError(
        f"{route} response was rejected as secret-bearing; only safe hash metadata was retained"
    )


def _reject_unsafe_decoded_json(
    body: bytes,
    *,
    config: LeanstralConfig,
    store: ArtifactStore | None,
    route: str,
    status_code: int,
    content_type: str | None,
) -> None:
    try:
        decoded = json.loads(body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return
    normalized = canonical_json_bytes(decoded)
    _reject_unsafe_body(
        normalized,
        config=config,
        store=store,
        route=route,
        status_code=status_code,
        content_type=content_type,
        component="decoded_response",
    )


def _remaining_seconds(deadline: float) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise LeanstralError("fallback wall-clock deadline exhausted")
    return remaining


def _read_bounded(response: Any, route: str, maximum: int) -> bytes:
    length = response.headers.get("Content-Length")
    if length is not None:
        try:
            advertised = int(length)
        except ValueError as exc:
            raise LeanstralError(f"response from {route} has an invalid Content-Length") from exc
        if advertised < 0 or advertised > maximum:
            raise LeanstralError(f"response from {route} exceeds {maximum}-byte body cap")
    body = response.read(maximum + 1)
    if len(body) > maximum:
        raise LeanstralError(f"response from {route} exceeds {maximum}-byte body cap")
    return body


def _request(
    config: LeanstralConfig,
    method: str,
    route: str,
    body: bytes | None = None,
    *,
    deadline: float | None = None,
    max_body_bytes: int,
) -> _HttpResult:
    url = f"{config.normalized_base_url()}{route}"
    request = urllib.request.Request(url, data=body, headers=_headers(config), method=method)
    # The intended endpoint is on the private inference plane. Ignore ambient
    # HTTP proxy variables so prompts cannot be routed through an unrelated
    # proxy inherited from an interactive shell or service manager.
    opener = urllib.request.build_opener(
        urllib.request.ProxyHandler({}),
        _NoRedirectHandler(),
    )
    request_deadline = (
        time.monotonic() + config.timeout_seconds if deadline is None else deadline
    )
    try:
        with opener.open(request, timeout=_remaining_seconds(request_deadline)) as response:
            response_body = _read_bounded(response, route, max_body_bytes)
            _remaining_seconds(request_deadline)
            return _HttpResult(
                status_code=response.status,
                body=response_body,
                content_type=response.headers.get("Content-Type"),
            )
    except urllib.error.HTTPError as exc:
        try:
            response_body = _read_bounded(exc, route, max_body_bytes)
            _remaining_seconds(request_deadline)
            return _HttpResult(
                status_code=exc.code,
                body=response_body,
                content_type=exc.headers.get("Content-Type") if exc.headers else None,
            )
        finally:
            exc.close()
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise LeanstralError(f"request to {route} failed: {exc}") from exc


def _decode_json(body: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise LeanstralError(f"{label} was not a UTF-8 JSON object") from exc
    if not isinstance(value, dict):
        raise LeanstralError(f"{label} was not a JSON object")
    return value


def _parse_health(config: LeanstralConfig, result: _HttpResult) -> HealthResult:
    if result.status_code != 200:
        raise LeanstralError(f"model health returned HTTP {result.status_code}")
    payload = _decode_json(result.body, "model health response")
    data = payload.get("data")
    if not isinstance(data, list):
        raise LeanstralError("model health response has no data array")
    ids = tuple(
        item["id"]
        for item in data
        if isinstance(item, dict) and isinstance(item.get("id"), str)
    )
    if len(ids) != 1 or ids[0] != config.model:
        rendered = ", ".join(repr(model_id) for model_id in ids) or "<none>"
        raise LeanstralError(
            f"endpoint model identity mismatch: expected exactly {config.model!r}, served {rendered}"
        )
    return HealthResult(model=config.model, served_model_ids=ids, status_code=result.status_code)


def check_health(config: LeanstralConfig) -> HealthResult:
    result = _request(
        config,
        "GET",
        "/models",
        max_body_bytes=MAX_HEALTH_RESPONSE_BYTES,
    )
    _reject_unsafe_body(
        result.body,
        config=config,
        store=None,
        route="/models",
        status_code=result.status_code,
        content_type=result.content_type,
    )
    _reject_unsafe_decoded_json(
        result.body,
        config=config,
        store=None,
        route="/models",
        status_code=result.status_code,
        content_type=result.content_type,
    )
    return _parse_health(config, result)


def _assistant_text(payload: dict[str, Any]) -> tuple[str, str | None]:
    choices = payload.get("choices")
    if not isinstance(choices, list) or not choices or not isinstance(choices[0], dict):
        raise LeanstralError("completion response has no first choice")
    choice = choices[0]
    message = choice.get("message")
    if not isinstance(message, dict):
        raise LeanstralError("completion response has no message object")
    content = message.get("content")
    if not isinstance(content, str):
        raise LeanstralError("completion response message content is not text")
    finish_reason = choice.get("finish_reason")
    if finish_reason is not None and not isinstance(finish_reason, str):
        finish_reason = str(finish_reason)
    return content, finish_reason


def _request_id() -> str:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    return f"completion-{timestamp}-{uuid.uuid4().hex[:12]}"


def _bound_deadline(started: float, deadline: float, binding: JobBinding) -> float:
    task_seconds = binding.task["budget"]["wall_clock_minutes"] * 60.0
    deadline = min(deadline, started + task_seconds)
    try:
        lease_expiry = datetime.fromisoformat(
            binding.job["workspace"]["lease_expires_at"].replace("Z", "+00:00")
        ).timestamp()
    except (AttributeError, ValueError) as exc:
        raise BindingError("live Job lease expiry is invalid") from exc
    lease_remaining = lease_expiry - time.time()
    deadline = min(deadline, time.monotonic() + lease_remaining)
    _remaining_seconds(deadline)
    return deadline


def _effective_job_config(
    config: LeanstralConfig, binding: JobBinding
) -> LeanstralConfig:
    sampling = binding.job["backend"]["sampling"]
    if set(sampling) != {"max_tokens", "temperature"}:
        raise BindingError(
            "fallback requires exact Job sampling fields max_tokens and temperature"
        )
    max_tokens = sampling["max_tokens"]
    if (
        isinstance(max_tokens, bool)
        or not isinstance(max_tokens, int)
        or max_tokens < 1
        or max_tokens > binding.task["budget"]["max_output_tokens"]
    ):
        raise BindingError("Job max_tokens is invalid or exceeds the Task budget")
    temperature = sampling["temperature"]
    if (
        isinstance(temperature, bool)
        or not isinstance(temperature, (int, float))
        or not math.isfinite(float(temperature))
        or not 0 <= float(temperature) <= 2
    ):
        raise BindingError("Job temperature is invalid")
    return replace(
        config,
        base_url=binding.endpoint,
        model=binding.model,
        model_revision=binding.model_revision,
        max_tokens=max_tokens,
        temperature=float(temperature),
        reasoning_effort=None,
    )


def _fallback_session_record(
    *,
    binding: JobBinding,
    snapshot: PromptSnapshot,
    config: LeanstralConfig,
    session_id: str,
) -> dict[str, Any]:
    immutable_job_contract = {
        "artifacts": binding.job["artifacts"],
        "attempt": binding.job["attempt"],
        "backend": binding.job["backend"],
        "id": binding.job["id"],
        "task_id": binding.job["task_id"],
        "task_revision": binding.job["task_revision"],
        "workspace": {
            key: binding.job["workspace"][key]
            for key in ("base_commit", "branch", "worktree")
        },
    }
    contract_bytes = canonical_json_bytes(immutable_job_contract)
    return {
        "schema_version": "2.0",
        "kind": "harness-v2-bounded-fallback-session",
        "session_id": session_id,
        "created_at": _utc_now(),
        "job_id": binding.job["id"],
        "task_id": binding.task["id"],
        "task_revision": binding.task["revision"],
        "base_commit": binding.task["base_commit"],
        "branch": binding.job["workspace"]["branch"],
        "lease_owner": binding.lease_owner,
        "backend": {
            "endpoint": binding.endpoint,
            "model": config.model,
            "model_revision": config.model_revision,
            "sampling": binding.job["backend"]["sampling"],
        },
        "immutable_job_contract_sha256": sha256_bytes(contract_bytes),
        "prompt_sha256": snapshot.prompt_sha256,
        "context_sha256": snapshot.context_sha256,
    }


def _write_evidence_manifest(
    *,
    store: ArtifactStore,
    binding: JobBinding,
    snapshot: PromptSnapshot,
    session: WrittenArtifact,
    request_id: str,
    outcome: str,
    artifacts: list[WrittenArtifact],
) -> WrittenArtifact:
    by_path = {artifact.relative_path: artifact for artifact in artifacts}
    document = {
        "schema_version": "2.0",
        "kind": "harness-v2-bounded-fallback-evidence",
        "created_at": _utc_now(),
        "job_id": binding.job["id"],
        "task_id": binding.task["id"],
        "task_revision": binding.task["revision"],
        "request_id": request_id,
        "outcome": outcome,
        "fallback_session_artifact": session.relative_path,
        "fallback_session_sha256": session.sha256,
        "prompt_sha256": snapshot.prompt_sha256,
        "context_sha256": snapshot.context_sha256,
        "artifacts": [
            {
                "path": artifact.relative_path,
                "sha256": artifact.sha256,
                "size_bytes": artifact.size_bytes,
            }
            for artifact in sorted(by_path.values(), key=lambda item: item.relative_path)
        ],
    }
    return store.write_json_once("fallback-evidence.json", document)


def _prepare_bound_snapshot(
    *,
    config: LeanstralConfig,
    job_id: str,
    state_dir: Path | str,
    lease_owner: str,
    lease_token: int,
    started: float,
    deadline: float,
) -> tuple[JobBinding, PromptSnapshot, LeanstralConfig, float]:
    if not config.model_revision:
        raise BindingError("LEANSTRAL_MODEL_REVISION is required for a fallback Job")
    binding = bind_live_job(
        job_id=job_id,
        state_dir=state_dir,
        lease_owner=lease_owner,
        lease_token=lease_token,
        endpoint=config.normalized_base_url(),
        model=config.model,
        model_revision=config.model_revision,
        deadline=deadline,
    )
    deadline = _bound_deadline(started, deadline, binding)
    effective = _effective_job_config(config, binding)
    snapshot = compute_prompt_snapshot(
        task=binding.task,
        repo_root=binding.worktree,
        deadline=deadline,
        exact_secrets=_exact_secrets(effective),
    )
    if (
        snapshot.prompt_sha256 != binding.job["artifacts"]["prompt_sha256"]
        or snapshot.context_sha256 != binding.job["artifacts"]["context_sha256"]
    ):
        raise BindingError(
            "fallback prompt/context hashes differ from the immutable Job; create a fresh Job"
        )
    assert_binding_live(binding, deadline=deadline)
    snapshot = persist_prompt_snapshot(
        snapshot,
        artifact_dir=binding.artifact_dir,
        deadline=deadline,
        allow_identical_existing=True,
    )
    assert_binding_live(binding, deadline=deadline)
    _remaining_seconds(deadline)
    return binding, snapshot, effective, deadline


def snapshot_job(
    *,
    config: LeanstralConfig,
    job_id: str,
    state_dir: Path | str,
    lease_owner: str,
    lease_token: int,
) -> tuple[JobBinding, PromptSnapshot]:
    started = time.monotonic()
    if not math.isfinite(config.timeout_seconds) or config.timeout_seconds <= 0:
        raise LeanstralError("fallback timeout must be a finite positive number")
    deadline = started + config.timeout_seconds
    binding, snapshot, _, deadline = _prepare_bound_snapshot(
        config=config,
        job_id=job_id,
        state_dir=state_dir,
        lease_owner=lease_owner,
        lease_token=lease_token,
        started=started,
        deadline=deadline,
    )
    assert_binding_live(binding, deadline=deadline)
    _remaining_seconds(deadline)
    return binding, snapshot


def run_once(
    *,
    config: LeanstralConfig,
    job_id: str,
    state_dir: Path | str,
    lease_owner: str,
    lease_token: int,
) -> RunResult:
    started = time.monotonic()
    if not math.isfinite(config.timeout_seconds) or config.timeout_seconds <= 0:
        raise LeanstralError("fallback timeout must be a finite positive number")
    deadline = started + config.timeout_seconds
    binding, snapshot, effective, deadline = _prepare_bound_snapshot(
        config=config,
        job_id=job_id,
        state_dir=state_dir,
        lease_owner=lease_owner,
        lease_token=lease_token,
        started=started,
        deadline=deadline,
    )
    disk_budget_bytes = snapshot.task["budget"]["disk_mb"] * 1024 * 1024
    initial_store = ArtifactStore(binding.artifact_dir, max_bytes=disk_budget_bytes)
    session_id = f"fallback-{uuid.uuid4().hex}"
    session_artifact = initial_store.write_json_once(
        "fallback-session.json",
        _fallback_session_record(
            binding=binding,
            snapshot=snapshot,
            config=effective,
            session_id=session_id,
        ),
    )
    store = ArtifactStore(
        binding.artifact_dir,
        max_bytes=disk_budget_bytes,
        event_context={
            "job_id": binding.job["id"],
            "fallback_session_sha256": session_artifact.sha256,
        },
    )
    evidence_artifacts = [*snapshot.artifacts, session_artifact]
    store.append_event(
        {
            "at": _utc_now(),
            "event": "fallback_session_started",
            "session_id": session_id,
            "artifact": session_artifact.relative_path,
            "sha256": session_artifact.sha256,
            "size_bytes": session_artifact.size_bytes,
            "prompt_sha256": snapshot.prompt_sha256,
            "context_sha256": snapshot.context_sha256,
        }
    )

    assert_binding_live(binding, deadline=deadline)
    try:
        health_raw = _request(
            effective,
            "GET",
            "/models",
            deadline=deadline,
            max_body_bytes=min(MAX_HEALTH_RESPONSE_BYTES, disk_budget_bytes),
        )
    except LeanstralError:
        store.append_event(
            {
                "at": _utc_now(),
                "event": "health_request_failed",
                "route": "/models",
                "error_type": "LeanstralError",
            }
        )
        raise
    _reject_unsafe_body(
        health_raw.body,
        config=effective,
        store=store,
        route="/models",
        status_code=health_raw.status_code,
        content_type=health_raw.content_type,
    )
    _reject_unsafe_decoded_json(
        health_raw.body,
        config=effective,
        store=store,
        route="/models",
        status_code=health_raw.status_code,
        content_type=health_raw.content_type,
    )
    assert_binding_live(binding, deadline=deadline)
    health_id = f"health-{_request_id()}"
    health_artifact = store.write_once(f"responses/{health_id}.json", health_raw.body)
    evidence_artifacts.append(health_artifact)
    store.append_event(
        {
            "at": _utc_now(),
            "event": "health_response",
            "request_id": health_id,
            "route": "/models",
            "status_code": health_raw.status_code,
            "content_type": health_raw.content_type,
            "headers": _redacted_headers(_headers(effective)),
            "raw_artifact": health_artifact.relative_path,
            "raw_sha256": health_artifact.sha256,
            "raw_size_bytes": health_artifact.size_bytes,
        }
    )
    health = _parse_health(effective, health_raw)
    _remaining_seconds(deadline)

    payload: dict[str, Any] = {
        "model": effective.model,
        "messages": [{"role": "user", "content": snapshot.prompt}],
        "max_tokens": effective.max_tokens,
        "temperature": effective.temperature,
        "stream": False,
    }
    if effective.reasoning_effort:
        payload["reasoning_effort"] = effective.reasoning_effort
    request_bytes = canonical_json_bytes(payload)
    request_id = _request_id()
    request_artifact = store.write_once(f"requests/{request_id}.json", request_bytes)
    evidence_artifacts.append(request_artifact)
    store.append_event(
        {
            "at": _utc_now(),
            "event": "completion_request",
            "request_id": request_id,
            "route": "/chat/completions",
            "model": effective.model,
            "headers": _redacted_headers(_headers(effective)),
            "sampling": {
                "max_tokens": effective.max_tokens,
                "reasoning_effort": effective.reasoning_effort,
                "temperature": effective.temperature,
                "timeout_seconds": effective.timeout_seconds,
            },
            "raw_artifact": request_artifact.relative_path,
            "raw_sha256": request_artifact.sha256,
            "raw_size_bytes": request_artifact.size_bytes,
            "prompt_sha256": snapshot.prompt_sha256,
            "context_sha256": snapshot.context_sha256,
        }
    )

    assert_binding_live(binding, deadline=deadline)
    try:
        response = _request(
            effective,
            "POST",
            "/chat/completions",
            request_bytes,
            deadline=deadline,
            max_body_bytes=min(MAX_COMPLETION_RESPONSE_BYTES, disk_budget_bytes),
        )
    except LeanstralError:
        store.append_event(
            {
                "at": _utc_now(),
                "event": "completion_request_failed",
                "request_id": request_id,
                "route": "/chat/completions",
                "error_type": "LeanstralError",
            }
        )
        raise
    _reject_unsafe_body(
        response.body,
        config=effective,
        store=store,
        route="/chat/completions",
        status_code=response.status_code,
        content_type=response.content_type,
    )
    _reject_unsafe_decoded_json(
        response.body,
        config=effective,
        store=store,
        route="/chat/completions",
        status_code=response.status_code,
        content_type=response.content_type,
    )
    assert_binding_live(binding, deadline=deadline)
    if response.status_code != 200:
        response_artifact = store.write_once(
            f"responses/{request_id}.json", response.body
        )
        evidence_artifacts.append(response_artifact)
        store.append_event(
            {
                "at": _utc_now(),
                "event": "completion_response",
                "request_id": request_id,
                "route": "/chat/completions",
                "status_code": response.status_code,
                "content_type": response.content_type,
                "raw_artifact": response_artifact.relative_path,
                "raw_sha256": response_artifact.sha256,
                "raw_size_bytes": response_artifact.size_bytes,
            }
        )
        store.append_event(
            {
                "at": _utc_now(),
                "event": "fallback_evidence_finalizing",
                "request_id": request_id,
                "artifact": "fallback-evidence.json",
                "outcome": f"http_{response.status_code}",
            }
        )
        evidence_artifacts.append(store.inspect_existing("events.jsonl"))
        _remaining_seconds(deadline)
        evidence_artifact = _write_evidence_manifest(
            store=store,
            binding=binding,
            snapshot=snapshot,
            session=session_artifact,
            request_id=request_id,
            outcome=f"http_{response.status_code}",
            artifacts=evidence_artifacts,
        )
        _remaining_seconds(deadline)
        raise LeanstralError(f"chat completion returned HTTP {response.status_code}")
    response_payload = _decode_json(response.body, "completion response")
    returned_model = response_payload.get("model")
    if returned_model != effective.model:
        raise LeanstralError(
            f"completion model identity mismatch: expected {effective.model!r}, got {returned_model!r}"
        )
    assistant, finish_reason = _assistant_text(response_payload)
    _reject_unsafe_body(
        assistant.encode("utf-8"),
        config=effective,
        store=store,
        route="/chat/completions",
        status_code=response.status_code,
        content_type=response.content_type,
        component="assistant_message",
    )
    assert_binding_live(binding, deadline=deadline)
    response_artifact = store.write_once(f"responses/{request_id}.json", response.body)
    evidence_artifacts.append(response_artifact)
    store.append_event(
        {
            "at": _utc_now(),
            "event": "completion_response",
            "request_id": request_id,
            "route": "/chat/completions",
            "status_code": response.status_code,
            "content_type": response.content_type,
            "raw_artifact": response_artifact.relative_path,
            "raw_sha256": response_artifact.sha256,
            "raw_size_bytes": response_artifact.size_bytes,
        }
    )
    assistant_artifact = store.write_once(
        f"assistant/{request_id}.md", assistant.encode("utf-8")
    )
    evidence_artifacts.append(assistant_artifact)
    store.append_event(
        {
            "at": _utc_now(),
            "event": "assistant_message",
            "request_id": request_id,
            "finish_reason": finish_reason,
            "artifact": assistant_artifact.relative_path,
            "sha256": assistant_artifact.sha256,
            "size_bytes": assistant_artifact.size_bytes,
        }
    )
    assert_binding_live(binding, deadline=deadline)
    store.append_event(
        {
            "at": _utc_now(),
            "event": "fallback_evidence_finalizing",
            "request_id": request_id,
            "artifact": "fallback-evidence.json",
            "outcome": "completed",
        }
    )
    evidence_artifacts.append(store.inspect_existing("events.jsonl"))
    _remaining_seconds(deadline)
    evidence_artifact = _write_evidence_manifest(
        store=store,
        binding=binding,
        snapshot=snapshot,
        session=session_artifact,
        request_id=request_id,
        outcome="completed",
        artifacts=evidence_artifacts,
    )
    _remaining_seconds(deadline)
    return RunResult(
        job_id=binding.job["id"],
        request_id=request_id,
        snapshot=snapshot,
        health=health,
        response_artifact=response_artifact.relative_path,
        response_sha256=response_artifact.sha256,
        assistant_artifact=assistant_artifact.relative_path,
        assistant_sha256=assistant_artifact.sha256,
        evidence_artifact=evidence_artifact.relative_path,
        evidence_sha256=evidence_artifact.sha256,
        finish_reason=finish_reason,
    )
