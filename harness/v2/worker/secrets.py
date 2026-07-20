"""Conservative secret-shape detection for fallback prompts and responses."""

from __future__ import annotations

import re
from collections.abc import Iterable


_PATTERNS: tuple[tuple[str, re.Pattern[bytes]], ...] = (
    (
        "private key",
        re.compile(rb"-----BEGIN (?:RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----"),
    ),
    (
        "provider token",
        re.compile(
            rb"(?:"
            rb"\bsk-[A-Za-z0-9_-]{16,}"
            rb"|\bhf_[A-Za-z0-9]{16,}"
            rb"|\bgh[pousr]_[A-Za-z0-9]{20,}"
            rb"|\bgithub_pat_[A-Za-z0-9_]{20,}"
            rb"|\bglpat-[A-Za-z0-9_-]{16,}"
            rb"|\bBearer\s+[A-Za-z0-9._~-]{16,}"
            rb")"
        ),
    ),
    (
        "AWS access key",
        re.compile(rb"(?<![A-Z0-9])(?:AKIA|ASIA)[A-Z0-9]{16}(?![A-Z0-9])"),
    ),
    (
        "credential URL",
        re.compile(rb"https?://[^/\s:@]+:[^@\s/]+@", re.IGNORECASE),
    ),
    (
        "password or API credential assignment",
        re.compile(
            rb"(?:^|[\s,{])['\"]?"
            rb"(?:password|passwd|pwd|api[_-]?key|access[_-]?token|client[_-]?secret)"
            rb"['\"]?\s*[:=]\s*"
            rb"(?:\"[^\"\r\n]{8,}\"|'[^'\r\n]{8,}'|[A-Za-z0-9_./+=:@-]{12,})",
            re.IGNORECASE | re.MULTILINE,
        ),
    ),
)


def secret_kind(
    data: bytes,
    *,
    exact_values: Iterable[str | bytes] = (),
) -> str | None:
    """Return a generic secret class without echoing any matched bytes."""

    for value in exact_values:
        encoded = value.encode("utf-8") if isinstance(value, str) else value
        if encoded and encoded in data:
            return "configured API credential"
    for label, pattern in _PATTERNS:
        if pattern.search(data):
            return label
    return None


__all__ = ["secret_kind"]
