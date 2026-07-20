# Harness v2 bounded Pi Job engine

Pi `0.80.10` is the only general agent loop inside a proof Job. Harness v2
still owns the immutable Task/Job contracts, SQLite state, fenced leases,
isolated worktrees, append-only artifacts, and Codex-only
review/acceptance/commit boundary. `harness.v2.worker` retains endpoint health,
deterministic snapshots, and an explicit one-shot fallback only; it is not a
second Job agent.

The execution boundary is:

```text
trusted Harness engine (worktree, lease, journal, evidence)
            ^ exact token-authenticated Unix RPC
bounded Pi process (private tmpfs, no worktree/control/artifact mounts)
            |
            v
Leanstral vLLM endpoint
```

Pi's unrestricted built-ins, discovery, skills, templates, themes, context
files, and approval flows are disabled. The canonical extension exposes only:

- `read_context`
- `search_symbol`
- `apply_patch_scoped`
- `lean_check`
- `git_diff`
- `report_blocked`

Every call crosses an exact, serialized Job/session RPC protocol. The trusted
broker rechecks the live Task, lease generation, branch, HEAD, and file scope;
records a patch intent before mutation; and consumes every call ID/sequence
once. Final success requires replaying the committed patch journal against the
Task base in an isolated Git index and byte-matching the live scoped diff.

## Pin and attest Pi

The committed lock pins `@earendil-works/pi-coding-agent@0.80.10` and
`typebox@1.1.38`. Production refuses arbitrary `--pi-bin` or version-only
authorization. It reattests the explicit Node executable, resolved Pi CLI JS,
its exact semantic version and Pi's `>=22.19.0` engine requirement,
package/lock identity, canonical `npm ls --json --all` graph, and every file,
directory, mode, and internal symlink in the complete install tree before
launch and again before a successful result. The version probe invokes only
the attested absolute Node path under a scrubbed environment.

On `mj-zima`, install into a fresh dedicated prefix and create two separately
sealed inputs outside that tree. The install is made read-only before its
manifest is constructed, because entry modes are part of the attested tree:

```sh
set -euo pipefail
umask 077
CONTROL_TAG=replace-with-clean-control-head
CONTROL_ROOT=/srv/data/poincare-harness/control
PI_ROOT=/srv/data/poincare-harness/pi-0.80.10-$CONTROL_TAG
PI_ATTEST=/srv/data/poincare-harness/pi-attestation-0.80.10-$CONTROL_TAG
test ! -e "$PI_ROOT" && test ! -L "$PI_ROOT"
test ! -e "$PI_ATTEST" && test ! -L "$PI_ATTEST"
install -d -m 0700 "$PI_ROOT" "$PI_ATTEST"
cp "$CONTROL_ROOT/harness/v2/pi/package.json" \
  "$CONTROL_ROOT/harness/v2/pi/package-lock.json" \
  "$PI_ROOT/"
cd "$PI_ROOT"
npm ci --ignore-scripts --engine-strict --no-audit --no-fund
chmod -R a-w -- "$PI_ROOT"
npm ls --json --all > "$PI_ATTEST/npm-ls.raw.json"
PYTHONPATH="$CONTROL_ROOT" python3 -S -P -B - \
  "$PI_ATTEST/npm-ls.raw.json" \
  "$PI_ATTEST/npm-ls.json" \
  "$PI_ATTEST/pi-install.json" \
  "$PI_ROOT" <<'PY'
import json
import os
import sys
from pathlib import Path

from harness.v2.pi.install import (
    build_install_manifest,
    canonical_manifest_bytes,
    probe_node_version,
)

graph = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
install_root = Path(sys.argv[4])
graph_data = json.dumps(
    graph, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(",", ":")
).encode("utf-8")
manifest = build_install_manifest(
    node_executable="/usr/bin/node",
    node_version=probe_node_version("/usr/bin/node"),
    install_root=install_root,
    cli_js_path=install_root / "node_modules/@earendil-works/pi-coding-agent/dist/cli.js",
    npm_dependency_graph=graph,
)
data = canonical_manifest_bytes(manifest)
for path, content in ((sys.argv[2], graph_data), (sys.argv[3], data)):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(content)
        stream.flush()
        os.fsync(stream.fileno())
directory = os.open(os.path.dirname(sys.argv[2]), os.O_RDONLY)
try:
    os.fsync(directory)
finally:
    os.close(directory)
PY
rm "$PI_ATTEST/npm-ls.raw.json"
```

The install and attestation directories must be new, current-user-owned paths.
Do not chmod or otherwise mutate the Pi tree after manifest construction.

The resulting versioned paths go in the private deployment `.env` as
`POINCARE_PI_INSTALL_MANIFEST` and `POINCARE_PI_DEPENDENCY_GRAPH`. Preflight
calls `verify_sealed_install_files`; the Job engine repeats that verification.

Production also requires `LEANSTRAL_BASE_URL`, `LEANSTRAL_MODEL`,
`LEANSTRAL_MODEL_REVISION`, `POINCARE_STATE_DIR`, `HARNESS_PI_BWRAP`,
`HARNESS_PI_SYSTEMD_RUN`, `HARNESS_PI_GIT`, `HARNESS_PI_LAKE_CACHE_ROOT`, and
exactly one toolchain root in `HARNESS_PI_TOOLCHAIN_ROOTS`. The deployment
wrapper passes the two `POINCARE_PI_*` sealed paths through the corresponding
CLI flags.

Optional, bounded decimal overrides are `HARNESS_PI_RUNTIME_TMPFS_BYTES`,
`HARNESS_PI_TMP_TMPFS_BYTES`, `HARNESS_PI_RUN_TMPFS_BYTES`,
`HARNESS_PI_LEAN_MEMORY_MAX_BYTES`, `HARNESS_PI_LEAN_TASKS_MAX`,
`HARNESS_PI_LEAN_CPU_QUOTA_PERCENT`, `HARNESS_PI_LEAN_RLIMIT_AS_BYTES`,
`HARNESS_PI_LEAN_RLIMIT_NPROC`, `HARNESS_PI_LEAN_RLIMIT_NOFILE`,
`HARNESS_PI_LEAN_RLIMIT_FSIZE_BYTES`, `HARNESS_PI_LEAN_RLIMIT_CORE_BYTES`, and
`HARNESS_PI_LEAN_RLIMIT_CPU_SECONDS`. Invalid values fail before Pi launches.

## Sandboxes and evidence

The Pi process runs under Bubblewrap with the attested Node/install and sealed
extension/config/system prompt/private settings read-only, bounded private
tmpfs for its home, session, and temporary data, no
repository/control/state/artifact mount, and a parent-death guard. The settings
file is hash-bound at `/sealed/agent/settings.json`, the sandbox fixes
`PI_CODING_AGENT_DIR=/sealed/agent`, and its exact canonical content disables
Pi auto-compaction. Any compaction extension or JSON-stream event is still a
fail-closed invariant violation. It must share the host network namespace to
reach the configured private vLLM endpoint; this is an explicit residual
boundary, not a destination-level firewall claim. Pi has no network tool and
no host filesystem path to exploit through a scoped tool.

`lean_check` is a separate, networkless sparse sandbox. Each allowed Task
command gets only the exact target/config source snapshot, the
provenance-validated read-only cache for the Task base, and the audited Lean
toolchain. A shared build/Job lock, cgroup-v2 memory/PID/CPU limits, process
rlimits, output caps, deadline, and cleanup fence every check. Context-only
files are broker-readable but absent from Lean's `/work` mount.

All authoritative streams, RPC/tool events, patch intents/blobs, compiler
output, final diff, cross-checks, manifests, and result records use one shared
append-only quota. Pi's tmpfs session is non-authoritative and disappears when
the process exits. The result is evidence only: Codex must independently rerun
the frozen gate, review the exact commit, and alone transition the Job/Task.

## Prompt, event, and token invariants

Pi `0.80.10` trims piped stdin before creating its first user message. Harness
therefore renders a transport-canonical prompt with no leading or trailing
whitespace, records its UTF-8 byte length and SHA-256 in public sealed config,
requires the nonblocking pipe to accept every byte, and verifies the same
identity in `before_agent_start`, every provider payload, and the trusted JSON
event stream. EPIPE, zero/short terminal writes, or a stalled pipe fail the Job;
positive short writes and transient EAGAIN/EINTR are retried.

The engine accepts only the pinned Pi `0.80.10` session/agent/turn/message/tool
lifecycle. It requires one fresh session header, the exact initial user
message, the pinned provider/model on all assistant messages, paired declared
tool calls and tool-result messages, a fresh assistant in each `agent_end`, and
one terminal `agent_settled` with no later events. Unknown, reordered,
compaction, stale-assistant, or malformed-usage events invalidate the run while
their raw evidence remains append-only.

Pi's context-aware `max_tokens` value is a hard input clamp. The extension sets
each provider request to the minimum of that existing clamp, the Job sampling
maximum, and the remaining cumulative Task output budget; it never raises the
Pi value. Streaming usage is checked against the active request cap, final
provider usage is committed exactly once per assistant response, and missing
or zero final usage is not accepted as zero-cost success.

## Run one fresh Job

Prepare prompt hashes before enqueueing:

```sh
python3 -m harness.v2.pi snapshot \
  --task-json TASK.json --worktree JOB_WORKTREE --output-dir STAGING_DIR
```

After Codex has enqueued, claimed, and moved the Job to `running`, use the
supervised production entrypoint:

```sh
harness/v2/deploy/run-job-supervised.sh \
  --job-id JOB_ID --lease-owner OWNER --lease-token TOKEN
```

Its inner invocation is equivalent to:

```sh
PYTHONPATH=ABSOLUTE_CLEAN_CONTROL_ROOT \
python3 -S -P -B -m harness.v2.pi run-job \
  --job-id JOB_ID --lease-owner OWNER --lease-token TOKEN \
  --state-dir ABSOLUTE_STATE --control-root ABSOLUTE_CLEAN_CONTROL_ROOT \
  --pi-install-manifest ABSOLUTE_SEALED_MANIFEST \
  --pi-dependency-graph ABSOLUTE_SEALED_NPM_GRAPH
```

The launcher and engine do not renew leases, transition acceptance, commit,
push, merge, delete a worktree, or manage the live vLLM/Ray service.

On a prepared Linux host, the opt-in sealed integration regression exercises
the real attested Node/Pi CLI, Bubblewrap profile, sealed extension/public
config/system prompt/settings, loopback OpenAI-compatible stream, exact six
tool payload, and authenticated `report_blocked` RPC without touching the live
model service:

```sh
HARNESS_PI_E2E_INSTALL_MANIFEST="$POINCARE_PI_INSTALL_MANIFEST" \
HARNESS_PI_E2E_DEPENDENCY_GRAPH="$POINCARE_PI_DEPENDENCY_GRAPH" \
HARNESS_PI_E2E_BWRAP="$HARNESS_PI_BWRAP" \
python3 -m unittest \
  harness.v2.pi.tests.test_actual_pi_sealed.ActualSealedPiIntegrationTest
```
