# Leanstral health and one-shot fallback

Pi is the primary Harness v2 Job execution engine. This directory is a smaller,
explicit fallback and diagnostic boundary between the Codex GPT orchestrator
and an already-running OpenAI-compatible Leanstral service. It can verify one
exact served model, snapshot one immutable Task plus its explicitly named
context files, and request one proposed proof response. It is not an agent
loop, dispatcher, or replacement for Pi.

It deliberately cannot edit or apply a patch, run Lean, create or remove a
worktree, expose Git operations, merge or commit, change Task state, or manage
vLLM, Ray, GPUs, tmux, or other processes. Its only Git subprocesses are fixed,
read-only identity, tracked-file, and dirty-status checks performed before a
prompt is built. The Codex orchestrator owns all mutation decisions and
independently reviews the raw response before any worktree change.

## Configuration

Copy the names from `.env.example` into the private service environment. Do
not commit the filled values. `LEANSTRAL_BASE_URL` and `LEANSTRAL_MODEL` are
required and intentionally have no CLI flags. Bound `snapshot` and `run` also
require `LEANSTRAL_MODEL_REVISION`; it must exactly match the immutable Job
backend revision. The endpoint's `/v1/models` response must contain exactly
the configured single model ID. That endpoint does not attest a weight
revision, so revision identity is a fail-closed Job-to-environment pin rather
than a claim of remote cryptographic attestation.

`LEANSTRAL_API_KEY` is optional. Authorization is sent to the endpoint but is
always represented as `<redacted>` in artifact metadata. URLs containing
credentials, queries, or fragments are rejected. The client ignores ambient
HTTP proxy variables and connects directly to the configured private endpoint.
HTTP redirects are disabled, response bodies are bounded, and health plus the
single completion share one wall-clock deadline, so Authorization cannot be
forwarded to a redirect target and a slow health probe cannot grant the
completion a second full timeout.

## Commands

Run from the repository root:

```sh
python3 -m harness.v2.worker health

python3 -m harness.v2.worker snapshot \
  --job-id automatic-scalar-derivative-a01 \
  --state-dir /absolute/path/to/harness/v2/state \
  --lease-owner codex-orchestrator \
  --lease-token 1

python3 -m harness.v2.worker run \
  --job-id automatic-scalar-derivative-a01 \
  --state-dir /absolute/path/to/harness/v2/state \
  --lease-owner codex-orchestrator \
  --lease-token 1 \
  --timeout-seconds 600
```

Use `run` only when the orchestrator has explicitly selected the fallback for
one bounded attempt. The command exits after one response and never continues
or dispatches another Job. It accepts no Task, repository, worktree, artifact,
endpoint, model, or sampling override. Those values come from the live Harness
state and the pinned environment.

Before writing or calling the model, the fallback requires the current runtime
schema, the latest active Task, a running Job, the exact active owner/fencing
token and complete file-scope lease set, registered immutable Task/Job
snapshots, the trusted canonical worktree and artifact directory, the exact
branch/HEAD/base commit, a clean context/edit scope, and recomputed prompt and
context hashes equal to the Job. It rechecks those facts at later evidence
boundaries. The Job sampling object is authoritative. The effective timeout is
bounded by the command timeout, Task wall-clock budget, and live lease expiry;
one deadline starts on entry and covers binding, snapshotting, HTTP, and final
evidence. The Task's `disk_mb` budget covers all existing and newly appended
files in the Job artifact directory, with budget recount plus write serialized
by a per-Job file lock.

## Evidence

Each artifact directory is append-only:

```text
task.json                 canonical Task snapshot
context-manifest.json     sorted file paths, sizes, hashes, aggregate hash
prompt.md                 exact deterministic prompt
fallback-session.json     write-once Job/backend/prompt/context binding
events.jsonl              redacted request/response metadata
requests/*.json           exact completion request
responses/*.json          raw health and completion responses, including errors
assistant/*.md            extracted assistant text for orchestrator review
fallback-evidence.json    final file hashes for a completed/HTTP-error attempt
```

Snapshot files and raw messages use exclusive creation and refuse overwrite.
`fallback-session.json` also makes a fallback attempt one-shot. Its SHA-256 is
injected into every later event, each event records the hash of the evidence it
describes, and the final manifest hashes the complete event log plus the
material files back to the exact Job, Task revision, prompt, context, and
session. Harness SQLite already
registers the immutable `task.json` and `job.json`; the runtime currently has
no generic non-lifecycle registration method for worker evidence, so this
explicit hash chain is the fallback's integrity boundary. Codex still reviews
the files independently and the fallback never changes Job or Task lifecycle
state.

The runtime Task snapshot must be byte-for-byte canonical and the queued Job
snapshot must retain its registered path and hash. Any disagreement or later
tampering fails closed. Secret-shaped context or responses are never persisted
as raw content: only a generic class, byte count, and SHA-256 are appended to
the bound event log.

Only files explicitly listed by `Task.context.files` are read. Absolute paths,
`..` traversal, duplicate paths, non-files, non-UTF-8 files, and any symbolic
link in a context path are rejected. Files are opened without following links,
with stable inode/size checks. Each context file is capped at 2 MiB and the
aggregate at 8 MiB. Before reading them, the fallback verifies that the
repository root and Git HEAD equal the frozen Task base, each context file is
tracked, and neither context nor the allowed edit scope is dirty. Provider
tokens, private keys, AWS keys, password/API assignments, credential-bearing
URLs, and the exact configured API key are rejected before prompt, raw
response, or assistant artifacts are written; matching text is never echoed in
an error.

`harness.v2.worker.snapshot.build_prompt_snapshot` remains only as an unbound
offline diagnostic/test helper. It can build an explicit-path snapshot but is
not exported from the package root, is not reachable from the CLI inference
path, and must never be treated as authorization to execute a Harness Job.

## Tests

```sh
python3 -m unittest discover -s harness/v2/worker/tests -v
```

The tests use a local standard-library HTTP server. They require no model,
network access, or third-party Python package.
