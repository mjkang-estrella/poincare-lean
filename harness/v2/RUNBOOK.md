# Harness v2 Core Runbook

This runtime is a Python 3 standard-library control plane. It manages Task/Job
state, SQLite transactions, expiring file-scope leases, trusted worktree
boundaries, independent Codex review, and append-only Job evidence. It does
not itself create worktrees, call a model, run Lean gates, merge commits, or
delete anything.

Run all commands from the repository root. A separate state directory can be
selected by putting `--state-dir PATH` before the command.

## Initialize

```sh
python3 -m harness.v2.runtime \
  --state-dir "$PWD/harness/v2/state" \
  --worktree-root /absolute/external/poincare-worktrees \
  --integration-root "$PWD" \
  init
```

`init` creates or migrates `harness/v2/state/harness.sqlite3` and is safe to
repeat after restarts or runtime upgrades. Both trusted roots must already
exist. They are persisted canonically and cannot later be changed for that
state database. The worktree root must be external to the integration checkout
and runtime state. An initialization without roots may enqueue evidence, but
claim and review fail closed until `init` is rerun with both trusted roots.
Runtime state is gitignored.

## Task lifecycle

Import records that conform to `schemas/task.schema.json`. Imports must start
in `proposed`; later states can only be reached through checked transitions.

```sh
python3 -m harness.v2.runtime task import path/to/task.json
python3 -m harness.v2.runtime task transition TASK_ID ready
python3 -m harness.v2.runtime task list
python3 -m harness.v2.runtime task show TASK_ID
```

The first enqueued Job atomically changes `ready` to `active`. Dependencies
must already be accepted. A blocked Task needs a blocked/rejected evidence Job
with a recorded exit reason:

```sh
python3 -m harness.v2.runtime task transition TASK_ID blocked \
  --reason 'Exact unresolved Lean shape and why it resists the allowed scope' \
  --evidence-job JOB_ID
```

## Job lifecycle and leases

Enqueue a record conforming to `schemas/job.schema.json`:

```sh
LEASE_SECONDS=18000
python3 -m harness.v2.runtime job enqueue path/to/job.json
python3 -m harness.v2.runtime job claim --job-id JOB_ID \
  --owner WORKER_INSTANCE --lease-seconds "$LEASE_SECONDS"
```

The Job artifact field must be
`harness/v2/state/jobs/<job-id>`, its branch must start with
`codex/<task-id>/`, and its Task revision/base commit must match exactly.
Its absolute workspace path must be exactly
`<trusted-worktree-root>/<job-id>`; a path elsewhere, through a symlink, or
inside the integration/control checkout is rejected.
Claim output contains a numeric `runtime.lease_token`. Keep that token with the
worker process; owner plus token fences stale processes after recovery.
Claims and `preparing -> running` are refused while the durable dispatch state
is `stopped`. `launch.sh` enables dispatch after preflight; `stop.sh` disables
it under the lifecycle lock before auditing or signalling any process. A fresh
database starts stopped. While stopped, an already-running or reviewing Job in
the current dispatch generation may heartbeat and complete its graceful drain,
but no preparing Job may start. A later stopped-to-running transition advances
the generation and fences any lease that did not drain.

A claim enters `preparing`. Advance and renew it explicitly:

```sh
python3 -m harness.v2.runtime job heartbeat JOB_ID \
  --owner WORKER_INSTANCE --lease-token LEASE_TOKEN \
  --lease-seconds "$LEASE_SECONDS" --state running

python3 -m harness.v2.runtime job heartbeat JOB_ID \
  --owner WORKER_INSTANCE --lease-token LEASE_TOKEN \
  --lease-seconds "$LEASE_SECONDS" --state reviewing
```

In automatic dispatch mode the trusted supervisor claims a 900-second lease
and renews it every 60 seconds while Pi is running. After Pi exits, a successful
result releases execution capacity and enters `reviewing`; Codex must continue
renewing the same owner/token during any long independent review. Explicit
recovery mode may instead use the commands above. Leanstral never receives
lease authority.

Overlapping repository path/glob scopes cannot be leased concurrently. Before
a supervisor record or Pi session exists, a queued or abandoned preparing Job
may be claimed with a new fencing token. Once a supervisor record exists, that
immutable Job is never relaunched: after proving its process group is no longer
live, Codex terminalizes it as interrupted and enqueues a fresh Job ID/attempt.
Expiry never removes the old worktree or artifacts, and scope reuse is refused
while the old Job supervisor still holds its execution lock. Likewise, a Task
cannot be superseded and a newer revision cannot be imported until every Job
for the affected revision is terminal.

Workers may stop only as `blocked` or `interrupted`:

```sh
python3 -m harness.v2.runtime job finish JOB_ID \
  --owner WORKER_INSTANCE --lease-token LEASE_TOKEN \
  --state blocked --exit-reason 'Exact unresolved Lean shape'
```

There is no worker-side transition to `passed` or `rejected`. The supervisor
must have exited before the heartbeat can enter `reviewing`;
that transition, terminalization, and review all acquire the same per-Job
execution fence nonblocking. While the Job has a live, complete fenced lease
in `reviewing`, Codex independently runs the frozen gate, writes `gate.json`
and its referenced output files beneath the Job artifact directory, and
records the review:

```sh
python3 -m harness.v2.runtime job review JOB_ID \
  --reviewer CODEX_REVIEWER_ID \
  --state passed --exit-reason 'Independent gate and review passed' \
  --gate-status passed --gate-result gate.json \
  --accepted-commit 40_HEX_COMMIT
```

The reviewer identity must differ from every current or historical worker
lease owner. Review fails if the lease expired, its generation changed, any
declared file scope was lost, the Job targets a stale Task revision, or any
evidence file was redirected through a symlink.

`gate.json` has this exact top-level shape:

```json
{
  "schema_version": "2.0",
  "status": "passed",
  "accepted_commit": "0123456789abcdef0123456789abcdef01234567",
  "accepted_tree": "89abcdef0123456789abcdef0123456789abcdef",
  "commands": [
    {
      "argv": ["git", "diff", "--check", "BASE", "--"],
      "status": "passed",
      "exit_code": 0
    }
  ],
  "declarations": [
    {
      "symbol": "Poincare.target",
      "source": "import Poincare\n#check Poincare.target\n#check (Poincare.target : FROZEN_LEAN_TYPE)\n",
      "source_sha256": "64_lowercase_hex",
      "argv": ["env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", "--stdin"],
      "status": "passed",
      "exit_code": 0,
      "stdout_path": "declaration-probes/0.stdout",
      "stdout_sha256": "64_lowercase_hex",
      "stderr_path": "declaration-probes/0.stderr",
      "stderr_sha256": "64_lowercase_hex"
    }
  ]
}
```

`commands` must reproduce every Task acceptance argv in exact order, with a
zero exit and `passed` outcome. `declarations` must reproduce every
`required_declarations` entry in exact order. The first required declaration
is the frozen target: its canonical stdin source includes both `#check symbol`
and `#check (symbol : objective.frozen_lean_type)`; later declarations use the
canonical import plus `#check symbol` because the Task contract does not carry
their types. `objective.frozen_lean_type` must be a Lean type expression, not
declaration or command syntax. The importer rejects declaration-shaped
prefixes; the executable stdin probe remains the authority for actual Lean
parsing. The runtime does not pretend to parse Lean semantics: it instead
binds the exact source bytes and fixed `lean --stdin` argv, and requires hashed
stdout/stderr files from the successful process. Those files and `gate.json`
are safely re-read and re-hashed during review and every acceptance retry.

The reviewed commit must exist, be the exact clean `HEAD` of the trusted Job
worktree, descend from the Task base commit, and belong to the same Git common
repository as the configured integration root. Its resolved `HEAD^{tree}` must
equal `accepted_tree`. Review and every acceptance retry recheck this Git
identity, so a random hash, unrelated repository at the expected path, moved
HEAD, dirty worktree, or mismatched tree fails closed.

A passed Job does not accept its Task. Acceptance is a separate orchestrator
action, and the Task commit must equal the commit embedded in the reviewed
Job evidence:

```sh
python3 -m harness.v2.runtime task transition TASK_ID accepted \
  --gate-job JOB_ID --accepted-commit 40_HEX_COMMIT
```

## Execute one Pi Job

Production dispatch goes through the process-group supervisor, not a direct Pi
binary:

```sh
harness/v2/deploy/run-job-supervised.sh \
  --job-id JOB_ID --lease-owner WORKER_INSTANCE --lease-token LEASE_TOKEN
```

The private deployment config supplies owner-only `0400` files named by
`POINCARE_PI_INSTALL_MANIFEST` and `POINCARE_PI_DEPENDENCY_GRAPH`. The
supervisor passes both to a fresh `harness.v2.pi run-job`; the engine fully
reattests the manifest-derived Node/CLI/install identity and launches Pi in its
worktree-free sandbox. A successful engine result remains worker evidence, not
a Harness transition.

## Safety and recovery

- Never put API keys, bearer tokens, passwords, or URL credentials in Task or
  Job JSON. The importer rejects common secret-bearing shapes, but callers are
  still responsible for redacting logs and externally written artifacts.
- `task.json`, `job.json`, `result.json`, database events, and artifact
  registrations are append-only. There is intentionally no delete command.
- Gate paths exposed in Job JSON stay artifact-relative. Absolute paths remain
  internal to the local control plane.
- SQLite and the artifact tree are restart state; tmux scrollback is not.
- Re-run `init` and inspect `job show` plus the supervisor record. Reclaim only
  a pre-launch queued/preparing Job. If launch was recorded, prove the process
  group is dead, terminalize that attempt, and create a fresh immutable Job.
  Do not manually reuse a stale token or relaunch the same Job.

Run the regression suite with:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning \
  -m unittest harness.v2.tests.test_runtime harness.v2.tests.test_cli
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning \
  -m unittest discover -s harness/v2/worker/tests -v
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning \
  -m unittest discover -s harness/v2/pi/tests -v
PYTHONDONTWRITEBYTECODE=1 python3 -W error::ResourceWarning \
  -m unittest discover -s harness/v2/deploy/tests -v
bash -n harness/v2/deploy/*.sh
git diff --check
```

The macOS suite deliberately skips the obsolete unsandboxed live-Pi fixtures
and the Linux parent-death test. Actual Pi validation is the manifest-bound
Linux preflight and bounded Job exercise; an arbitrary `.bin/pi` test path is
not production evidence.

The unit suites do not replace the Linux cache/sandbox gate. On `mj-zima`, the
Codex-owned `record-lean-cache-provenance.sh` must first serialize and seal the
exact root build, root Lean check, and selected Task gate. Its provenance binds
the exact Git, Lake, and Lean executable identities and the canonical
`lib/lean` compiler-library tree. Pass that immutable `provenance.json` to
`publish-lean-cache.sh --provenance`; then run
`verify-lean-cache.sh` and `cache-sandbox-smoke.sh`. The smoke elaborates a real
Poincare source file through the same networkless, sparse, read-only
Bubblewrap profile used by `lean_check`. Never publish while a build is still
mutating `.lake`.
