# mj-zima deployment and launcher

This directory is the narrow, restart-safe shell around Harness v2. It starts
Codex on `mj-zima`, dispatches every attempt through a fresh bounded Pi session,
treats the DGX Spark endpoint as inference-only, preserves
all durable evidence under ignored `harness/v2/state/`, and owns exactly three
tmux session names:

- `poincare-control`: the Codex orchestration cycle;
- `poincare-workers`: a bounded dispatcher and fresh leased Pi Job sessions;
- `poincare-observe`: an immediate and then 10,800-second durable evidence
  heartbeat. It is an evidence producer on `mj-zima`, not a claim that this Mac
  Codex thread stays alive. This thread reports the deployment result once and
  ends; it can inspect the durable evidence later on demand.

The SQLite store and append-only artifacts, not tmux scrollback, are recovery
state. Launcher scripts never remove worktrees, branches, artifacts, model
files, or logs. They never run Ray/GPU/model-server management commands. Fresh
SQLite state is stopped and only the lifecycle-locked launcher enables
dispatch after preflight.

## Configure once on mj-zima

After cloning the repository, installing its pinned Lean toolchain, and
installing Ubuntu's `bubblewrap`, GNU `flock`/`mv`, and `rsync` packages (the
sandbox must be `/usr/bin/bwrap`), and installing Node.js 22.19 or newer:

```sh
sudo apt-get update
sudo apt-get install --no-install-recommends bubblewrap coreutils rsync util-linux
install -d -m 0700 /srv/projects/poincare-worktrees \
  /srv/projects/poincare-cache-sources \
  /srv/data/poincare-harness/pi-attestation \
  /srv/data/poincare-harness/lean-cache
cd /srv/projects/poincare
cp harness/v2/deploy/env.example harness/v2/deploy/.env
chmod 600 harness/v2/deploy/.env
```

Edit `.env` with the live private endpoint, exact served model ID, exact
official artifact revision, Codex path, sealed Pi install-manifest and
dependency-graph paths, external Job worktree root, user-local tool paths, and
canonical absolute Git and tmux executables. `.env` is ignored in this
directory. Do not put API keys in it or commit it.

`POINCARE_MAX_LEANSTRAL_JOBS` is the hard execution ceiling (at most four).
`POINCARE_LEANSTRAL_BACKLOG_TARGET` is the desired combined count of queued,
preparing, and running Jobs and must not exceed that ceiling. The default is
four. Reviewing Jobs do not satisfy the target; status and heartbeat evidence
show any underfill. Codex may remain below target only when it records a
concrete lease, cache, dependency, resource, or task-shape reason.

Install Pi from the committed lockfile into a fresh dedicated directory. Make
the complete install tree read-only, then capture `npm ls --json --all` and use
`harness.v2.pi.install.build_install_manifest` with explicit `/usr/bin/node`,
the exact `/usr/bin/node --version` result, the install root, the resolved
`dist/cli.js`, and those graph bytes. Pi 0.80.10 requires Node 22.19.0 or newer.
Seal the canonical manifest and graph as separate owner-only `0400` files
outside the install tree at the two paths configured in `.env`. Preflight
reattests and re-probes the exact Node path with a scrubbed environment,
the resolved CLI, lock/package metadata, dependency graph, and every install
tree entry; it rejects version drift or an incompatible runtime without a
`PATH` lookup. `.bin/pi` and version output alone are never authorization:

```sh
set -euo pipefail
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
umask 077
npm ci --ignore-scripts --engine-strict --no-audit --no-fund
chmod -R a-w -- "$PI_ROOT"
```

See `harness/v2/pi/README.md` for the complete owner-only write-once graph and
manifest-generation command; do not precreate either temporary output.

Create the external cache root named in `.env`. Before any Job uses a base
commit, run the provenance recorder against a read-only absolute Task record.
It serializes and preserves the exact root build, root Lean check, and one
selected Task Lean/build gate, then returns a sealed `provenance.json`. The
record binds the exact Git, Lake, and Lean executable identities plus the
canonical `lib/lean` compiler-library tree digest; publisher and verifier
independently rehash that closure. Only that evidence may authorize one cache
publication:

```sh
TASK_BASE=7ce913d87be973256517ea862fb4d3dbfae7cb82
TASK_BASE_SOURCE=/srv/projects/poincare-cache-sources/$TASK_BASE
TASK_RECORD=/srv/data/poincare-harness/import/automatic-scalar-derivative-constructor-r1.json
CONTROL_DEPLOY=/srv/data/poincare-harness/control/harness/v2/deploy
test ! -e "$TASK_BASE_SOURCE" && test ! -L "$TASK_BASE_SOURCE"
/usr/bin/git -C /srv/projects/poincare worktree add --detach \
  "$TASK_BASE_SOURCE" "$TASK_BASE"
cd "$TASK_BASE_SOURCE"
"$CONTROL_DEPLOY/record-lean-cache-provenance.sh" \
  --task "$TASK_RECORD" --command-index 1 \
  --source-root "$TASK_BASE_SOURCE" /absolute/private/deploy.env
"$CONTROL_DEPLOY/publish-lean-cache.sh" \
  --source-root "$TASK_BASE_SOURCE" --provenance /absolute/sealed/provenance.json \
  /absolute/private/deploy.env
"$CONTROL_DEPLOY/verify-lean-cache.sh" \
  --source-root "$TASK_BASE_SOURCE" /absolute/private/deploy.env
"$CONTROL_DEPLOY/cache-sandbox-smoke.sh" \
  --source-root "$TASK_BASE_SOURCE" /absolute/private/deploy.env
```

The paths above make the first old-base Job explicit: the cache-source
worktree must be clean at Task base
`7ce913d87be973256517ea862fb4d3dbfae7cb82` and must remain external to the
configured `POINCARE_WORKTREE_ROOT`. The actual `a01` Job worktree remains
under that configured Job root. The selected automatic-module cache gate is
zero-based command index `1`: its explicit `lake build` guarantees the
unrooted `NormalizedFlowHausdorffScalarTimeDerivativeAutomatic.olean` needed
after Pi changes the target import. Command index `2` only checks the old
target at the Task base and is not sufficient cache provenance. Use the
absolute provenance path printed by the recorder. Do not let a later Harness control commit silently retarget
verification to its newer integration HEAD.

For initial provisioning, the publisher itself may run from a separate clean,
committed control-code worktree while `--source-root` remains at the older Task
base. It imports the cache contract from the script's own Git checkout, verifies
that the source is a worktree of the configured repository, and never requires
the source base to contain the new Harness files. It strips dependency Git
metadata, dereferences only safe internal file symlinks, writes canonical local
Lake package overrides, binds the snapshot to the exact commit/tree and project
manifests, removes every write bit, and atomically installs
`lean-cache/<40-hex-base>`. Existing snapshots and failed staging directories
are never removed or overwritten.

The control commit and the old Task base are different cache keys. Before
preflight, fast-forward the configured integration checkout to the clean
control HEAD and publish its cache separately. Create a schema-valid,
owner-only provenance Task whose `base_commit` is that exact HEAD and whose
selected acceptance command is
`["env","LEAN_NUM_THREADS=1","lake","env","lean","Poincare/Statement.lean"]`.
This Task is only cache-build provenance and is not imported as proof work:

```sh
CONTROL_ROOT=/srv/data/poincare-harness/control
INTEGRATION_ROOT=/srv/projects/poincare
CONTROL_DEPLOY="$CONTROL_ROOT/harness/v2/deploy"
CONTROL_HEAD=$(/usr/bin/git -C "$CONTROL_ROOT" rev-parse HEAD)
CONTROL_TASK=/srv/data/poincare-harness/import/cache-provenance-$CONTROL_HEAD.json
/usr/bin/git -C "$INTEGRATION_ROOT" merge --ff-only "$CONTROL_HEAD"
test "$(/usr/bin/git -C "$INTEGRATION_ROOT" rev-parse HEAD)" = "$CONTROL_HEAD"
"$CONTROL_DEPLOY/record-lean-cache-provenance.sh" \
  --task "$CONTROL_TASK" --command-index 0 \
  --source-root "$INTEGRATION_ROOT" /absolute/private/deploy.env
"$CONTROL_DEPLOY/publish-lean-cache.sh" \
  --source-root "$INTEGRATION_ROOT" --provenance /absolute/sealed/control-provenance.json \
  /absolute/private/deploy.env
"$CONTROL_DEPLOY/verify-lean-cache.sh" \
  --source-root "$INTEGRATION_ROOT" /absolute/private/deploy.env
"$CONTROL_DEPLOY/cache-sandbox-smoke.sh" \
  --source-root "$INTEGRATION_ROOT" /absolute/private/deploy.env
```

Use the exact provenance path printed by the second recorder invocation. Both
`lean-cache/$TASK_BASE` and `lean-cache/$CONTROL_HEAD` must exist and verify:
the Pi Job selects the former, while preflight selects the latter.

Run preflight explicitly before the first launch:

```sh
/srv/data/poincare-harness/control/harness/v2/deploy/preflight.sh \
  /absolute/private/deploy.env
```

Preflight fails closed unless it can verify the integration checkout and
branch, Codex authentication, the complete sealed Pi 0.80.10 install identity,
the configured Git and tmux executable identities without a `PATH` lookup,
`/usr/bin/bwrap` user/PID/mount/network isolation,
the pinned Lean compiler,
free disk, user-owned worktree root, initialized runtime store, required
runtime, worker-health, and Pi entrypoints, absence of foreign collisions on
the three tmux names, a verified current per-base cache, a real
`Poincare/Statement.lean` elaboration through Pi's exact Bubblewrap/cache
profile, `/models`,
and one bounded chat completion. It prints neither the endpoint nor a model
response.

The production proof-attempt entrypoint is
`harness/v2/deploy/run-job-supervised.sh`. It binds one active fenced Job to a
recorded Linux process group and invokes `python3 -m harness.v2.pi run-job`
with the sealed manifest and dependency graph. The inner CLI is useful for
focused tests, but does not replace the supervisor boundary.

## Launch, inspect, and stop

```sh
harness/v2/deploy/launch.sh
harness/v2/deploy/status.sh
/usr/bin/tmux attach -t poincare-control
/usr/bin/tmux attach -t poincare-observe
```

`launch.sh` is idempotent. It preserves a running session only when the
session's private tmux option matches this repository's Harness owner marker.
It refuses a same-named foreign session.

The control loop snapshots every prompt, Codex JSONL stream, stderr, final
message, exact completion probe, and (when applicable) full completion audit.
Codex runs with host authority because it is the trusted orchestrator that
must attest root-owned executables, allocate worktrees, supervise Jobs, review,
and commit. That authority is not inherited by Pi or Leanstral: every model Job
still has disabled built-ins and only the exact six scoped tools.
It hashes the committed Harness trust boundary before and after each cycle and
pauses if Codex or another process changes it; control-plane repairs require a
separate review and relaunch.
At each cycle the prompt includes a measured execution-backlog snapshot. Codex
prefills a safe disjoint same-base batch before optional repository-wide audits,
reviews through one serial merge queue, and runs broad integration gates once
per compatible batch rather than once per small accepted diff.
After any Codex exit it waits the configured cooldown and starts a fresh cycle
from git, SQLite, and artifacts only when Codex's schema-validated cycle result
says resumption is safe. A nonzero Codex process exit is preserved and retried
indefinitely with capped exponential backoff; the third consecutive failure
adds an operator-alert event while the heartbeat remains alive. A successful
cycle with a missing/invalid resume decision pauses as unsafe state. It exits
successfully only when a clean, stable integration checkout contains the exact
canonical theorem, its axiom footprint is allowed, and
`scripts/completion_audit.sh` also passes. Codex creates worktrees and owns
independent review, gates,
acceptance, integration, and commits. It must dispatch actual proof attempts
through the repository Pi executor: fresh process per Job, complete JSON/RPC
evidence, no unrestricted built-ins, and only the six scoped tools named in the
orchestrator prompt. Model-requested `lean_check` processes additionally run in
a deny-by-default Bubblewrap sandbox; Codex's later independent review gates
remain outside the worker capability.

Independent Job review uses `review-job-focused.sh`. It refuses broad
`lake build` commands and mutable worktree caches, reuses the verified
commit-keyed cache read-only, and creates only an ephemeral olean projection
for the frozen module checks and canonical declaration probes. Passed Jobs are
held for a compatible batch of up to `POINCARE_INTEGRATION_BATCH_SIZE` (default
four); Codex then runs one root integration checkpoint for the batch. This
keeps full builds as milestone evidence without paying their cost per Job.

The worker plane dispatches only immutable Jobs already prepared and queued by
Codex; it does not invent Tasks, allocate worktrees, review, accept, or commit.
SQLite serializes the durable dispatch switch with every claim and separately
rejects overlapping file-scope leases. Each real supervisor acquires one of exactly
`POINCARE_MAX_LEANSTRAL_JOBS` locked capacity slots and the Job-wide execution
lock before its final admission. Both locks remain held until Pi exits, then
are released before the successful Job enters Codex-owned `reviewing`.
Stop disables durable dispatch first, signals and reaps authenticated process
groups next, and only then terminalizes Jobs and releases scopes. Running and
reviewing Jobs in the current dispatch generation may drain gracefully while
stopped; preparing Jobs cannot start, and the next launch generation fences
anything left behind. Queued Jobs remain durable but consume no execution
capacity.

Every immutable Job has at most one recorded supervisor and one Pi session.
Before any supervisor record exists, a queued/preparing attempt may be
reclaimed. Once launch is recorded, a crash or expired lease is terminalized
as interrupted only after the recorded process group is proven dead; Codex then
creates a fresh Job ID/attempt. Recovery never relaunches the same Job.

The result route is explicit: a successful sealed `pi-run-result.json` enters
`reviewing`; an authenticated `report_blocked` terminalizes the Job as blocked;
every other unsuccessful run becomes interrupted and requires Codex to create
a new immutable attempt. The worker plane renews running leases every minute.
Reviewing leases remain Codex's responsibility while independent gates run.

The observe loop records a JSON heartbeat immediately and every 10,800 seconds
(three hours). Each line includes HEAD, branch, dirty-path and worktree counts,
the exact declaration/axiom probe result, model API health, and ownership state
of the three sessions. This is durable `mj-zima` evidence only. This Mac Codex
thread reports the final deployment outcome once and then ends; it does not run
a three-hour loop. In a later user turn, it can inspect and report the retained
host evidence on demand. Evidence lives at:

```text
harness/v2/state/deploy/
  events.jsonl
  control/events.jsonl
  control/cycles/<cycle-id>/
  observe/heartbeats.jsonl
  observe/snapshots/<heartbeat-id>/
  workers/events.jsonl
```

To request a graceful drain while preserving all state:

```sh
harness/v2/deploy/stop.sh
```

The stop command first validates stable tmux IDs, configuration fingerprints,
roles, and base panes. By default it writes a durable stop request and kills no
process: control stops between cycles, the worker plane waits for SQLite to
report no active Jobs, and observe exits last. If an operator has inspected
the current Jobs and explicitly accepts interruption, use:

```sh
harness/v2/deploy/stop.sh --interrupt-owned-jobs
```

This override still cannot touch a session without the exact stable identity.
An existing supervisor exit record never suppresses authenticated recovery of
live members in its recorded process group.
Restart with `launch.sh`; do not delete stale artifacts or worktrees as a form
of recovery.

## Operational evidence and failures

- `status.sh` is read-only and shows the newest durable control event and
  heartbeat in addition to tmux state.
- A missing or unhealthy Leanstral endpoint blocks a new launch. A later model
  outage is recorded by the heartbeat and handled as a Job stop condition; the
  harness never restarts the service.
- A dirty integration checkout is reported and preserved. The prompt requires
  Codex to understand it before editing.
- A Task blocked after repeated equivalent attempts must retain the exact Lean
  type and evidence. The outer proof objective continues by selecting or
  proposing a soundly narrower dependency, never by weakening the theorem.
- Significant independently gated progress may be committed locally by Codex.
  The launcher and prompt do not push.

## Validate launcher changes

From the repository root:

```sh
bash -n harness/v2/deploy/*.sh
git diff --check -- harness/v2/deploy harness/v2/prompts
```

For a live validation, put real values only in ignored `.env`, run
`preflight.sh`, launch, inspect `status.sh`, and stop the owned sessions. Never
substitute a production model endpoint in a committed fixture.
