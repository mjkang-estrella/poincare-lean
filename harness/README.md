# Proof Harness

This directory contains two generations of proof orchestration:

1. A first-generation harness and its historical evidence.
2. The executable Harness v2 control plane for bounded Pi/Leanstral Jobs.

## Legacy v1

At the 2026-07-19 handoff, the existing surfaces are:

- `tasks/`: 409 Markdown task prompts.
- `reports/`: 365 worker outcome reports.
- `ledger.json`: task history through 2026-07-07.
- `worker_contract.md`: useful worker honesty rules.
- `dispatch.sh`: a Mac-specific Codex dispatcher with hard-coded paths and
  model settings.
- `gate.sh`: a focused build and axiom gate.
- `logs/`: ignored runtime logs.

This history is valuable. It should not be deleted or treated as current
queue state. In particular, v1 conflates a durable task with one worker run,
allows prose to carry important state, and assumes a specific local machine,
Codex model, worktree path, and prebuilt cache.

## Executable Harness v2

Harness v2 separates:

- **Task**: the stable theorem objective, scope, context, acceptance contract,
  and stop conditions.
- **Job**: one attempt by one backend/model in one isolated worktree.

The primary execution path is:

```text
Codex GPT
  -> Harness v2 Task/Job control plane
  -> one fresh bounded Pi 0.80.10 JSON Job session
  -> Leanstral
```

`v2/runtime/` implements validated Task/Job lifecycle transitions, SQLite
state, fenced file-scope leases, and append-only artifact registration.
`v2/pi/` runs one fresh Pi session for one Job and captures its message and tool
event stream. `v2/deploy/` provides the restart-safe `mj-zima` launcher and
exact 10,800-second evidence heartbeat. This Mac setup thread reports the
verified deployment once and ends; later operators can inspect the durable
host evidence from the Mac on demand. Isolated Job worktrees and independent
Lean gates remain Codex responsibilities.

Pi's unrestricted built-ins are disabled. The complete Leanstral-facing tool
surface is exactly:

- `read_context`
- `search_symbol`
- `apply_patch_scoped`
- `lean_check`
- `git_diff`
- `report_blocked`

There is no worker shell, SSH, unrestricted filesystem access, Git
commit/push/merge, branch or worktree deletion, Docker, Ray, tmux, or
model-service management. Codex alone selects the frontier, allocates
worktrees, reviews diffs, reruns gates, accepts Tasks, and commits meaningful
verified progress. The `lean_check` broker fails closed unless Linux
Bubblewrap can expose only a read-only Job source tree, a read-only immutable
Lake cache keyed by the Task base commit, with validated publisher provenance,
and the pinned Lean toolchain without network access or repository Git
metadata.

One Task may have several fresh Pi/Leanstral Jobs. A passed Job never accepts
its Task automatically; acceptance requires an independently rerun gate and a
Codex-recorded commit.

`v2/worker/` is deliberately not another agent loop. It retains endpoint
health checks, deterministic prompt/context snapshots, and an explicit
one-shot fallback for diagnostics or recovery only.

See [v2/SPEC.md](v2/SPEC.md), [v2/RUNBOOK.md](v2/RUNBOOK.md), the schemas in
`v2/schemas/`, and the illustrative records in `v2/examples/`.

## Compatibility Policy

Do not rewrite the legacy ledger in place. Harness v2:

1. read old tasks/reports as optional context;
2. create new v2 records in a separate state directory;
3. import only selected legacy tasks after revalidating them against current
   HEAD;
4. preserve all raw job artifacts append-only.

The exact project terminal condition remains a clean, stable integration HEAD
where Lean checks
`Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement` with the
allowed axiom footprint and the full completion audit passing. The persistent
host evidence heartbeat observes that condition; a Mac operator may inspect
it on demand, but this setup thread is not part of the long-term terminal.
