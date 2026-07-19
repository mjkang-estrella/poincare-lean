# Agent Operating Contract

This repository is an unfinished Lean formalization of the Poincare
conjecture. Your job is to make honest theorem-bearing progress while keeping
the difference between a coherent scaffold and a complete proof explicit.

## Required First Read

Before editing, read:

1. `README.md`
2. `HANDOFF.md`
3. `docs/PROJECT_MAP.md`
4. the task file and every context file named by that task
5. the nearest existing Lean definitions and their actual imports

Check `git status --short --branch`, `git worktree list --porcelain`, and the
current commit before deciding that a prose ledger is current.

## Source of Truth

Lean is the authority. Generated status, harness ledgers, reports, and comments
can be stale. Never infer that `Poincare.poincare_conjecture` exists from a
green root import or a conditional theorem with a similar name. Probe the exact
declaration when completion matters.

## Scope of a Good Task

A task should name:

- one theorem-shaped objective or one precisely stated blocking shape;
- a base commit;
- allowed and forbidden files;
- the definitions and earlier reports that provide context;
- exact acceptance commands;
- valid stop conditions.

If the objective is too large for one reviewable diff, split it at a real
mathematical interface. Do not split it into alias-only or ledger-only churn.

## Editing Rules

- Use a `codex/<task-name>` branch in an isolated worktree for delegated proof
  work.
- Do not edit `main` from a worker job.
- Do not add `sorry`, `admit`, axioms, postulates, `native_decide`, or vacuous
  wrappers.
- Do not weaken, replace, or silently reinterpret a frozen target.
- Use the task's allowed file scope. Minimal import wiring may be added only
  when it is required to expose verified work.
- Prefer small named lemmas that close a real dependency over monolithic proof
  search.
- A blocked report is a valid result when it records the exact resisting Lean
  type, attempted routes, and the strongest verified partial result.

## Verification

Every worker attempt must at least run:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Path/ChangedFile.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Path/ChangedFile.lean
git diff --check
```

The orchestrator, not the worker, decides acceptance. It independently reruns
the task gate from the recorded base commit and checks the actual diff. Root
integration normally adds:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare.lean
sh scripts/interface_audit.sh
sh scripts/semantic_surface_audit.sh
sh scripts/theorem_contract_audit.sh
sh scripts/root_import_audit.sh
sh scripts/axiom_audit.sh
```

Use `lake build` and the completion/status scripts at explicit integration
checkpoints. Do not launch overlapping full builds from multiple jobs.

## Harness v2

The current `harness/tasks`, `harness/reports`, and `harness/ledger.json` are a
legacy record. New orchestration must follow `harness/v2/SPEC.md`:

- a **Task** is the durable objective and acceptance contract;
- a **Job** is one attempt by one worker against that task;
- workers never merge or mark tasks accepted;
- all job artifacts are append-only;
- the GPT orchestrator owns decomposition, review, merge order, and status;
- Leanstral is a bounded proof worker, not the project coordinator.

## Resource and Safety Boundaries

- Do not stop, restart, or take ownership of a model server, Ray cluster, GPU
  process, or tmux session unless the user has placed it in scope.
- Do not remove a dirty worktree or branch without proving its changes are
  merged, backed up, or intentionally discarded.
- Do not expose secrets in task files, prompts, logs, or committed config.
- Use leases so two jobs cannot edit the same file family concurrently.
- Preserve failed compiler output and the final diff as job evidence.

When handing off, update `HANDOFF.md` with dated facts, not predictions, and
leave the next agent one exact first action.
