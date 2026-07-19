# Proof Harness

This directory contains two different things:

1. A first-generation harness and its historical evidence.
2. The specification for the next Codex GPT + Leanstral harness.

## Legacy v1

The existing surfaces are:

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

## Harness v2

The v2 design separates:

- **Task**: the stable theorem objective, scope, context, acceptance contract,
  and stop conditions.
- **Job**: one attempt by one backend/model in one isolated worktree.

One Task may have several Leanstral attempts, a GPT repair attempt, and a final
GPT review Job. A Task becomes accepted only when the orchestrator reruns its
gate and records the accepted commit.

See [v2/SPEC.md](v2/SPEC.md), the schemas in `v2/schemas/`, and the illustrative
records in `v2/examples/`.

## Compatibility Policy

Do not rewrite the legacy ledger in place. The first v2 implementation should:

1. read old tasks/reports as optional context;
2. create new v2 records in a separate state directory;
3. import only selected legacy tasks after revalidating them against current
   HEAD;
4. preserve all raw job artifacts append-only.
