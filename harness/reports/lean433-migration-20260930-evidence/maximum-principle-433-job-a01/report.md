# MaximumPrinciple 4.33 migration worker report

Commit: `492b3c025d8df1f5d417e9f870b099f909a46072`
Base: `18e6d0225ba98f9aa4cf706f41e0daaf9ef4c46f`
Branch: `codex/maximum-principle-433-a01`
Allowed and changed file: `Poincare/MaximumPrinciple.lean` only. Working tree clean.

## Outcome

The existing maximum-principle module compiles on pinned Lean 4.33.1. The repair uses Mathlib `convert!` at derivative transports to unfold definitionally equal real group/module instances, explicitly expands function composition at the local-minimum transport, and removes an empty simp step. No transparency option remains. Imports, theorem signatures, hypotheses and universe arities are unchanged. No new declaration, assumption, unsafe/partial proof dependency or nonstandard foundational axiom was introduced.

## Exact worker gates

1. `env LEAN_NUM_THREADS=1 lake env lean Poincare/MaximumPrinciple.lean`: exit0, attempt-03-lean,12.271210s.
2. `env LEAN_NUM_THREADS=1 lake build Poincare.MaximumPrinciple`: exit0, gate-02-scoped-build,9.245668s. This was a scoped module build, not a full retained-root build.
3. `env LEAN_NUM_THREADS=1 lake env lean harness/v2/state/upstream-verification-20260930/maximum-principle-433-task-a01/FrozenMaximumPrincipleProbe-a02.lean`: exit0, gate-03-frozen-probe,15.827645s. All22 FROZEN_CONTRACT_OK and22 AXIOM_CONTRACT_OK markers were validated against the frozen Task declaration list. Exact types, universe arities, full unsafe/partial dependency checks and allowed axiom closures passed.
4. Scoped forbidden-token `rg` command: exit1, no matches.
5. `git diff --check`: exit0.

All gate receipts bind the same final source SHA256 `aff7a9b72bf51e625012ebaade5f2f6ccfcbca1e0d4fe47ee6169612867a9df3`. The committed source has that identical hash. A separate literal source-header comparison also confirms all22 old theorem headers unchanged, but the fresh frozen Lean probe is the API authority. The retained `ha` hypothesis is intentionally unchanged despite an unused-variable warning; other remaining warnings concern existing push_neg deprecation and an existing unused simp argument.

## Append-only attempt history

Attempt01 failed after removing the empty simp and trying the allowed backward transparency option. Attempt02 compiled after conversion/composition repairs. Attempt03 removed the unnecessary global option and redundant simp tails and compiled successfully. Every attempt preserves its source before/after, diff, exact cwd/argv, exit, timestamps and compiler transcript. No previous artifact was overwritten.

The host-clock/dispatch gap between attempt02 and attempt03 exceeded the original40-minute wall budget despite31.302s total recorded compiler time. Root explicitly renewed the gate/commit budget for15minutes; `budget-extension-a01.json` preserves that authorization and the original Task evidence unchanged.

## Mathematical boundary and next action

This enables retaining the historical full root during the version migration for the credited unconditional upstream endpoint adapter. It constructs no independent Hamilton convergence, Ricci-flow existence, smoothing or surgery input. Full root/completion audits remain the orchestrator's responsibility. No merge or Task acceptance was performed.

Exact first action for root: independently rerun the frozen Task acceptance commands against this scoped commit, then choose serial integration into the retained-root migration.
