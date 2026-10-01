# SmoothInitialMetricLocalPullback 4.33 worker report

Commit: `9e468974dc2ff85db10aaef0ef9ce5d032ee1358`
Base: `757d0dda020470783afef7b0edfe1601da00274c`
Branch: `codex/metric-pullback-433-a01`
Changed file: `Poincare/Global/SmoothInitialMetricLocalPullback.lean` only. One insertion/one deletion. Working tree clean.

## Outcome and exact proof boundary

The only edit adds the existing proof-local `e` to the simp unfolding list for `hxHom`:

```lean
have hxHom : x ∈ eHom.baseSet := by simpa [eHom, eR, e] using hx
```

This unfolds the already-bound actual tangent trivialization, aligning its baseSet with the existing chart-domain membership produced by simplification. The original hx is used; no extra chart-source/domain premise, global invertibility assumption, condition or package is introduced. Both subsequent pullback slots and inverse identities remain exactly as before. No using!, convert!, elaborator option or trust/kernel setting was needed.

The whole-source guard confirms every byte outside localEuclideanInner_coordinates's proof body is unchanged: all four public headers/types/universes, imports, original domain hypotheses, smooth ENat.top regularity, section declarations and the other three proof bodies. Actual SmoothInitialMetricDefinitions.localEuclideanInner remains unchanged in its owning pinned file, including genuine tangent trivialization, continuousLinearMapAt, canonical Euclidean inner product and both pullback slots. Pinned RiemannianContext, toolchain and manifest hashes remain unchanged.

## Exact worker gates

- `env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/SmoothInitialMetricLocalPullback.lean`: exit0,18.707847s, attempt-01-lean.
- `env LEAN_NUM_THREADS=1 lake build Poincare.Global.SmoothInitialMetricLocalPullback`: exit0,17.221434s, explicit scoped module target.
- `env LEAN_NUM_THREADS=1 lake env lean harness/v2/state/upstream-verification-20260930/metric-pullback-433-task-a01/FrozenMigrationProbe-a02.lean`: exit0,8.965207s. All four FROZEN_CONTRACT_OK and four AXIOM_CONTRACT_OK markers independently checked against the frozen Task declaration list. Exact literal types, rigid universe arities and full transitive unsafe/partial/allowed-axiom closure checks pass. Smooth order remains ENat.top coerced into WithTop ENat.
- Exact `python3 .../check-scope.py`: exit0 with PRESERVED_METRIC_PULLBACK_ALL_OTHER_DATA_TYPES_PROOFS.
- Exact scoped forbidden-token scan: exit1, no matches.
- `git diff --check`: exit0.

All gate receipts and committed source bind SHA256 `21223dc69e7349430677ef4bbaebc8b6d8bc18f0e957f382bbc7338c8330e251`. The old recorded compiler failure, immutable Task/context hashes, original/final source, exact cwd/argv/environment overrides, timings/exits/transcripts and final diff are preserved append-only. One proof attempt sufficed. Source compile had no diagnostics; scoped build replayed unchanged dependency warnings. Pinned context hashes were checked before editing and again after all gates.

## Scope and next action

The original actual smooth initial-metric constructor and bundle consumers can reuse this same coordinate lemma. This supports retained-root compatibility/final verified-PC integration. Core S remains discharged; no original Hamilton input or convergence construction is supplied here. No full build, helper agent, service operation, outside-scope edit, merge or Task acceptance occurred.

Root's exact first action: independently rerun the frozen Task acceptance commands against this scoped commit, then choose serial integration. Full retained-root and exact final completion gates remain the orchestrator's responsibility.
