# Handoff Snapshot

Snapshot date: 2026-07-17 (America/Los_Angeles)

## Project State

- Repository: `/Users/mjkang/Develop/poincare`
- Branch at inspection: `main`
- Inspected HEAD: `d8f2e43c23680f9a9310bde5c3a3d2088f9728dc`
- Remote relation at inspection: `main...origin/main`, no divergence shown
- Lean files: 835
- Root imports in `Poincare.lean`: 828
- Reserved endpoint probe: failed with `Unknown identifier
  Poincare.poincare_conjecture`
- Conclusion: the repository is coherent enough to import a very large proof
  graph, but the Poincare conjecture is not yet completed in Lean.

The working tree was clean before this documentation/harness-refinement change.

## Status Caveats

- `CURRENT_STATUS.md` was generated on 2026-06-30. It is not a current snapshot
  of the 2026-07-17 HEAD.
- `harness/ledger.json` ends with the 2026-07-07 `M5-glob-67` selector-assembly
  boundary. It predates the large 2026-07-17 commit and is historical.
- Commit `d8f2e43c` imports a broad set of later analytic, Cartan,
  compact-history, smoothing, normalized-flow, and end-to-end modules. Its
  one-line commit message does not explain that scope.
- Do not resume by blindly redispatching the last legacy ledger task.

## Proof Continuation

The late imported proof surface includes the positive-time ODE-overlap and
compact-history chain, notably:

- `Poincare/Global/CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction.lean`
- `Poincare/Global/CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction.lean`
- `Poincare/Global/CartanRootedOverlapRefinedInsertionCompactHistoryReduction.lean`
- `Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary.lean`
- `Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean`

These files are a candidate frontier, not a pre-approved next task. The next
orchestrator must first identify the exact strongest consumer at HEAD and
extract one unresolved hypothesis shape into a v2 Task.

## Exact First Action for the Next Agent

From the repository root:

```sh
git status --short --branch
git log -5 --oneline
rg -n 'theorem|Boundary|Reduction|Provider' \
  Poincare/Global/CartanRootedOverlapRefinedInsertionCompactHistoryReduction.lean \
  Poincare/Global/PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary.lean
```

Then trace the strongest theorem's direct consumers and create one task using
`harness/v2/schemas/task.schema.json`. Do not start a broad proof job before
that task has a frozen base commit, file scope, and acceptance commands.

## Planned Runtime Topology

Read-only host inspection on 2026-07-17 found:

- `mj-zima`: reachable Ubuntu x86_64 host; tmux and git installed;
  `~/.local/bin/codex` exists but is not on the noninteractive SSH `PATH`; no
  Poincare clone was found at the three common candidate paths checked.
- `mj-spark-1` and `mj-spark-2`: reachable DGX Spark aarch64 hosts.
- Both Sparks were participating in a live Ray/vLLM workload and each had an
  active GPU worker using about 26 GB. That workload is out of scope and was
  left untouched.
- The old `/home/mj-kang/models/mistralai-Leanstral-2603` install path was not
  present. No Leanstral directory was found in the shallow model/mount search.

The desired new model is the exact official artifact
`mistralai/Leanstral-1.5-119B-A6B`. Model installation, vLLM version checks,
multi-node fit, and a dedicated endpoint are Phase 0 work. Do not stop the
current Ray cluster or reuse its ports without explicit authorization.

## Handoff Goal

The target system is:

- Codex GPT on `mj-zima` as the only orchestrator and merge authority;
- Leanstral served on the DGX Spark pair as a bounded Lean proof worker;
- isolated worktrees and independent Lean gates on `mj-zima`;
- append-only Task, Job, prompt, diff, compiler, and review evidence;
- tmux for the initial control plane, with restart-safe state on disk.

The implementation plan and data contracts are in `harness/v2/SPEC.md`.
