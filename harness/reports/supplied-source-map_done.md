# Supplied source map worker result

Date: 2026-09-08. Branch: `worker/supplied-source-map`.
Base: `5f57f9b6085a0037461b703f79778e69fe638aad`.
Proof head: `1d1480cd`.

All four frozen targets are proved in the single new Lean module
`Poincare/Global/CartanSuppliedSourceMap.lean`, under namespace
`Poincare.CartanSuppliedSourceMap`. The existing manifold instances suffice;
no compactness, curvature, joint regularity, or extra target condition was
added. This is a worker result awaiting independent orchestrator review.
No merge or task acceptance was performed.

The source anchor belongs to `S.normal x` and maps to zero. The linear
equivalence preserves zero; `F.zero_mem_source` and `F.chart_zero` then give
the next membership and value. The round-sphere chart sends its anchor to
zero, so its inverse is defined there and returns `p`. These laws prove both
anchor targets. The forward-map formula is reflexive. Generic specialization
rewrites with that formula and the existing source and Cartan map formulas.
It asserts equality of total forward maps, as requested.

Only the new Lean module, this report, and the required dated `HANDOFF.md`
entry change. No existing Lean source or root import changes. The assigned
isolated branch is retained as required by the task-specific contract.
H1/H2, supplied successor data, chain continuation, and sphere recognition
are outside this result.

## Verified lemma commits

Each commit followed a successful direct Lean check of the cumulative file.

- `fce465dc`: definition and `anchor_mem_source`.
- `20ed70af`: `germ_anchor`.
- `3bcf7ab4`: `germ_apply`.
- `1d1480cd`: `generic_map_eq`.

## Direct compiler checks

Command after each lemma:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceMap.lean
```

The successful runs each exited 0 with empty stdout/stderr. Their logs are
`/tmp/supplied-source-map-anchor-mem.log`,
`/tmp/supplied-source-map-germ-anchor.log`,
`/tmp/supplied-source-map-germ-apply.log`, and
`/tmp/supplied-source-map-generic-map-eq-rewrite.log`.

The first generic specialization attempt used a bare `rfl`. That run exited
1, with this exact output, retained in
`/tmp/supplied-source-map-generic-map-eq.log`:

```text
Poincare/Global/CartanSuppliedSourceMap.lean:67:8: error: (kernel) deterministic timeout
```

The corrected proof uses `germ_apply`, function extensionality,
`CartanSourceExponential.genericFamily_apply`, and `CartanMap.cartanMap_apply`
before its final `rfl`. No heartbeat setting was increased.

## Focused worker gate

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/supplied-source-map Poincare.Global.CartanSuppliedSourceMap Poincare.CartanSuppliedSourceMap.anchor_mem_source Poincare.CartanSuppliedSourceMap.germ_anchor Poincare.CartanSuppliedSourceMap.germ_apply Poincare.CartanSuppliedSourceMap.generic_map_eq
```

Exit 0. Exact output, including the gate's five-line build tail:

```text
=== GATE: forbidden tokens in Poincare/Global/CartanSuppliedSourceMap.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.CartanSuppliedSourceMap ===
  omit [ChartedSpace E M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3358/3358] Built Poincare.Global.CartanSuppliedSourceMap (2.3s)
Build completed successfully (3358 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=6 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.CartanSuppliedSourceMap.anchor_mem_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.germ_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.germ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.generic_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
=== GATE: PASS ===
```

The gate runs `lake build Poincare.Global.CartanSuppliedSourceMap` and scans
all declarations owned by the module. Its scan covers six declarations,
including generated content, with no nonstandard dependencies. All four
named theorem closures are exactly `[propext, Classical.choice, Quot.sound]`.
No overlapping full build was launched by this worker.

## Exact name probes

`/tmp/supplied-source-map-probe.lean` contains:

```lean
import Poincare.Global.CartanSuppliedSourceMap
#check Poincare.CartanSuppliedSourceMap.anchor_mem_source
#check Poincare.CartanSuppliedSourceMap.germ_anchor
#check Poincare.CartanSuppliedSourceMap.germ_apply
#check Poincare.CartanSuppliedSourceMap.generic_map_eq
#print axioms Poincare.CartanSuppliedSourceMap.anchor_mem_source
#print axioms Poincare.CartanSuppliedSourceMap.germ_anchor
#print axioms Poincare.CartanSuppliedSourceMap.germ_apply
#print axioms Poincare.CartanSuppliedSourceMap.generic_map_eq
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-source-map-probe.lean`.
Exit 0. Exact output:

```text
Poincare.CartanSuppliedSourceMap.anchor_mem_source.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} (S : Poincare.CartanSourceExponential.Family g)
  (F : Poincare.CartanTargetExponential.Family) (x : M) (p : Poincare.RoundSphere3)
  (K : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) :
  x ∈ (Poincare.CartanSuppliedSourceMap.germ S F x p K).source
Poincare.CartanSuppliedSourceMap.germ_anchor.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} (S : Poincare.CartanSourceExponential.Family g)
  (F : Poincare.CartanTargetExponential.Family) (x : M) (p : Poincare.RoundSphere3)
  (K : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) :
  ↑(Poincare.CartanSuppliedSourceMap.germ S F x p K) x = p
Poincare.CartanSuppliedSourceMap.germ_apply.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} (S : Poincare.CartanSourceExponential.Family g)
  (F : Poincare.CartanTargetExponential.Family) (x : M) (p : Poincare.RoundSphere3)
  (K : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) :
  ↑(Poincare.CartanSuppliedSourceMap.germ S F x p K) = fun z =>
    ↑(chartAt (Poincare.ClosedSmoothModel 3) p).symm (↑(F.chart p) (K (↑(S.normal x) z)))
Poincare.CartanSuppliedSourceMap.generic_map_eq.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric 3 M) (x : M) (p : Poincare.RoundSphere3)
  (L : Poincare.CartanMap.TangentAlignment g x p) :
  ↑(Poincare.CartanSuppliedSourceMap.germ (Poincare.CartanSourceExponential.genericFamily g)
        Poincare.CartanTargetExponential.genericFamily x p L.toContinuousLinearEquiv) =
    Poincare.CartanMap.cartanMap g x p L
'Poincare.CartanSuppliedSourceMap.anchor_mem_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.germ_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.germ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedSourceMap.generic_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Source and whitespace checks

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedSourceMap.lean
git diff --check 5f57f9b6085a0037461b703f79778e69fe638aad
```

The token scan exited 1 with empty output, meaning no matches. The diff check
exited 0 with empty output. The initial checkout was clean and on the assigned
branch; `git worktree list --porcelain` and `git rev-parse HEAD` confirmed the
isolated worktree and base. The live toolchain check returned:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

The proof diff is retained in `/tmp/supplied-source-map-proof.diff` and in the
four commits. Scratch logs are supplemental; the failed compiler output and
successful gate/probe output are embedded here as durable evidence.

Exact first action for the orchestrator: independently run
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceMap.lean`
against these commits, then rerun the four name probes and worker gate before
acceptance. The next planned mathematical task is
`CartanSuppliedSourceGermTransfer.lean` from the inventory.
