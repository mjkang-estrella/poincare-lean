# Metric transport blocked by the frozen fiber identification

Date: 2026-09-07, America/Los_Angeles.
Branch: `worker/metric-transport`.
Base: `7e955466b24a22af0873a73f20a3b00d7e8f05b9`.
Verified proof commit: `c9eb952c`.

## Outcome and stop condition

The frozen transport preserving `inner` as a function on the definitionally
identified copies of `E` is mathematically false for arbitrary preferred-chart
selections with equal maximal atlases. This attempt stops under hard rule 2
of `harness/tasks/M5-glob-69.md`, the invalid-statement rule. It does not claim
partial-success stop condition (b), a completed transport, or a fully
Lean-instantiated counterexample.

One new theorem has been proved and committed in the sole allowed Lean file:
`Poincare.RiemannianMetricInstanceTransport.inner_trivialization_apply`.
It computes the hom-bundle trivialization of an actual metric by applying the
inverse tangent trivialization to both arguments. In particular, the moving
preferred chart cannot be omitted. No existing Lean file or root import was
edited. No ledger, task, or acceptance status was changed.

## Checked pointwise formula

Write `c_x = chartAt E x`. For `x` in the source of `c_a`, Lean verifies

```text
(trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) ... a ⟨x, g.inner x⟩).2 v w
  = g.inner x (A(a,x) v) (A(a,x) w),
A(a,x) = (tangentBundleCore I M).coordChange (achart E a) (achart E x) x.
```

By Mathlib's `tangentBundleCore_coordChange_achart`, the operator is

```text
A(a,x) = D(extChartAt I x ∘ (extChartAt I a).symm)(extChartAt I a x),
```

with the derivative within `range I`. Here `I = 𝓡 3`, so the model is
boundaryless and this is the ordinary derivative.

The tangent trivialization itself goes in the opposite direction:
`TangentBundle.trivializationAt_apply` uses the derivative from `c_x` to
`c_a`. Its inverse uses the derivative from `c_a` to `c_x`, as verified by
`TangentBundle.symmL_trivializationAt_eq_core` and the new theorem.

`TangentSpace` is a type synonym for `E`. However, its total-space topology
comes from `tangentBundleCore`, whose `indexAt` is `achart`. The resulting
bundle therefore depends on the preferred chart at every moving base point.
Equality of maximal atlases identifies the available smooth base charts;
it does not identify their raw-fiber trivialization functions or the
resulting total-space topologies through the identity of `E`.

## Mathematical counterexample, not yet instantiated as a Lean theorem

Take `M = E = ClosedSmoothModel 3` with its usual topology and usual charted
structure. Take the constant Euclidean metric `g.inner x = innerSL ℝ`.
Mathlib's `riemannianMetricVectorSpace E` supplies this metric at order `ω`;
its smoothness can be lowered to `∞`.

Define a second charted structure with atlas `{id, s}`, where `s(y) = 2 • y`.
Choose `chartAt E 0 = id`, and choose `chartAt E x = s` for every `x ≠ 0`.
Both charts have source and target `univ`. All transition maps are invertible
linear maps, hence smooth. The maximal atlas is the ordinary smooth maximal
atlas. These charts even satisfy every positive uniform source-ball bound.

Suppose the requested transport existed and retained `g.inner` as raw
bilinear maps on `E`. In its hom-bundle trivialization at anchor `a = 0`,
the checked formula gives

```text
A(0,0) = id,              coefficient at 0 = innerSL ℝ,
A(0,x) = 2 • id (x ≠ 0),  coefficient at x = 4 • innerSL ℝ.
```

Evaluate on any fixed nonzero `v` in both slots. The value at zero is
`⟪v,v⟫ > 0`; the value at every nonzero point is `4 * ⟪v,v⟫`.
This is discontinuous at zero. But `Bundle.contMDiffAt_section` applied to
the required `contMDiff` field makes these coefficients smooth, hence
continuous. This is a contradiction.

Thus the issue is in the required equality of raw `inner` values, before
any difficulty proving hom-bundle smoothness. The proposed vector-field
fallback with unchanged raw fiber values also fails: its trivialization
at zero sends a constant nonzero `v` to `v` at zero and `(1/2) • v` away
from zero.

The counterexample uses no compactness, matching the frozen transport's
listed assumptions. `ClosedSmoothRiemannianMetric` itself does not require
`CompactSpace`; “Closed” in its name does not add that assumption.

## Exact first action for the next task

Revise the frozen `transport_inner` contract to use the geometric tangent
identification. For old and new preferred charts `c_x` and `c'_x`, the
new-to-old identification is

```text
J_x = D(c_x ∘ (c'_x).symm)(c'_x x),
g'.inner x v w = g.inner x (J_x v) (J_x w).
```

First construct this fiberwise continuous linear equivalence and prove that
it intertwines the two tangent trivializations. Then transport the bilinear
form by applying `J_x` to both inputs. This is a proposed replacement target,
not an implementation or silent weakening of the frozen one. In the example,
the corrected raw coefficients are `innerSL ℝ` at zero and
`(1/4) • innerSL ℝ` elsewhere, which have constant coefficients in the fixed
identity-chart trivialization.

No exact “resisting def” and conditional `target_of_resisting` constructor
are added: those belong to partial-success stop condition (b). Here the
frozen implication itself is false, so introducing it as a hypothesis would
only hide the invalid statement. The requested distance equality was skipped
because no transport satisfying the frozen contract exists. No claim about
the distance theorem for a corrected geometric transport is made.

## Actual acceptance commands and output

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/RiemannianMetricInstanceTransport.lean
```

Exit 0, empty stdout/stderr, recorded in
`/tmp/metric-transport-lemma-01.log`.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.RiemannianMetricInstanceTransport
```

Exit 0:

```text
✔ [2702/2702] Built Poincare.Global.RiemannianMetricInstanceTransport (3.1s)
Build completed successfully (2702 jobs).
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/RiemannianMetricInstanceTransport.lean
```

Exit 1, empty output, meaning no matches.

```sh
git diff --check
```

Exit 0, empty output.

The axiom probe `/tmp/metric-transport-axioms.lean` contains:

```lean
import Poincare.Global.RiemannianMetricInstanceTransport
#print axioms Poincare.RiemannianMetricInstanceTransport.inner_trivialization_apply
#check Poincare.RiemannianMetricInstanceTransport.inner_trivialization_apply
```

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/metric-transport-axioms.lean
```

Exit 0:

```text
'Poincare.RiemannianMetricInstanceTransport.inner_trivialization_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.RiemannianMetricInstanceTransport.inner_trivialization_apply.{u_1} {M : Type u_1} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric 3 M) {a x : M} (hx : x ∈ (chartAt (Poincare.ClosedSmoothModel 3) a).source)
  (v w : Poincare.ClosedSmoothModel 3) :
  ((↑(trivializationAt (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
                (fun x =>
                  TangentSpace (Poincare.closedSmoothModelWithCorners 3) x →L[ℝ]
                    TangentSpace (Poincare.closedSmoothModelWithCorners 3) x →L[ℝ] ℝ)
                a)
            ⟨x, g.inner x⟩).2
        v)
      w =
    ((g.inner x)
        (((tangentBundleCore (Poincare.closedSmoothModelWithCorners 3) M).coordChange
            (achart (Poincare.ClosedSmoothModel 3) a) (achart (Poincare.ClosedSmoothModel 3) x) x)
          v))
      (((tangentBundleCore (Poincare.closedSmoothModelWithCorners 3) M).coordChange
          (achart (Poincare.ClosedSmoothModel 3) a) (achart (Poincare.ClosedSmoothModel 3) x) x)
        w)
```

Only the worker gate was run. Root integration audits and `lake build` of
the entire project remain the orchestrator's responsibility.

## Failed compiler evidence

The first pointwise-formula probe ended with `rfl` before simplifying the
trivial scalar bundle's linear map. Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/metric-transport-probe.lean
```

First attempt, exit 1, preserved as `/tmp/metric-transport-probe-01.log`:

```text
/tmp/metric-transport-probe.lean:24:4: error: Tactic `rfl` failed: The left-hand side
  (Trivialization.continuousLinearMapAt ℝ (trivializationAt ℝ (fun x => ℝ) a) x)
    (((g.inner x) (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) v))
      (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) w))
is not definitionally equal to the right-hand side
  ((g.inner x) (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) v))
    (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) w)

M : Type u_1
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
a x : M
hx : x ∈ (chartAt E a).source
v w : E
⊢ (Trivialization.continuousLinearMapAt ℝ (trivializationAt ℝ (fun x => ℝ) a) x)
      (((g.inner x) (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) v))
        (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) w)) =
    ((g.inner x) (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) v))
      (((tangentBundleCore I M).coordChange (achart E a) (achart E x) x) w)
```

Second attempt used `simp` but left a definitional equality, exit 1,
preserved as `/tmp/metric-transport-probe-02.log`:

```text
/tmp/metric-transport-probe.lean:21:2: error: unsolved goals
M : Type u_1
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
a x : M
hx : x ∈ (chartAt E a).source
v w : E
⊢ ((g.inner x) ((fderiv ℝ (↑(chartAt E x) ∘ ↑(chartAt E a).symm) (↑(chartAt E a) x)) v))
      ((fderiv ℝ (↑(chartAt E x) ∘ ↑(chartAt E a).symm) (↑(chartAt E a) x)) w) =
    ((g.inner x) ((fderiv ℝ (↑(chartAt E x) ∘ ↑(chartAt E a).symm) (↑(chartAt E a) x)) v))
      ((fderiv ℝ (↑(chartAt E x) ∘ ↑(chartAt E a).symm) (↑(chartAt E a) x)) w)
```

The third attempt used `simp` followed by `rfl`, exited 0 with empty output,
and is preserved as `/tmp/metric-transport-probe-03.log`. The accepted source
uses that checked proof. These are proof-script errors in the pointwise
calculation, not compiler refutations of the full frozen target.

The proof diff against the recorded base is preserved at
`/tmp/metric-transport-final.diff` and permanently by commit `c9eb952c`.
