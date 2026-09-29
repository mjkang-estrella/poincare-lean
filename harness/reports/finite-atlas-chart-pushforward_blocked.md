# Finite-atlas chart push-forward: blocked with verified partial results

Date: 2026-09-15. Branch: `worker/finite-atlas-chart-pushforward`.
Base: `6b8d0c3d51c8ad95019277dce709ab52a5a028f5`.
Proof head: `088b8a45dd0c2ac924ff64844d2c54c70f2e03fd`.

## Result

The frozen task is blocked by its normalization and quantitative assumptions.
No bounded graph push-forward or extraction operator is claimed. All ten new
named theorems pass the focused gate, and all 130 emitted declarations of the
extended module, including internal declarations, have exactly the required
three foundational dependencies. The original source is an unchanged prefix;
only declarations after its original namespace closing line were added.

This is a worker result awaiting independent review. No merge, acceptance,
root integration build, or completion claim was made. Frozen task and contract
files and every other existing Lean file are unchanged.

## Verified partial results

Three mathematical proof items were committed separately:

- `6faac3cf`: coordinate substitution and composition on actual chart sources.
- `6040dce5`: value-level partition reconstruction and the extra-weight obstruction.
- `e1954d22`: incompatibility of ordinary unweighted transport with the weighted carrier.

Commit `088b8a45` replaces one simplifier step by a termwise sum proof, preserving
its statement while removing two generated helpers with empty dependency sets.
The ordinary worker gate had allowed those helpers; the stricter exact-set
scan detected them. The final scan includes all internal declarations.

New declarations:

- `Poincare.FiniteAtlasParabolicTensorSpace.change_chart`
- `Poincare.FiniteAtlasParabolicTensorSpace.change_cocycle`
- `Poincare.FiniteAtlasParabolicTensorSpace.partition_zero_of_not_source`
- `Poincare.FiniteAtlasParabolicTensorSpace.sum_partition`
- `Poincare.FiniteAtlasParabolicTensorSpace.localized_transport_eq`
- `Poincare.FiniteAtlasParabolicTensorSpace.sum_localized_transport`
- `Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport`
- `Poincare.FiniteAtlasParabolicTensorSpace.sum_partition_sq_lt_one`
- `Poincare.FiniteAtlasParabolicTensorSpace.reweighted_transport_ne_entry`
- `Poincare.FiniteAtlasParabolicTensorSpace.unweighted_transport_not_mem`

The coordinate composition result is a value identity. The derivative/Jacobian
cocycle and a bounded transported graph have not been constructed.

The generic value reconstruction theorems apply to both
`Poincare.FiniteAtlasParabolicTensorSpace.Y_M` and
`Poincare.FiniteAtlasParabolicTensorSpace.X_M`, using respectively
`Poincare.FiniteAtlasParabolicTensorSpace.evalY` and
`Poincare.FiniteAtlasParabolicTensorSpace.evalX`. They do not assert existence
of carriers for their summands. In particular, value reconstruction alone is
not the requested bounded-linear-operator construction.

## Blocker 1: graph composition with a bound depending only on C² sup bounds

The Hessian chain rule contains `(Du ∘ φ) D²φ`. Its Hölder bound needs Hölder
control of `D²φ`, not merely its supremum. The survey already distinguishes
this: scalar transport needs C²,α control, while transport of covariant
2-tensors also differentiates two Jacobian factors and needs their C²,α control,
for example C³,α control of the transition map. Compactness and smoothness give
such bounds for a fixed buffered transition, but do not make them controlled
by its C² sup bounds alone.

Here is a mathematical counterexample to the requested uniform quantitative
dependence, not a Lean-formalized counterexample. Fix `0 < α < 1`, `T = 1`, and

```
φ_n(x₁,x₂,x₃) = (x₁ + n⁻² sin(n x₁), x₂, x₃),  n ≥ 2.
u(t,y) = t η(y) y₁,  0 ≤ t ≤ 1,
```

where η is a fixed compactly supported smooth cutoff equal to one on a
neighborhood of the origin. Extend the four graph components by zero off the
time cylinder. The input graph is fixed, has zero initial trace, and has finite
norm. These are smooth global diffeomorphisms with uniform Lipschitz and
inverse-Lipschitz bounds, uniform derivatives through order two, and uniform
value bounds on any fixed compact set. Near the origin at time one, the
`(1,1)` Hessian component of the composition is `−sin(n x₁)`. Comparing
`x₁ = 0` with `x₁ = π/(2n)` gives a Hölder quotient `(2n/π)^α`. It is unbounded.
Thus common C² sup bounds cannot give the requested common graph-norm bound.

No replacement norm, hidden higher derivative hypothesis, or modified frozen
statement was introduced. The missing analytic construction remains the
zero-extended, buffered nonlinear composition graph, including the Hölder
bound for its Hessian and the bounds for Jacobian-weight products.

## Blocker 2: ordinary transport does not produce the stored weighted family

At a manifold point x, let `Tᵢⱼ Fⱼ` denote the double Jacobian contraction
from source chart j into destination chart i, with precisely the derivative
orientation in `Poincare.FiniteAtlasParabolicTensorSpace.jac`.
The existing carrier law is

```
χⱼ(x) Fᵢ(t,φᵢx) = χᵢ(x) Tᵢⱼ Fⱼ(t,φⱼx).
```

A tensor obtained by ordinary chart transport instead satisfies
`Fᵢ = Tᵢⱼ Fⱼ`. Combining these would force `χⱼ Fᵢ = χᵢ Fᵢ`, which fails for a
nonzero entry where the weights differ. This incompatibility is proved in
`Poincare.FiniteAtlasParabolicTensorSpace.unweighted_transport_not_mem` using
the actual carrier membership and actual Jacobian contraction.

To represent a genuine pushed tensor in this carrier, the destination chart
must multiply its representation by χᵢ. This is also necessary for the support
condition: support in a transported image of the source support does not by
itself imply support in the destination set
`Poincare.FiniteAtlasParabolicTensorSpace.coordSupport`.

Even after inserting the destination factor, no claim is made that all
carrier witnesses, symmetry for arbitrary input component families, Jacobian
cocycles, zero extensions, or quantitative bounds have been proved here.
The input 3×3 family must also have the symmetry required by the carrier.

## Blocker 3: extraction multiplies an already localized entry again

Under the literal stored-entry interpretation of restriction in item 3,
extraction is `χⱼ Fⱼ`. The entries Fⱼ already include χⱼ, as specified in
survey section 1.2. After using the destination factor required by the
weighted carrier, the proposed reconstruction is therefore

```
Σⱼ χⱼ(x) [χᵢ(x) Tᵢⱼ Fⱼ] = (Σⱼ χⱼ(x)²) Fᵢ,
```

not Fᵢ. This equation is the checked theorem
`Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport`.
The strict inequality for the sum of squares at any point with one weight
strictly between zero and one is the checked theorem
`Poincare.FiniteAtlasParabolicTensorSpace.sum_partition_sq_lt_one`.
Consequently the requested equality fails at any nonzero entry at such a
point, by `Poincare.FiniteAtlasParabolicTensorSpace.reweighted_transport_ne_entry`.
These are conditional obstructions on the actual atlas and carrier; no explicit
nonzero global carrier or concrete atlas counterexample is constructed here.

The correct value-level sum, using the stored entries once, is proved by
`Poincare.FiniteAtlasParabolicTensorSpace.sum_localized_transport`:

```
Σⱼ χᵢ(x) Tᵢⱼ Fⱼ = (Σⱼ χⱼ(x)) Fᵢ = Fᵢ.
```

Each summand is set to zero when x is outside the source chart. The proof uses
subordination to show that χⱼ also vanishes there. It makes no division by a
partition function and does not assume all charts contain x.

If “restriction” was intended to mean the chart representation of an already
reconstructed unweighted tensor, multiplying that representation by χⱼ gives
exactly the stored entry Fⱼ. That interpretation needs to be explicit in a
superseding task. It is not multiplication of the stored entry by χⱼ again.
With literal extraction and destination-localized push, the own-chart
composition also has two factors χᵢ, so it cannot have the stated single-factor
formula in general.

### Exact resisting Lean goal

An intentionally unsuccessful proof of the item-3 value identity rewrites by
`Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport`.
The command exited 1 with the following exact output. The final module does
not contain this failed example.

```text
/private/tmp/finite-atlas-chart-pushforward-evidence/reconstruction-failure.lean:404:47: error: unsolved goals
M : Type u
inst✝⁴ : TopologicalSpace M
inst✝³ : ChartedSpace (ClosedSmoothModel 3) M
inst✝² : IsManifold (closedSmoothModelWithCorners 3) ∞ M
A : AtlasData M
H : Type u_1
inst✝¹ : NormedAddCommGroup H
inst✝ : NormedSpace ℝ H
ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ
f : ↥(tensorSubmodule A ev)
i j : Fin A.cover.chartCount
a b : Fin 3
t : ℝ
x : M
hi : x ∈ (chart A i).source
hpos : 0 < (A.partition j) x
hlt : (A.partition j) x < 1
hne : (ev (t, ↑(chart A i) x)) (↑f (i, a, b)) ≠ 0
⊢ (∑ j, (A.partition j) x ^ 2) * (ev (t, ↑(chart A i) x)) (↑f (i, a, b)) = (ev (t, ↑(chart A i) x)) (↑f (i, a, b))
```

The stronger committed theorem proves the negation under exactly the displayed
nonzero and genuine-overlap hypotheses. More analytic estimates cannot solve
this algebraic goal.

## Verification at the final proof head

Commands and actual results:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
(no output)
exit 0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
(no output)
exit 1 (no matches)

$ git diff --check
(no output)
exit 0

$ LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/finite-atlas-chart-pushforward Poincare.Global.FiniteAtlasParabolicTensorSpace
=== GATE: forbidden tokens in Poincare/Global/FiniteAtlasParabolicTensorSpace.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FiniteAtlasParabolicTensorSpace ===
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3869/3869] Built Poincare.Global.FiniteAtlasParabolicTensorSpace (6.1s)
Build completed successfully (3869 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=94 nonstandard=[]
=== GATE: PASS ===
exit 0
```

The build's displayed linter note comes from replayed dependencies; focused
compilation of the changed module produces no warnings. The module-wide
worker gate excludes internal names and checks only that dependencies are
allowed. The additional audit below includes internal names and checks exact
set equality, covering the task's stricter requirement.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.FiniteAtlasParabolicTensorSpace
    | throwError "module not found"
  let mut bad : Array String := #[]
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      if axs.size != 3 || !axs.contains ``propext || !axs.contains ``Classical.choice || !axs.contains ``Quot.sound then
        bad := bad.push s!"{n}: {axs}"
  logInfo m!"EXACT_EMITTED_SCAN declarations={count} bad={bad}"
  unless bad.isEmpty do throwError "unexpected dependency set"
```

```text
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/finite-atlas-chart-pushforward-evidence/emitted-audit.lean
EXACT_EMITTED_SCAN declarations=130 bad=[]
exit 0
```

For the explicit print gate, append these commands to a copy of the complete
changed module and compile it. This avoids depending on a stale compiled copy.

```lean
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.change_chart
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.change_cocycle
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.partition_zero_of_not_source
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.sum_partition
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.localized_transport_eq
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.sum_localized_transport
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.sum_partition_sq_lt_one
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.reweighted_transport_ne_entry
#print axioms Poincare.FiniteAtlasParabolicTensorSpace.unweighted_transport_not_mem
```

```text
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/finite-atlas-chart-pushforward-evidence/final-audit.lean
'Poincare.FiniteAtlasParabolicTensorSpace.change_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.change_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.partition_zero_of_not_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.sum_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.localized_transport_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.sum_localized_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.sum_partition_sq_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.reweighted_transport_ne_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.unweighted_transport_not_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

## Failed attempts retained as evidence

The first algebra proof failed because the statement needed a local classical
decidability instance for chart membership, and a cancellation lemma was
incorrectly used as an iff. The compiler-generated recovery term in the output
below is not a term written into the source. The next focused compilation
passed after those corrections.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:292:23: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (x ∈ (chart A j).source)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:299:2: error: unsolved goals
case neg
M : Type u
inst✝⁴ : TopologicalSpace M
inst✝³ : ChartedSpace (ClosedSmoothModel 3) M
inst✝² : IsManifold (closedSmoothModelWithCorners 3) ∞ M
A : AtlasData M
H : Type u_1
inst✝¹ : NormedAddCommGroup H
inst✝ : NormedSpace ℝ H
ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ
f : ↥(tensorSubmodule A ev)
i j : Fin A.cover.chartCount
a b : Fin 3
t : ℝ
x : M
hi : x ∈ (chart A i).source
hj : x ∉ (chart A j).source
⊢ (A.partition i) x * sorry = 0
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:299:15: warning: This simp argument is unused:
  if_neg hj

Hint: Omit it from the simp argument list.
  simp only [i̵f̵_̵n̵e̵g̵ ̵h̵j̵,̵ ̵mul_zero, partition_zero_of_not_source A j x hj, zero_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:299:26: warning: This simp argument is unused:
  mul_zero

Hint: Omit it from the simp argument list.
  simp only [if_neg hj, m̵u̵l̵_̵z̵e̵r̵o̵,̵ ̵partition_zero_of_not_source A j x hj, zero_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:305:29: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (x ∈ (chart A j).source)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:310:11: error: `simp` made no progress
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:317:48: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (x ∈ (chart A j).source)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:322:11: error: `simp` made no progress
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:343:48: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (x ∈ (chart A k).source)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:351:28: error(lean.invalidField): Invalid field `mp`: The environment does not contain `Function.mp`, so it is not possible to project the field `mp` from an expression
  mul_right_cancel₀ hne
of type
  ?m.263 * (ev (t, ↑(chart A i) x)) (↑f (i, a, b)) = ?m.265 * (ev (t, ↑(chart A i) x)) (↑f (i, a, b)) → ?m.263 = ?m.265
exit 1
```

The first full emitted audit then detected the two simplifier helpers with
empty dependency sets. The subsequent proof rewrite removed both helpers.

```text
EXACT_EMITTED_SCAN declarations=132 bad=[Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport._simp_1_2: #[],
 Poincare.FiniteAtlasParabolicTensorSpace.sum_reweighted_localized_transport._simp_1_1: #[]]
/private/tmp/finite-atlas-chart-pushforward-evidence/emitted-audit.lean:3:0: error: unexpected dependency set
exit 1
```

The failed reconstruction probe can be reproduced by appending the following
to the complete changed module. Its diagnostic above was produced before the
last proof-only rewrite, so absolute line numbers can shift on replay.

```lean
namespace Poincare.FiniteAtlasParabolicTensorSpace
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M)
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  (ev : ℝ × Poincare.ClosedSmoothModel 3 → H →L[ℝ] ℝ)
attribute [local instance] Classical.propDecidable
example (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hi : x ∈ (chart A i).source)
    (hpos : 0 < A.partition j x) (hlt : A.partition j x < 1)
    (hne : ev (t, chart A i x) (f.val (i, a, b)) ≠ 0) :
    (∑ k, A.partition k x * (A.partition i x * (if x ∈ (chart A k).source then
      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i k x c a * jac A i k x d b) *
        ev (t, chart A k x) (f.val (k, c, d)) else 0))) =
      ev (t, chart A i x) (f.val (i, a, b)) := by
  rw [sum_reweighted_localized_transport A ev f i a b t x hi]
end Poincare.FiniteAtlasParabolicTensorSpace
```

## First action for the next worker

Run:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
```

Then have the orchestrator issue a superseding contract which explicitly uses
destination-localized push, extraction of the already stored entry, symmetric
input tensors, and buffered C²,α scalar/C³,α transition bounds. For equality of
graphs from values, state a positive time interval. The first new analytic
objective is a bounded nonlinear composition map with the required Hölder
bounds and a valid zero extension across chart boundaries. Do not weaken the
existing frozen task or treat the value-level sums as completed graph maps.

## Final proof diff

```diff
diff --git a/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean b/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
index f931e5b9..d3029966 100644
--- a/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
+++ b/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
@@ -246,0 +247,143 @@ end Poincare.FiniteAtlasParabolicTensorSpace
+
+namespace Poincare.FiniteAtlasParabolicTensorSpace
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
+  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
+  (A : AtlasData M)
+
+/-- Coordinate changes recover the destination coordinates on their actual source. -/
+theorem change_chart (i j : Fin A.cover.chartCount) (x : M)
+    (hx : x ∈ (chart A i).source) :
+    change A i j (chart A i x) = chart A j x := by
+  exact congrArg (chart A j) ((chart A i).left_inv hx)
+
+/-- Composition through a third chart agrees on the common chart domain. -/
+theorem change_cocycle (i j k : Fin A.cover.chartCount) (x : M)
+    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source) :
+    change A j k (change A i j (chart A i x)) = change A i k (chart A i x) := by
+  rw [change_chart A i j x hi, change_chart A j k x hj, change_chart A i k x hi]
+
+end Poincare.FiniteAtlasParabolicTensorSpace
+
+namespace Poincare.FiniteAtlasParabolicTensorSpace
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
+  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
+  (A : AtlasData M)
+
+/-- A partition member vanishes away from its chart source. -/
+theorem partition_zero_of_not_source (i : Fin A.cover.chartCount) (x : M)
+    (hx : x ∉ (chart A i).source) : A.partition i x = 0 :=
+  image_eq_zero_of_notMem_tsupport (fun h => hx (partition_support_source A i h))
+
+/-- The finite partition has total weight one at every manifold point. -/
+theorem sum_partition (x : M) : ∑ i, A.partition i x = 1 := by
+  simpa only [finsum_eq_sum_of_fintype] using A.partition.sum_eq_one (Set.mem_univ x)
+
+variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
+  (ev : ℝ × Poincare.ClosedSmoothModel 3 → H →L[ℝ] ℝ)
+
+attribute [local instance] Classical.propDecidable
+
+/-- One localized transport equals the source partition weight times the destination entry. -/
+theorem localized_transport_eq (f : ↥(tensorSubmodule A ev))
+    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hi : x ∈ (chart A i).source) :
+    A.partition i x * (if x ∈ (chart A j).source then
+      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i j x c a * jac A i j x d b) *
+        ev (t, chart A j x) (f.val (j, c, d)) else 0) =
+      A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) := by
+  classical
+  by_cases hj : x ∈ (chart A j).source
+  · simpa only [if_pos hj] using (weighted_transition A ev f i j a b t x ⟨hi, hj⟩).symm
+  · simp only [if_neg hj, mul_zero, partition_zero_of_not_source A j x hj, zero_mul]
+
+/-- Summing the transported stored entries reconstructs each localized value. -/
+theorem sum_localized_transport (f : ↥(tensorSubmodule A ev))
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hi : x ∈ (chart A i).source) :
+    (∑ j, A.partition i x * (if x ∈ (chart A j).source then
+      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i j x c a * jac A i j x d b) *
+        ev (t, chart A j x) (f.val (j, c, d)) else 0)) =
+      ev (t, chart A i x) (f.val (i, a, b)) := by
+  classical
+  simp_rw [localized_transport_eq A ev f i _ a b t x hi]
+  rw [← Finset.sum_mul, sum_partition A x, one_mul]
+
+/-- Multiplying the stored entries by their partition weights a second time squares the weights. -/
+theorem sum_reweighted_localized_transport (f : ↥(tensorSubmodule A ev))
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hi : x ∈ (chart A i).source) :
+    (∑ j, A.partition j x * (A.partition i x * (if x ∈ (chart A j).source then
+      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i j x c a * jac A i j x d b) *
+        ev (t, chart A j x) (f.val (j, c, d)) else 0))) =
+      (∑ j, (A.partition j x) ^ 2) * ev (t, chart A i x) (f.val (i, a, b)) := by
+  classical
+  rw [Finset.sum_mul]
+  apply Finset.sum_congr rfl
+  intro j _
+  rw [localized_transport_eq A ev f i j a b t x hi]
+  ring
+
+/-- A genuinely overlapping partition has squared weights with total strictly below one. -/
+theorem sum_partition_sq_lt_one (x : M) (j : Fin A.cover.chartCount)
+    (hpos : 0 < A.partition j x) (hlt : A.partition j x < 1) :
+    ∑ i, (A.partition i x) ^ 2 < 1 := by
+  rw [← sum_partition A x]
+  apply Finset.sum_lt_sum
+  · intro i _
+    have hn := A.partition.nonneg i x
+    have hl := A.partition.le_one i x
+    nlinarith
+  · exact ⟨j, Finset.mem_univ j, by nlinarith⟩
+
+/-- Extra source weights cannot reconstruct a nonzero entry on a genuine partition overlap. -/
+theorem reweighted_transport_ne_entry (f : ↥(tensorSubmodule A ev))
+    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hi : x ∈ (chart A i).source)
+    (hpos : 0 < A.partition j x) (hlt : A.partition j x < 1)
+    (hne : ev (t, chart A i x) (f.val (i, a, b)) ≠ 0) :
+    (∑ k, A.partition k x * (A.partition i x * (if x ∈ (chart A k).source then
+      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i k x c a * jac A i k x d b) *
+        ev (t, chart A k x) (f.val (k, c, d)) else 0))) ≠
+      ev (t, chart A i x) (f.val (i, a, b)) := by
+  classical
+  rw [sum_reweighted_localized_transport A ev f i a b t x hi]
+  intro heq
+  have hsum : (∑ k, (A.partition k x) ^ 2) = 1 :=
+    mul_right_cancel₀ hne (heq.trans (one_mul _).symm)
+  exact (ne_of_lt (sum_partition_sq_lt_one A x j hpos hlt)) hsum
+
+end Poincare.FiniteAtlasParabolicTensorSpace
+
+namespace Poincare.FiniteAtlasParabolicTensorSpace
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
+  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
+  (A : AtlasData M)
+  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
+  (ev : ℝ × Poincare.ClosedSmoothModel 3 → H →L[ℝ] ℝ)
+
+/-- An ordinary unweighted transition is incompatible with unequal partition weights at a nonzero entry. -/
+theorem unweighted_transport_not_mem (f : LocalProduct A H)
+    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hx : x ∈ (chart A i).source ∩ (chart A j).source)
+    (hraw : ev (t, chart A i x) (f (i, a, b)) =
+      ∑ c : Fin 3, ∑ d : Fin 3, (jac A i j x c a * jac A i j x d b) *
+        ev (t, chart A j x) (f (j, c, d)))
+    (hweight : A.partition i x ≠ A.partition j x)
+    (hne : ev (t, chart A i x) (f (i, a, b)) ≠ 0) :
+    f ∉ tensorSubmodule A ev := by
+  intro hf
+  have hw := weighted_transition A ev ⟨f, hf⟩ i j a b t x hx
+  change A.partition j x * ev (t, chart A i x) (f (i, a, b)) =
+    A.partition i x * (∑ c : Fin 3, ∑ d : Fin 3,
+      (jac A i j x c a * jac A i j x d b) *
+        ev (t, chart A j x) (f (j, c, d))) at hw
+  rw [← hraw] at hw
+  exact hweight (mul_right_cancel₀ hne hw).symm
+
+end Poincare.FiniteAtlasParabolicTensorSpace
```
