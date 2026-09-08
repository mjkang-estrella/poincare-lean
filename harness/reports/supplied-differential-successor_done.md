# Supplied differential successor completed

Date: 2026-09-08. Branch: `worker/supplied-differential-successor`.
Frozen checkout base: `12a0da09cef76c99a34a9b35a6965b8eb8bb6052`.
Verified proof head: `4bb23927f051c7cc5b3dac178c2cdb33be394ac0`.

## Result

All five frozen targets are proved in the single new module
`Poincare/Global/CartanSuppliedDifferentialSuccessor.lean`:
`anchor_laws`, `generic_map_eq`, `vector_eq`, `successor_fields`, and
`eq_anchor_of_vector_eq_zero`. All displayed definitions and structures were
copied verbatim from the task, including explicit source/target chart hosts,
both anchor-validity fields, actual supplied-germ source membership, and the
reanchored derivative witness.

This meets task 6's exact stop condition and M5-glob-69 stop condition (a).
The result awaits independent orchestrator review and acceptance. No merge
or task acceptance was performed. The assigned worker branch is retained.
Only the new Lean file and this report change. Existing Lean files,
`Poincare.lean`, `HANDOFF.md`, and audit wiring are unchanged under the
explicit task scope.

The source anchor maps to zero, the framed linear equivalence preserves zero,
and the target normal chart's inverse returns its anchor. These facts give
both source membership and the anchor value. Generic specialization unfolds
the total forward composition and rewrites the existing normal/Cartan map
formulas. It proves equality on every input, without comparing selected
source sets.

For `vector_eq`, the stored source-coordinate equation identifies `z` with
the inverse normal image of `d.v` by injectivity of the explicit host chart.
The normal chart's right inverse law then gives
`d.v = Q.sourceNormal s.anchor z`. Both inverse-domain requirements come
from `source_vector_mem`, and host-chart membership comes from
`source_mem_oldChart`. The successor-field theorem exposes the geometric
state and retained predecessor-source membership. Normal-chart injectivity,
the recovered vector, and the anchor zero law prove the final zero-vector
conclusion.

No constructor from `CoordinateData` to `Data`, witness-independence theorem,
H1/H2 estimate, chain recursion, or recognition result is claimed. These are
later tasks in the frozen plan.

## Separate verified proof commits

Each commit followed successful direct Lean elaboration of the cumulative file.

| Commit | Verified addition | Compiler log |
| --- | --- | --- |
| `81682861` | Definitions and `anchor_laws` | `01-anchor.log` |
| `f3f52e2a` | `generic_map_eq` | `02-generic.log` |
| `cf8ed318` | `vector_eq` | `03-vector.log` |
| `cf7aaa53` | `successor_fields` | `04-fields.log` |
| `4bb23927` | `eq_anchor_of_vector_eq_zero` | `05-zero.log` |

Logs and scratch probes are retained under
`/tmp/supplied-differential-successor-evidence/`.
There were no failed compiler attempts. Each of the five direct checks exited
0 with empty stdout/stderr:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
```

Toolchain command and actual output, exit 0:

```sh
lake env lean --version
```

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

## Focused build and axiom gate

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/supplied-differential-successor Poincare.Global.CartanSuppliedDifferentialSuccessor Poincare.CartanSuppliedDifferentialSuccessor.anchor_laws Poincare.CartanSuppliedDifferentialSuccessor.generic_map_eq Poincare.CartanSuppliedDifferentialSuccessor.vector_eq Poincare.CartanSuppliedDifferentialSuccessor.successor_fields Poincare.CartanSuppliedDifferentialSuccessor.eq_anchor_of_vector_eq_zero
```

Exit 0. Actual output from `gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/CartanSuppliedDifferentialSuccessor.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.CartanSuppliedDifferentialSuccessor ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3606/3606] Built Poincare.Global.CartanSuppliedDifferentialSuccessor (3.9s)
Build completed successfully (3606 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=84 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.CartanSuppliedDifferentialSuccessor.anchor_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.generic_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.vector_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.successor_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.eq_anchor_of_vector_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is replayed from an unchanged dependency. The new module's direct
checks emitted no warnings. The focused build runs serially; no full root
build or integration audit was launched. The module-wide scan checks 84
non-internal declarations, including generated structure declarations.
Every named theorem has exactly the permitted three-dependency closure.

## Frozen-signature probe

The following probe was extracted from the task-6 block in
`harness/reports/parametrization-plan-2.md`, using each complete target type
as an `example` whose proof is the corresponding implemented theorem.
The shared instance binders and quantifier order are unchanged.

```lean
import Poincare.Global.CartanSuppliedDifferentialSuccessor
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

open CartanSuppliedDifferentialSuccessor
example : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g),
  s.anchor ∈ Q.sourceAnchors → s.target ∈ Q.targetAnchors →
  s.anchor ∈ (germ Q s).source ∧ map Q s s.anchor = s.target := anchor_laws

#print axioms CartanSuppliedDifferentialSuccessor.anchor_laws

example : ∀ (s : CartanChain.ChainState g), map (generic g) s = s.map := generic_map_eq

#print axioms CartanSuppliedDifferentialSuccessor.generic_map_eq

example : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.v = Q.sourceNormal s.anchor z := vector_eq

#print axioms CartanSuppliedDifferentialSuccessor.vector_eq

example : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.successor.anchor = z ∧
  d.successor.target = map Q s z ∧ z ∈ (germ Q s).source := successor_fields

#print axioms CartanSuppliedDifferentialSuccessor.successor_fields

example :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z), d.v = 0 → z = s.anchor := eq_anchor_of_vector_eq_zero

#print axioms CartanSuppliedDifferentialSuccessor.eq_anchor_of_vector_eq_zero

end Poincare
```

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-differential-successor-evidence/frozen-signatures.lean
```

Exit 0. Actual output from `frozen-signatures.log`:

```text
'Poincare.CartanSuppliedDifferentialSuccessor.anchor_laws' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.generic_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.vector_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.successor_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedDifferentialSuccessor.eq_anchor_of_vector_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Definition/structure comparison was also checked directly:

```sh
python3 - <<'PYCONTRACT'
from pathlib import Path
import re
source = Path('Poincare/Global/CartanSuppliedDifferentialSuccessor.lean').read_text()
task = Path('harness/tasks/supplied-differential-successor.md').read_text()
definitions = re.findall(r'```lean\n(.*?)\n```', task, re.S)[1].split('-- TARGET 6.1')[0]
assert definitions in source
print('All displayed definitions and structures match the task verbatim.')
PYCONTRACT
```

Exit 0, actual output:

```text
All displayed definitions and structures match the task verbatim.
```

## Token and whitespace checks

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
git diff --check
git diff 12a0da09cef76c99a34a9b35a6965b8eb8bb6052 --check
```

Token scan: exit 1, no matches. Both whitespace checks: exit 0, no output.
The source diff adds 208 lines in exactly one new Lean file.

Exact first review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
```

Then independently rerun the focused gate and frozen-signature probe from
this report against the recorded base and proof commits. Root integration
and acceptance belong to the orchestrator.

## Verified proof diff

Preserved from the recorded base to the verified proof head in
`/tmp/supplied-differential-successor-evidence/proof.diff`:

```diff
diff --git a/Poincare/Global/CartanSuppliedDifferentialSuccessor.lean b/Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
new file mode 100644
index 00000000..79d4bb00
--- /dev/null
+++ b/Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
@@ -0,0 +1,208 @@
+import Poincare.Global.FixedChartUniformPreferredGermAgreement
+import Poincare.Global.DifferentialInducedSuccessor
+
+/-!
+# Supplied Cartan maps and differential successor witnesses
+
+Normal charts, velocity frames, and coordinate hosts are explicit.
+The patch frame is extended by the identity outside its retained anchors;
+anchor laws only apply on the retained sets.
+-/
+
+noncomputable section
+open Filter Metric Set
+open scoped Manifold ContDiff Topology NNReal unitInterval
+namespace Poincare
+universe u
+local notation "E" => ClosedSmoothModel 3
+local notation "I" => closedSmoothModelWithCorners 3
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
+  [IsManifold I ∞ M]
+variable {g : ClosedSmoothRiemannianMetric 3 M}
+
+namespace CartanSuppliedDifferentialSuccessor
+structure Interpretation (g : ClosedSmoothRiemannianMetric 3 M) where
+  sourceAnchors : Set M
+  targetAnchors : Set RoundSphere3
+  sourceNormal : M → OpenPartialHomeomorph M E
+  targetNormal : RoundSphere3 → OpenPartialHomeomorph RoundSphere3 E
+  sourceFrame : M → E ≃L[ℝ] E
+  targetFrame : RoundSphere3 → E ≃L[ℝ] E
+  sourceHost : M → M
+  targetHost : RoundSphere3 → RoundSphere3
+  source_anchor_mem : ∀ x ∈ sourceAnchors, x ∈ (sourceNormal x).source
+  source_anchor_zero : ∀ x ∈ sourceAnchors, sourceNormal x x = 0
+  target_anchor_mem : ∀ p ∈ targetAnchors, p ∈ (targetNormal p).source
+  target_anchor_zero : ∀ p ∈ targetAnchors, targetNormal p p = 0
+
+def generic (g : ClosedSmoothRiemannianMetric 3 M) : Interpretation g where
+  sourceAnchors := univ
+  targetAnchors := univ
+  sourceNormal := (CartanSourceExponential.genericFamily g).normal
+  targetNormal := (CartanSourceExponential.genericFamily roundSphereMetric3).normal
+  sourceFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
+  targetFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
+  sourceHost := id
+  targetHost := id
+  source_anchor_mem := fun x _ => (CartanSourceExponential.genericFamily g).anchor_mem_source x
+  source_anchor_zero := fun x _ => (CartanSourceExponential.genericFamily g).normal_anchor x
+  target_anchor_mem := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).anchor_mem_source p
+  target_anchor_zero := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).normal_anchor p
+
+def patchFrame {x₀ : M} {U : Set E}
+    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) : E ≃L[ℝ] E :=
+  @dite _ (x ∈ C.anchors) (Classical.propDecidable _) (fun hx =>
+    InducedAlignment.continuousLinearEquivOfInvertible
+      (FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x)
+      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx))
+    (fun _ => ContinuousLinearEquiv.refl ℝ E)
+
+def patch {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
+    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
+    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V) :
+    Interpretation g where
+  sourceAnchors := C.anchors
+  targetAnchors := D.anchors
+  sourceNormal := C.normal
+  targetNormal := D.normal
+  sourceFrame := patchFrame C
+  targetFrame := patchFrame D
+  sourceHost := fun _ => x₀
+  targetHost := fun _ => p₀
+  source_anchor_mem := C.anchor_mem_normal_source
+  source_anchor_zero := C.normal_anchor
+  target_anchor_mem := D.anchor_mem_normal_source
+  target_anchor_zero := D.normal_anchor
+
+def linear (Q : Interpretation g) (s : CartanChain.ChainState g) : E ≃L[ℝ] E :=
+  ((Q.sourceFrame s.anchor).trans s.alignment.toContinuousLinearEquiv).trans
+    (Q.targetFrame s.target).symm
+
+def germ (Q : Interpretation g) (s : CartanChain.ChainState g) :
+    OpenPartialHomeomorph M RoundSphere3 :=
+  (Q.sourceNormal s.anchor).trans
+    ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
+      (Q.targetNormal s.target).symm)
+
+def map (Q : Interpretation g) (s : CartanChain.ChainState g) : M → RoundSphere3 :=
+  germ Q s
+
+def sourceExp (Q : Interpretation g) (x : M) : OpenPartialHomeomorph E E :=
+  (Q.sourceNormal x).symm.trans (chartAt E (Q.sourceHost x))
+
+def targetExp (Q : Interpretation g) (p : RoundSphere3) : OpenPartialHomeomorph E E :=
+  (Q.targetNormal p).symm.trans (chartAt E (Q.targetHost p))
+
+def chartMap (Q : Interpretation g) (s : CartanChain.ChainState g) : E → E :=
+  fun z => targetExp Q s.target (linear Q s ((sourceExp Q s.anchor).symm z))
+
+def chartDifferential (Q : Interpretation g) (s : CartanChain.ChainState g)
+    (A B : E ≃L[ℝ] E) : E →L[ℝ] E :=
+  ((A.symm.trans (linear Q s)).trans B : E ≃L[ℝ] E)
+
+def reanchoredChartMap (Q : Interpretation g) (s : CartanChain.ChainState g)
+    (z : M) : E → E :=
+  fun w => extChartAt I (map Q s z) (map Q s ((extChartAt I z).symm w))
+
+structure CoordinateData (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M) where
+  source_anchor_valid : s.anchor ∈ Q.sourceAnchors
+  target_anchor_valid : s.target ∈ Q.targetAnchors
+  source_mem : z ∈ (germ Q s).source
+  v : E
+  A : E ≃L[ℝ] E
+  B : E ≃L[ℝ] E
+  source_vector_mem : v ∈ (sourceExp Q s.anchor).source
+  target_vector_mem : linear Q s v ∈ (targetExp Q s.target).source
+  source_mem_oldChart : z ∈ (extChartAt I (Q.sourceHost s.anchor)).source
+  target_mem_oldChart : map Q s z ∈ (extChartAt I (Q.targetHost s.target)).source
+  source_coordinate : extChartAt I (Q.sourceHost s.anchor) z = sourceExp Q s.anchor v
+  target_coordinate : extChartAt I (Q.targetHost s.target) (map Q s z) =
+    targetExp Q s.target (linear Q s v)
+  source_exp_derivative : HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E) v
+  target_exp_derivative : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E) (linear Q s v)
+  cartan_chart_derivative : HasStrictFDerivAt (chartMap Q s)
+    (chartDifferential Q s A B) (sourceExp Q s.anchor v)
+  metric_pullback : ∀ u u' : E,
+    CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost s.target)
+      (targetExp Q s.target (linear Q s v))
+      (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
+    CovariantDerivative.chartMetric g.inner (Q.sourceHost s.anchor)
+      (sourceExp Q s.anchor v) u u'
+
+structure Data (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
+    extends CoordinateData Q s z where
+  alignment : CartanMap.TangentAlignment g z (map Q s z)
+  hasFDerivAt_reanchoredChartMap : HasFDerivAt (reanchoredChartMap Q s z)
+    (alignment.toContinuousLinearEquiv : E →L[ℝ] E) (extChartAt I z z)
+
+def Data.successor {Q : Interpretation g} {s : CartanChain.ChainState g} {z : M}
+    (d : Data Q s z) : CartanChain.ChainState g :=
+  ⟨z, map Q s z, d.alignment⟩
+
+/-- Retained anchors lie in the supplied germ source and map to the target anchor. -/
+theorem anchor_laws : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g),
+  s.anchor ∈ Q.sourceAnchors → s.target ∈ Q.targetAnchors →
+  s.anchor ∈ (germ Q s).source ∧ map Q s s.anchor = s.target := by
+  intro Q s hx hp
+  have hzero : (0 : E) ∈ (Q.targetNormal s.target).target := by
+    simpa only [Q.target_anchor_zero s.target hp] using
+      (Q.targetNormal s.target).map_source (Q.target_anchor_mem s.target hp)
+  constructor
+  · change s.anchor ∈ (Q.sourceNormal s.anchor).source ∧
+      Q.sourceNormal s.anchor s.anchor ∈
+        ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
+          (Q.targetNormal s.target).symm).source
+    refine ⟨Q.source_anchor_mem s.anchor hx, ?_⟩
+    simpa [Q.source_anchor_zero s.anchor hx] using hzero
+  · change (Q.targetNormal s.target).symm
+      (linear Q s (Q.sourceNormal s.anchor s.anchor)) = s.target
+    rw [Q.source_anchor_zero s.anchor hx, map_zero,
+      ← Q.target_anchor_zero s.target hp]
+    exact (Q.targetNormal s.target).left_inv (Q.target_anchor_mem s.target hp)
+
+/-- Identity frames and generic normals recover the old total forward map. -/
+theorem generic_map_eq : ∀ (s : CartanChain.ChainState g), map (generic g) s = s.map := by
+  intro s
+  funext z
+  change ((CartanSourceExponential.genericFamily roundSphereMetric3).normal s.target).symm
+    (s.alignment.toContinuousLinearEquiv
+      ((CartanSourceExponential.genericFamily g).normal s.anchor z)) =
+    CartanMap.cartanMap g s.anchor s.target s.alignment z
+  rw [CartanSourceExponential.genericFamily_apply, CartanMap.cartanMap_apply]
+  rfl
+
+/-- The stored host-chart coordinate identifies the actual supplied normal vector. -/
+theorem vector_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
+  (z : M) (d : Data Q s z), d.v = Q.sourceNormal s.anchor z := by
+  intro Q s z d
+  have hz : z ∈ (chartAt E (Q.sourceHost s.anchor)).source := by
+    simpa only [extChartAt_source] using d.source_mem_oldChart
+  have hc : (chartAt E (Q.sourceHost s.anchor)) z =
+      (chartAt E (Q.sourceHost s.anchor)) ((Q.sourceNormal s.anchor).symm d.v) := by
+    simpa only [extChartAt_coe] using d.source_coordinate
+  have he : z = (Q.sourceNormal s.anchor).symm d.v :=
+    (chartAt E (Q.sourceHost s.anchor)).injOn hz d.source_vector_mem.2 hc
+  calc
+    d.v = Q.sourceNormal s.anchor ((Q.sourceNormal s.anchor).symm d.v) :=
+      ((Q.sourceNormal s.anchor).right_inv d.source_vector_mem.1).symm
+    _ = Q.sourceNormal s.anchor z := congrArg (Q.sourceNormal s.anchor) he.symm
+
+/-- The successor retains its new anchor, actual target, and predecessor source evidence. -/
+theorem successor_fields : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
+  (z : M) (d : Data Q s z), d.successor.anchor = z ∧
+  d.successor.target = map Q s z ∧ z ∈ (germ Q s).source := by
+  intro Q s z d
+  exact ⟨rfl, rfl, d.source_mem⟩
+
+/-- A zero stored normal vector forces the new point to be the predecessor anchor. -/
+theorem eq_anchor_of_vector_eq_zero :
+  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
+    (d : Data Q s z), d.v = 0 → z = s.anchor := by
+  intro Q s z d hv
+  apply (Q.sourceNormal s.anchor).injOn d.source_mem.1
+    (Q.source_anchor_mem s.anchor d.source_anchor_valid)
+  rw [← vector_eq Q s z d, hv,
+    Q.source_anchor_zero s.anchor d.source_anchor_valid]
+
+end CartanSuppliedDifferentialSuccessor
+end Poincare
```
