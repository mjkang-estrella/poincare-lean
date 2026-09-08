# Fixed-chart endpoint slices completed

Date: 2026-09-08. Branch: `worker/fixed-chart-endpoint-slices`.
Base: `5f57f9b6085a0037461b703f79778e69fe638aad`.
Verified proof head: `853f4b50`.

## Result

`Poincare/Global/FixedChartEndpointSlices.lean` constructs `slice P hfst z`
with the exact requested source, target, forward function, and inverse function.
`symm_fst` derives inverse anchor preservation on `P.target` by applying `hfst`
to `P.symm q` and rewriting with `P.right_inv`. No stronger hypothesis or
per-anchor source choice is needed.

Both zero laws and all four joint-locus laws are proved. The source and target
loci are exactly `{q | q.1 ∈ A ∧ q ∈ P.source}` and
`{q | q.1 ∈ A ∧ q ∈ P.target}`. The continuity laws hold for every `A`;
only openness requires `hA`. Only the two zero laws need `[Zero E]`.
The module otherwise assumes only `[TopologicalSpace E]` and imports
`Mathlib.Topology.OpenPartialHomeomorph.Basic`.

This meets stop condition (a). It supplies the product-topology interface only.
It does not instantiate a geodesic patch, identify a preferred exponential,
or close H1, H2, or sphere recognition. Acceptance and integration remain
with the orchestrator.

The required README, HANDOFF, project map, inventory, task, and cited product
definitions/imports were inspected. The live worktree was clean at the base
above; the older base in M5-glob-69 is historical. The explicitly assigned
worker branch was retained. No existing Lean file or root import changed.

## Verification commands and actual output

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartEndpointSlices.lean
```

Exit 0, no output. Each theorem was compiled before its separate commit.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartEndpointSlices
```

Exit 0:

```text
✔ [915/915] Built Poincare.Global.FixedChartEndpointSlices (1.1s)
Build completed successfully (915 jobs).

```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartEndpointSlices.lean
git diff --check
```

Token scan: exit 1 with no matches. Diff check: exit 0 with no output.
No full build or root integration audit was launched.

### Declaration, exact-field, and named axiom probes

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-endpoint-slices-probe.lean
```

Probe source, retained here so the scratch file is reproducible:

```lean
import Poincare.Global.FixedChartEndpointSlices
open Poincare.FixedChartEndpointSlices
#check slice
#check slice_zero
#check slice_zero_mem_source
#check isOpen_slice_sourceLocus
#check isOpen_slice_targetLocus
#check continuousOn_slice_eval
#check continuousOn_slice_symmEval
#print axioms symm_fst
#print axioms slice
#print axioms slice_zero
#print axioms slice_zero_mem_source
#print axioms isOpen_slice_sourceLocus
#print axioms isOpen_slice_targetLocus
#print axioms continuousOn_slice_eval
#print axioms continuousOn_slice_symmEval
variable {E : Type*} [TopologicalSpace E]
variable (P : OpenPartialHomeomorph (E × E) (E × E))
variable (hfst : ∀ q ∈ P.source, (P q).1 = q.1) (z : E)
example : (slice P hfst z).source = {v | (z,v) ∈ P.source} := rfl
example : (slice P hfst z).target = {y | (z,y) ∈ P.target} := rfl
example : (slice P hfst z : E → E) = fun v => (P (z,v)).2 := rfl
example : ((slice P hfst z).symm : E → E) = fun y => (P.symm (z,y)).2 := rfl

```

Exit 0, actual output:

```text
Poincare.FixedChartEndpointSlices.slice.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) (z : E) :
  OpenPartialHomeomorph E E
Poincare.FixedChartEndpointSlices.slice_zero.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) [Zero E] {A : Set E}
  (hstationary : ∀ z ∈ A, ↑P (z, 0) = (z, z)) (z : E) : z ∈ A → ↑(slice P hfst z) 0 = z
Poincare.FixedChartEndpointSlices.slice_zero_mem_source.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) [Zero E] {A : Set E}
  (hzero : ∀ z ∈ A, (z, 0) ∈ P.source) (z : E) : z ∈ A → 0 ∈ (slice P hfst z).source
Poincare.FixedChartEndpointSlices.isOpen_slice_sourceLocus.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) {A : Set E} (hA : IsOpen A) :
  IsOpen {q | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).source}
Poincare.FixedChartEndpointSlices.isOpen_slice_targetLocus.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) {A : Set E} (hA : IsOpen A) :
  IsOpen {q | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).target}
Poincare.FixedChartEndpointSlices.continuousOn_slice_eval.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) (A : Set E) :
  ContinuousOn (fun q => ↑(slice P hfst q.1) q.2) {q | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).source}
Poincare.FixedChartEndpointSlices.continuousOn_slice_symmEval.{u_1} {E : Type u_1} [TopologicalSpace E]
  (P : OpenPartialHomeomorph (E × E) (E × E)) (hfst : ∀ q ∈ P.source, (↑P q).1 = q.1) (A : Set E) :
  ContinuousOn (fun q => ↑(slice P hfst q.1).symm q.2) {q | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).target}
'Poincare.FixedChartEndpointSlices.symm_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.slice_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.slice_zero_mem_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.isOpen_slice_sourceLocus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.isOpen_slice_targetLocus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.continuousOn_slice_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartEndpointSlices.continuousOn_slice_symmEval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

### Module-wide axiom scan

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-endpoint-slices-module-axioms.lean
```

```lean
import Poincare.Global.FixedChartEndpointSlices
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.FixedChartEndpointSlices).isPrefixOf n then
      count := count + 1
      let axs ← collectAxioms n
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "nonstandard dependency {a} in {n}"
  logInfo m!"Checked {count} module declarations; all dependencies permitted."

```

Exit 0:

```text
Checked 16 module declarations; all dependencies permitted.

```

### Failed compiler evidence

The first `symm_fst` attempt omitted `include hfst in`. Lean did not include
the section hypothesis because it did not occur in the stated conclusion.
The failed command was the same direct Lean command above, with output
redirected to `/tmp/fixed-chart-endpoint-slices-step1.log`. Exit 1:

```text
Poincare/Global/FixedChartEndpointSlices.lean:22:12: error(lean.unknownIdentifier): Unknown identifier `hfst`
Poincare/Global/FixedChartEndpointSlices.lean:21:26: error: unsolved goals
E : Type u_1
inst✝ : TopologicalSpace E
P : OpenPartialHomeomorph (E × E) (E × E)
q : E × E
hq : q ∈ P.target
⊢ (↑P.symm q).1 = q.1

```

Adding `include hfst in` fixed this elaboration issue. The retry and every
subsequent lemma compilation exited 0 without output. No mathematical
hypothesis changed and no later compiler attempt failed.

## Proof commits

```text
8993aea9 Prove inverse product chart preserves anchors on target
f8603fcf Construct exact vertical partial homeomorphism slices
5e83f9a5 Prove stationary zero value of each endpoint slice
11324c13 Prove endpoint slice zero-source law
99c85240 Prove endpoint slice open-source law
ae854d36 Prove endpoint slice open-target law
939c1dbe Prove endpoint slice continuous-eval law
853f4b50 Prove endpoint slice continuous-symm-eval law

```

## Final proof diff

Reproduce with `git diff 5f57f9b6 853f4b50 -- Poincare/Global/FixedChartEndpointSlices.lean`.

```diff
diff --git a/Poincare/Global/FixedChartEndpointSlices.lean b/Poincare/Global/FixedChartEndpointSlices.lean
new file mode 100644
index 00000000..d0efeef4
--- /dev/null
+++ b/Poincare/Global/FixedChartEndpointSlices.lean
@@ -0,0 +1,105 @@
+import Mathlib.Topology.OpenPartialHomeomorph.Basic
+
+/-!
+# Exact slices of an anchor-preserving product chart
+
+A product partial homeomorphism preserving the first coordinate on its source
+restricts to a partial homeomorphism at each anchor. Its inverse preserves the
+first coordinate on the target as a consequence of the inverse law.
+-/
+
+namespace Poincare.FixedChartEndpointSlices
+
+open Set
+
+variable {E : Type*} [TopologicalSpace E]
+variable (P : OpenPartialHomeomorph (E × E) (E × E))
+variable (hfst : ∀ q ∈ P.source, (P q).1 = q.1)
+
+include hfst in
+/-- The inverse preserves anchors on the exact product target. -/
+theorem symm_fst {q : E × E} (hq : q ∈ P.target) :
+    (P.symm q).1 = q.1 := by
+  have h := hfst (P.symm q) (P.map_target hq)
+  rw [P.right_inv hq] at h
+  exact h.symm
+
+/-- Restriction to an anchor, retaining the exact vertical source and target. -/
+def slice (z : E) : OpenPartialHomeomorph E E where
+  toFun v := (P (z, v)).2
+  invFun y := (P.symm (z, y)).2
+  source := {v | (z, v) ∈ P.source}
+  target := {y | (z, y) ∈ P.target}
+  map_source' := by
+    intro v hv
+    have heq : (z, (P (z, v)).2) = P (z, v) :=
+      Prod.ext (hfst (z, v) hv).symm rfl
+    change (z, (P (z, v)).2) ∈ P.target
+    rw [heq]
+    exact P.map_source hv
+  map_target' := by
+    intro y hy
+    have heq : (z, (P.symm (z, y)).2) = P.symm (z, y) :=
+      Prod.ext (symm_fst P hfst hy).symm rfl
+    change (z, (P.symm (z, y)).2) ∈ P.source
+    rw [heq]
+    exact P.map_target hy
+  left_inv' := by
+    intro v hv
+    have heq : (z, (P (z, v)).2) = P (z, v) :=
+      Prod.ext (hfst (z, v) hv).symm rfl
+    change (P.symm (z, (P (z, v)).2)).2 = v
+    rw [heq, P.left_inv hv]
+  right_inv' := by
+    intro y hy
+    have heq : (z, (P.symm (z, y)).2) = P.symm (z, y) :=
+      Prod.ext (symm_fst P hfst hy).symm rfl
+    change (P (z, (P.symm (z, y)).2)).2 = y
+    rw [heq, P.right_inv hy]
+  open_source := P.open_source.preimage (continuous_const.prodMk continuous_id)
+  open_target := P.open_target.preimage (continuous_const.prodMk continuous_id)
+  continuousOn_toFun :=
+    (P.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
+      (fun _ hv => hv)).snd
+  continuousOn_invFun :=
+    (P.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
+      (fun _ hy => hy)).snd
+
+/-- The stationary product zero section gives the slice's anchor value. -/
+theorem slice_zero [Zero E] {A : Set E}
+    (hstationary : ∀ z ∈ A, P (z, 0) = (z, z)) :
+    ∀ z ∈ A, slice P hfst z 0 = z := by
+  intro z hz
+  exact congrArg Prod.snd (hstationary z hz)
+
+/-- The supplied zero section lies in the exact slice source. -/
+theorem slice_zero_mem_source [Zero E] {A : Set E}
+    (hzero : ∀ z ∈ A, (z, (0 : E)) ∈ P.source) :
+    ∀ z ∈ A, 0 ∈ (slice P hfst z).source := by
+  exact hzero
+
+/-- The joint source over an open anchor set is open. -/
+theorem isOpen_slice_sourceLocus {A : Set E} (hA : IsOpen A) :
+    IsOpen {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).source} := by
+  change IsOpen (Prod.fst ⁻¹' A ∩ P.source)
+  exact (hA.preimage continuous_fst).inter P.open_source
+
+/-- The joint target over an open anchor set is open. -/
+theorem isOpen_slice_targetLocus {A : Set E} (hA : IsOpen A) :
+    IsOpen {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).target} := by
+  change IsOpen (Prod.fst ⁻¹' A ∩ P.target)
+  exact (hA.preimage continuous_fst).inter P.open_target
+
+/-- Forward evaluation is jointly continuous on the exact restricted source. -/
+theorem continuousOn_slice_eval (A : Set E) :
+    ContinuousOn (fun q : E × E => slice P hfst q.1 q.2)
+      {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).source} := by
+  exact P.continuousOn.snd.mono (fun _ hq => hq.2)
+
+/-- Inverse evaluation is jointly continuous on the exact restricted target. -/
+theorem continuousOn_slice_symmEval (A : Set E) :
+    ContinuousOn (fun q : E × E => (slice P hfst q.1).symm q.2)
+      {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).target} := by
+  exact P.continuousOn_symm.snd.mono (fun _ hq => hq.2)
+
+end Poincare.FixedChartEndpointSlices

```

## Handoff

First independent review command:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartEndpointSlices`.
Then replay the retained declaration and module-wide axiom probes. The next
mathematical task is task 4, `FixedChartUniformSourceNormal`, using these exact
slices on the supplied product inverse.
