# Supplied source germ transfer worker result

Date: 2026-09-08. Branch: `worker/supplied-source-germ-transfer`.
Base: `ae6ce9f49e8de8a07d1cc3fc061c7bd8ba4750d2`.
Verified proof head: `7a8ba3ae`.

All three frozen targets are proved in `Poincare/Global/CartanSuppliedSourceGermTransfer.lean`, namespace `Poincare.CartanSuppliedSourceGermTransfer`. The only import is the landed task-1 module `Poincare.Global.CartanSuppliedSourceMap`.

The forward comparison composes the supplied normal-coordinate agreement with the target map. For the inverse comparison, zero belongs to the first normal chart's target by its anchor law. Its inverse tends to the source anchor. Pulling back the forward agreement and the second chart's open source gives a neighborhood where the first chart's right inverse law and the second chart's left inverse law apply. The final theorem extracts an open neighborhood from the intersection of both germ sources and their agreement set. No additional neighborhood hypothesis or equality of total inverses is used.

Exactly one new Lean file is added. Existing Lean files and `Poincare.lean` are unchanged. This report and a dated `HANDOFF.md` entry record the worker result. The assigned isolated worker branch is retained. The result awaits independent orchestrator review; no merge or task acceptance is recorded. No H1, H2, global development, or recognition theorem is claimed.

## Proof commits

Each commit followed a successful direct Lean check of the cumulative file.

- `3118ab89`: forward Cartan germ agreement.
- `9d00daa0`: inverse normal germ agreement.
- `7a8ba3ae`: open common source agreement.

## Direct compilation and failed attempt

The following command was run after each lemma:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceGermTransfer.lean
```
Step 1 exited 0 with empty output, recorded in `/tmp/supplied-source-germ-transfer-step1.log`. The first step-2 attempt exited 1 with this exact output:

```text
Poincare/Global/CartanSuppliedSourceGermTransfer.lean:54:4: error: Type mismatch: After simplification, term
  OpenPartialHomeomorph.continuousAt_symm (S.normal x) hzero
 has type
  ContinuousAt (↑(S.normal x).symm) 0
but is expected to have type
  Tendsto (↑(S.normal x).symm) (𝓝 0) (𝓝 x)
```
The repair explicitly applies `.tendsto` to the continuity proof before rewriting the inverse's value at zero. The retry exited 0 with empty output in `/tmp/supplied-source-germ-transfer-step2-retry.log`. Step 3 exited 0 with empty output in `/tmp/supplied-source-germ-transfer-step3.log`. The statements were unchanged.

## Focused build and module-wide gate

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/supplied-source-germ-transfer Poincare.Global.CartanSuppliedSourceGermTransfer Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement
```

Exit 0. Exact output from `/tmp/supplied-source-germ-transfer-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/CartanSuppliedSourceGermTransfer.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.CartanSuppliedSourceGermTransfer ===
  omit [ChartedSpace E M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3359/3359] Built Poincare.Global.CartanSuppliedSourceGermTransfer (2.2s)
Build completed successfully (3359 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=3 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```
The gate invokes `lake build Poincare.Global.CartanSuppliedSourceGermTransfer` and scans every declaration owned by that module. All three named theorem closures are exactly `[propext, Classical.choice, Quot.sound]`. Only this focused worker build was launched; integration gates remain for the orchestrator.

## Exact declaration probes

`/tmp/supplied-source-germ-transfer-probe.lean` contains:

```lean
import Poincare.Global.CartanSuppliedSourceGermTransfer
#check Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq
#check Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq
#check Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement
#print axioms Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq
#print axioms Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq
#print axioms Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement
```

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-source-germ-transfer-probe.lean
```

Exit 0. Exact output:

```text
Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} (S S' : Poincare.CartanSourceExponential.Family g)
  (F : Poincare.CartanTargetExponential.Family) (x : M) (p : Poincare.RoundSphere3)
  (K : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) (h : ↑(S.normal x) =ᶠ[nhds x] ↑(S'.normal x)) :
  ↑(Poincare.CartanSuppliedSourceMap.germ S F x p K) =ᶠ[nhds x] ↑(Poincare.CartanSuppliedSourceMap.germ S' F x p K)
Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq.{u} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] {g : Poincare.ClosedSmoothRiemannianMetric 3 M}
  (S S' : Poincare.CartanSourceExponential.Family g) (x : M) (h : ↑(S.normal x) =ᶠ[nhds x] ↑(S'.normal x)) :
  ↑(S.normal x).symm =ᶠ[nhds 0] ↑(S'.normal x).symm
Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric 3 M} (S S' : Poincare.CartanSourceExponential.Family g)
  (F : Poincare.CartanTargetExponential.Family) (x : M) (p : Poincare.RoundSphere3)
  (K : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) (h : ↑(S.normal x) =ᶠ[nhds x] ↑(S'.normal x)) :
  ∃ V,
    IsOpen V ∧
      x ∈ V ∧
        V ⊆
            (Poincare.CartanSuppliedSourceMap.germ S F x p K).source ∩
              (Poincare.CartanSuppliedSourceMap.germ S' F x p K).source ∧
          Set.EqOn (↑(Poincare.CartanSuppliedSourceMap.germ S F x p K))
            (↑(Poincare.CartanSuppliedSourceMap.germ S' F x p K)) V
'Poincare.CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSourceGermTransfer.normal_symm_eventuallyEq_of_normal_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedSourceGermTransfer.exists_open_common_source_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedSourceGermTransfer.lean
git diff --check
```
The token scan exited 1 with empty output, meaning no matches. The diff check exited 0 with empty output.

Toolchain from `lake env lean --version`:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

## Verified proof diff

```diff
diff --git a/Poincare/Global/CartanSuppliedSourceGermTransfer.lean b/Poincare/Global/CartanSuppliedSourceGermTransfer.lean
new file mode 100644
index 00000000..2cb0dac8
--- /dev/null
+++ b/Poincare/Global/CartanSuppliedSourceGermTransfer.lean
@@ -0,0 +1,89 @@
+import Poincare.Global.CartanSuppliedSourceMap
+
+/-!
+# Neighborhood transport for supplied source Cartan germs
+
+Agreement of supplied normal coordinates near an anchor transfers to the
+Cartan maps and to the inverse normal coordinates near zero. The inverse
+comparison uses the partial inverse laws only on their open domains.
+-/
+
+noncomputable section
+
+open Filter Set
+open scoped Manifold ContDiff Topology
+
+namespace Poincare
+namespace CartanSuppliedSourceGermTransfer
+
+universe u
+
+local notation "E" => ClosedSmoothModel 3
+local notation "I" => closedSmoothModelWithCorners 3
+
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
+variable [IsManifold I ∞ M]
+variable {g : ClosedSmoothRiemannianMetric 3 M}
+
+/-- Normal-coordinate agreement near the anchor gives Cartan germ agreement. -/
+theorem germ_eventuallyEq_of_normal_eventuallyEq
+    (S S' : CartanSourceExponential.Family g)
+    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
+    (K : E ≃L[ℝ] E)
+    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
+    (CartanSuppliedSourceMap.germ S F x p K : M → RoundSphere3)
+      =ᶠ[𝓝 x]
+    (CartanSuppliedSourceMap.germ S' F x p K : M → RoundSphere3) := by
+  rw [CartanSuppliedSourceMap.germ_apply, CartanSuppliedSourceMap.germ_apply]
+  filter_upwards [h] with z hz
+  rw [hz]
+
+/-- Inverse normal coordinates agree near zero by the local inverse laws. -/
+theorem normal_symm_eventuallyEq_of_normal_eventuallyEq
+    (S S' : CartanSourceExponential.Family g) (x : M)
+    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
+    ((S.normal x).symm : E → M) =ᶠ[𝓝 (0 : E)]
+      ((S'.normal x).symm : E → M) := by
+  have hzero : (0 : E) ∈ (S.normal x).target := by
+    simpa only [S.normal_anchor] using
+      (S.normal x).map_source (S.anchor_mem_source x)
+  have hinvzero : (S.normal x).symm (0 : E) = x := by
+    simpa only [S.normal_anchor] using
+      (S.normal x).left_inv (S.anchor_mem_source x)
+  have htendsto : Tendsto (S.normal x).symm (𝓝 (0 : E)) (𝓝 x) := by
+    simpa only [hinvzero] using (S.normal x).continuousAt_symm hzero |>.tendsto
+  have hsource : ∀ᶠ v in 𝓝 (0 : E),
+      (S.normal x).symm v ∈ (S'.normal x).source :=
+    htendsto ((S'.normal x).open_source.mem_nhds (S'.anchor_mem_source x))
+  filter_upwards [htendsto h, hsource,
+    (S.normal x).open_target.mem_nhds hzero] with v hv hvs hvt
+  have heq : S'.normal x ((S.normal x).symm v) = v :=
+    hv.symm.trans ((S.normal x).right_inv hvt)
+  calc
+    (S.normal x).symm v =
+        (S'.normal x).symm (S'.normal x ((S.normal x).symm v)) :=
+      ((S'.normal x).left_inv hvs).symm
+    _ = (S'.normal x).symm v := congrArg (S'.normal x).symm heq
+
+/-- The agreeing Cartan germs share an open source neighborhood of the anchor. -/
+theorem exists_open_common_source_agreement
+    (S S' : CartanSourceExponential.Family g)
+    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
+    (K : E ≃L[ℝ] E)
+    (h : (S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E)) :
+    ∃ V, IsOpen V ∧ x ∈ V ∧
+      V ⊆ (CartanSuppliedSourceMap.germ S F x p K).source ∩
+        (CartanSuppliedSourceMap.germ S' F x p K).source ∧
+      EqOn (CartanSuppliedSourceMap.germ S F x p K)
+        (CartanSuppliedSourceMap.germ S' F x p K) V := by
+  have hagree := germ_eventuallyEq_of_normal_eventuallyEq S S' F x p K h
+  have hsource := (CartanSuppliedSourceMap.germ S F x p K).open_source.mem_nhds
+    (CartanSuppliedSourceMap.anchor_mem_source S F x p K)
+  have hsource' := (CartanSuppliedSourceMap.germ S' F x p K).open_source.mem_nhds
+    (CartanSuppliedSourceMap.anchor_mem_source S' F x p K)
+  rcases mem_nhds_iff.mp (inter_mem (inter_mem hsource hsource') hagree) with
+    ⟨V, hV, hVopen, hxV⟩
+  exact ⟨V, hVopen, hxV, fun z hz => (hV hz).1, fun z hz => (hV hz).2⟩
+
+end CartanSuppliedSourceGermTransfer
+end Poincare
```

## Exact first review action

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceGermTransfer.lean
```
