Worker result: done for the frozen class-B contract, pending independent orchestrator review.

Dated handoff: 2026-09-11. Branch `worker/heat-duhamel-hessian-spatial-holder`.
Base: `3bdabbc9806d413b0f71c939d8d0e1a96394c6c5`. Verified proof head: `286176d325b9188d0134e0975fd220c1fcd8506f`.

`Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder`
proves the exact task proposition. It bounds the difference of the actual
second Frechet derivatives of the Duhamel integral, for every time in the
closed cylinder, with the constant chosen before the time horizon and forcing.
The final frozen-type assignment was copied from the read-only task file and
compiled without changing its quantifiers.

The module contains 23 theorems and three local instances. Each theorem was
compiled before its individual commit. The third-moment bound is committed at
`da860692`, the near bound at `29413c17`, the far Duhamel bound at `4252f63e`,
and the exact assembly at `940c92f6`. A final cleanup at `286176d3` removes
compiler diagnostics and restores the default elaboration limit.

The only new Lean file is `Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.
The report is the only other added file. Existing Lean files, `Poincare.lean`,
and the frozen task/context files are unchanged. The scoped worker contract
forbids editing existing files, so the dated handoff and next action are
recorded here instead of changing `HANDOFF.md`.

Write `JHα = ∫ ‖D²K₁(y)‖ ‖y‖^α`, `J3α = ∫ ‖D³K₁(y)‖ ‖y‖^α`,
and `J30 = ∫ ‖D³K₁(y)‖`. The constructed constant is
`max 1 (2 * JHα * (2 / α) + (J3α + J30) * (2 / (1 - α)))`.
All three moments have proved integrability. The third derivative is the
actual derivative of the existing kernel Hessian; its formula, cubic Gaussian
envelope, dilation, and exact moment scaling are proved in the new module.

The near estimate uses the existing cancelled Hessian time majorant on a
translated terminal interval. The far estimate first identifies both heat
Hessians with integrals using one cancellation constant. For data expressed
as `f(x - y)`, the second kernel is `Hess t (y + (z - x))`. This corrects the
sign in the suggested route; the distance is unchanged. The proof integrates
the actual third derivative along the segment, proves weighted translation
integrability and product integrability, and applies Fubini. When
`‖x-z‖² ≤ t-s`, both resulting terms scale as `(t-s)^(α/2-3/2)`.
The far time integral supplies `2/(1-α)`. The assembly handles the diagonal,
the all-near case, and the genuine near/far split explicitly.

This result proves the spatial increment task. It does not assert temporal
Hölder control, the rest of L3, or a completed Poincare proof. No worker merge
or task-acceptance action was performed.

Final acceptance results:

| Check | Actual result |
| --- | --- |
| `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean` | Exit 0, empty output, probe 048 |
| Frozen proposition assigned the exact new theorem | Exit 0, empty output, probe 050 |
| `#print axioms` for all 23 theorems and three instances | Exactly `[propext, Classical.choice, Quot.sound]`, probe 049 |
| Declaration-wide dependency assertion | `EXACT_DEPENDENCY_SCAN declarations=26 PASS`, probe 049 |
| Forbidden-token grep | Exit 1, empty output, meaning no matches |
| `git diff --check` and base-to-proof diff check | Exit 0, empty output |

First action for independent review:

```sh
git diff 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..286176d325b9188d0134e0975fd220c1fcd8506f -- Poincare/Global/HeatDuhamelHessianSpatialHolder.lean
```

Then rerun the focused gate and exact-target/dependency probes preserved
below. Root integration and its broader audits remain the orchestrator's
responsibility.

Proof file SHA-256: `3b1aa2514864497435d45872b80565895b6d0406ca3d29bc440c4f032b759561`.

The following evidence records all 50 Lean probes, including failed
attempts. Sources are preserved as a first full snapshot followed by exact
unified changes from the preceding numbered snapshot. Applying those changes
in order reconstructs every probe input, including the final probe payloads.
Compiler output is preserved. In all evidence blocks, trailing spaces are
encoded as literal `\u0020` and trailing tabs as `\u0009`. Decode those
sequences before applying source patches or reconstructing output. This
preserves the evidence while keeping the report free of trailing whitespace. Early failed attempts include an unavailable
optional Mathlib object; the final proof instead uses the already imported
fundamental theorem of calculus. No optional object build or root build was
needed.

<details>
<summary>Final command output and commit sequence</summary>

Command: `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`. Exit 1.

```text
```

Command: `git diff --check`. Exit 0.

```text
```

Command: `git diff 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5 --check`. Exit 0.

```text
```

Command: `git status --short --branch`. Exit 0.

```text
## worker/heat-duhamel-hessian-spatial-holder
```

Command: `git rev-parse HEAD`. Exit 0.

```text
286176d325b9188d0134e0975fd220c1fcd8506f
```

Command: `git log --reverse '--format=%h %s' 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..HEAD`. Exit 0.

```text
e0361044 Prove the explicit third spatial heat kernel derivative
a005c938 Bound the third heat derivative by a cubic Gaussian envelope
0bf658f0 Prove unit-time weighted third derivative integrability
d6387c8f Prove parabolic dilation of the third heat derivative
bace9a6f Scale the radially weighted third heat derivative
f37e47c8 Compute the weighted third derivative integral under dilation
4fdfff38 Prove positive-time weighted third derivative integrability
3b70ea13 Compute the exact third derivative moment time exponent
da860692 Prove the weighted third heat kernel moment bound
84923de2 Bound the cancelled Hessian on arbitrary terminal time intervals
29413c17 Prove the near-time spatial Hessian Holder increment estimate
9542e81f Prove the actual Duhamel Hessian estimate at large spatial separation
cf666d4f Bound the far-time singular power integral with the sharp spatial exponent
ee35457a Put both Hessian observation points over a common cancellation constant
964e2072 Identify the cancelled kernel translation formula for Hessian increments
1087ba2a Control Hessian kernel translations by a segment integral of the third derivative
fdc0f473 Control weighted third derivative moments under spatial translation
562da1e2 Prove joint integrability of the segment and weighted third derivative
3c8f838f Prove the weighted Hessian kernel translation estimate by Fubini
b2ad1243 Derive the far-scale weighted Hessian kernel bound
6821c905 Bound far-scale heat Hessian increments for spatial Holder forcing
4252f63e Prove the far-time Duhamel Hessian spatial Holder bound
940c92f6 Prove the frozen Duhamel Hessian spatial Holder theorem
286176d3 Keep the spatial Holder proof within default elaboration limits
```

Command: `git diff 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5 --stat`. Exit 0.

```text
 .../Global/HeatDuhamelHessianSpatialHolder.lean    | 715 +++++++++++++++++++++
 1 file changed, 715 insertions(+)
```

</details>

<details>
<summary>Final proof diff against the recorded base</summary>

```diff
diff --git a/Poincare/Global/HeatDuhamelHessianSpatialHolder.lean b/Poincare/Global/HeatDuhamelHessianSpatialHolder.lean
new file mode 100644
index 00000000..47ce5517
--- /dev/null
+++ b/Poincare/Global/HeatDuhamelHessianSpatialHolder.lean
@@ -0,0 +1,715 @@
+import Poincare.Global.HeatDuhamelHessianDifferentiation
+import Mathlib.Analysis.MeanInequalitiesPow
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology InnerProductSpace Interval
+
+namespace Poincare.HeatDuhamelHessianSpatialHolder
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+local notation "Third" => fun (t : ℝ) (x : E) => fderiv ℝ (Hess t) x
+
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+  HeatDuhamelHessianDifferentiation
+
+/-- The third derivative of the Gaussian, evaluated in three directions. -/
+theorem third_apply {t : ℝ} (ht : t ≠ 0) (x u v w : E) :
+    Third t x u v w = heatKernel t x *
+      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
+        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
+          ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2)) := by
+  have hH : ContDiff ℝ 1 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
+  have hd := (((hH.differentiable (by norm_num) x).hasFDerivAt.clm_apply
+    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x))
+  have he : (fun z : E => Hess t z v w) = fun z : E => heatKernel t z *
+      (⟪v, z⟫_ℝ * ⟪w, z⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
+    funext z
+    simpa only [iteratedFDeriv_two_apply, real_inner_comm] using
+      iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht z v w
+  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
+  have hw := (innerSL ℝ w).hasFDerivAt (x := x)
+  have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
+    (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
+  rw [he] at hd
+  simp only [Pi.mul_apply, innerSL_apply_apply, div_eq_mul_inv] at hp hd
+  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp)
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
+    ContinuousLinearMap.zero_apply, map_zero, zero_add, smul_eq_mul,
+    innerSL_apply_apply] at h
+  rw [h]
+  simp only [heatKernel, real_inner_comm]
+  ring_nf
+
+/-- The unit-time third derivative has a cubic Gaussian envelope. -/
+theorem norm_third_one_le (x : E) :
+    ‖Third 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by
+  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
+  have hB : 0 ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by positivity
+  apply ContinuousLinearMap.opNorm_le_bound _ hB
+  intro u
+  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg u))
+  intro v
+  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+  intro w
+  rw [third_apply one_ne_zero]
+  norm_num only [one_pow, mul_one]
+  rw [norm_mul, Real.norm_of_nonneg hk]
+  calc
+    _ ≤ heatKernel 1 x *
+        (‖⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ‖ / 8 +
+          ((‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ‖ + ‖⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖) +
+            ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖) / 4) := by
+      gcongr
+      calc
+        _ ≤ ‖-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / 8‖ +
+            ‖(⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
+              ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / 4‖ := norm_add_le _ _
+        _ ≤ _ := by
+          simp only [norm_div, norm_neg, Real.norm_ofNat]
+          gcongr
+          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
+    _ ≤ heatKernel 1 x *
+        (((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) / 8 +
+          (((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖)) +
+            (‖x‖ * ‖u‖) * (‖v‖ * ‖w‖)) / 4) := by
+      simp only [norm_mul]
+      gcongr <;> apply norm_inner_le_norm
+    _ = _ := by ring
+
+/-- The weighted third derivative is integrable at unit time. -/
+theorem integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
+    Integrable (fun x : E => ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
+  have hc : 0 ≤ c := by dsimp [c]; positivity
+  have hweight : Continuous (fun x : E => ‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))) :=
+    ((Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).comp continuous_norm).mul
+      (((continuous_norm.pow 2).div_const 8).neg.rexp)
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
+      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+      hweight.aestronglyMeasurable
+      (Filter.Eventually.of_forall fun x => show
+        ‖‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
+          rw [Real.norm_of_nonneg (by positivity)]
+          exact rpow_mul_gaussian_le_eight (by linarith) (by linarith) (norm_nonneg x))
+  have hcont : ContDiff ℝ 0 (Third 1) :=
+    (((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)
+  refine (hbound.const_mul c).mono'
+    (hcont.continuous.norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
+  refine Filter.Eventually.of_forall fun x => ?_
+  rw [Real.norm_of_nonneg (by positivity)]
+  have hK : heatKernel (1 : ℝ) x =
+      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
+    rw [← Real.exp_add]
+    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
+      Nat.cast_ofNat, mul_one]
+    congr 1
+    congr 1
+    ring
+  have hw : ‖x‖ ^ (α + 1) = ‖x‖ ^ α * ‖x‖ :=
+    Real.rpow_add_one' (norm_nonneg x) (by linarith)
+  calc
+    ‖Third 1 x‖ * ‖x‖ ^ α ≤
+        (heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)) * ‖x‖ ^ α :=
+      mul_le_mul_of_nonneg_right (norm_third_one_le x) (Real.rpow_nonneg (norm_nonneg x) α)
+    _ ≤ (heatKernel 1 x * (‖x‖ * (1 + ‖x‖ ^ 2))) * ‖x‖ ^ α := by
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
+      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
+      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg x) 3]
+    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
+        (‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK, hw]; ring
+
+/-- Parabolic dilation of the full third spatial derivative. -/
+theorem third_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    Third (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹) • Third 1 x := by
+  ext u v w
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
+  rw [third_apply (pow_ne_zero _ ha.ne'), third_apply one_ne_zero,
+    heatKernel_sq_smul a ha x]
+  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
+  field_simp
+
+/-- Pointwise parabolic dilation including the radial weight. -/
+theorem weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
+    ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
+      ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (‖Third 1 x‖ * ‖x‖ ^ α) := by
+  rw [third_sq_smul a ha x,
+    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 3)⁻¹ by positivity) (Third 1 x),
+    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
+  ring
+
+/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
+theorem weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
+    (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
+      ((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Third (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
+        ∫ x : E, ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+      simp_rw [weighted_third_sq_smul a ha]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α)) := by ring
+
+/-- Weighted Bochner integrability at every positive time. -/
+theorem integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) := by
+  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
+  rw [← Real.sq_sqrt ht.le]
+  apply (integrable_comp_smul_iff volume _ ha.ne').1
+  simp_rw [weighted_third_sq_smul (Real.sqrt t) ha]
+  exact (integrable_weighted_third_one hα hα1).const_mul _
+
+/-- Exact scaling of the third spatial derivative moment. -/
+theorem weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
+    (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) =
+      t ^ (α / 2 - 3 / 2) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  have h := weighted_third_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h]
+  congr 1
+  have hp : (Real.sqrt t) ^ 3 = t ^ ((3 : ℝ) / 2) := by
+    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
+    congr 1
+    norm_num
+  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht]
+  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
+  ring
+
+/-- The third Gaussian moment has a positive constant independent of time. -/
+theorem third_moment_bound :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
+      Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) ∧
+      (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 3 / 2) := by
+  intro α hα hα1
+  refine ⟨max 1 (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t ht
+  refine ⟨integrable_weighted_third hα.le hα1.le ht, ?_⟩
+  rw [weighted_third_integral ht, mul_comm (t ^ (α / 2 - 3 / 2))]
+  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
+
+/-- The near-time cancelled integral is bounded by the length of its time interval. -/
+theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hat : a ≤ t) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (t - a) ^ (α / 2) := by
+  have hb := norm_integral_cancelled_hessian_time_le hα hα1 (sub_nonneg.mpr hat)
+    (f := fun p => f (p.1 + a, p.2))
+    (fun s hs => hK (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩) x
+  have he := intervalIntegral.integral_comp_add_right
+    (a := (0 : ℝ)) (b := t - a)
+    (fun s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) a
+  simp only [zero_add, sub_add_cancel] at he
+  have htau (s : ℝ) : t - a - s = t - (s + a) := by ring
+  simp only [htau] at hb
+  rw [he] at hb
+  exact hb
+
+/-- The near part of the spatial increment has the required Hölder power. -/
+theorem near_hessian_difference_le {α K a t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
+    {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : t - a ≤ ‖x - z‖ ^ 2) :
+    ‖(∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
+      (∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
+      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
+  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
+  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
+  have hp : (t - a) ^ (α / 2) ≤ ‖x - z‖ ^ α := by
+    calc
+      (t - a) ^ (α / 2) ≤ (‖x - z‖ ^ 2) ^ (α / 2) :=
+        Real.rpow_le_rpow (sub_nonneg.mpr hat) hscale (by linarith)
+      _ = ‖x - z‖ ^ α := by
+        rw [← Real.rpow_natCast_mul (norm_nonneg (x - z))]
+        congr 1
+        norm_num
+        ring
+  calc
+    _ ≤ ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ +
+        ‖∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y‖ :=
+      norm_sub_le _ _
+    _ ≤ (K * J) * (2 / α) * (t - a) ^ (α / 2) +
+        (K * J) * (2 / α) * (t - a) ^ (α / 2) :=
+      add_le_add (norm_integral_cancelled_hessian_near_le hα hα1 hat hK x)
+        (norm_integral_cancelled_hessian_near_le hα hα1 hat hK z)
+    _ = (2 * J * (2 / α)) * K * (t - a) ^ (α / 2) := by ring
+    _ ≤ (2 * J * (2 / α)) * K * ‖x - z‖ ^ α :=
+      mul_le_mul_of_nonneg_left hp
+        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ)
+          (div_nonneg (by norm_num) hα.le)) hK0)
+
+/-- The spatial Hölder estimate for the actual Duhamel Hessian when the near interval is all of time. -/
+theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : t ≤ ‖x - z‖ ^ 2) :
+    let u : E → ℝ := fun x => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x
+    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
+      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
+  dsimp only
+  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
+    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
+  exact near_hessian_difference_le hα hα1 hK0 ht.1
+    (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x z (by simpa using hscale)
+
+/-- The far-time power integral supplies the factor two over one minus the exponent. -/
+theorem far_time_power_integral_le {α ρ t : ℝ}
+    (hα1 : α < 1) (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ t) :
+    ρ * (∫ s in (0 : ℝ)..(t - ρ ^ 2), (t - s) ^ (α / 2 - 3 / 2)) ≤
+      (2 / (1 - α)) * ρ ^ α := by
+  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
+  have hq : α / 2 - 3 / 2 + 1 < 0 := by linarith
+  rw [intervalIntegral.integral_comp_sub_left
+    (fun r : ℝ => r ^ (α / 2 - 3 / 2)) t, sub_sub_cancel, sub_zero]
+  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
+  · calc
+      ρ * ((t ^ (α / 2 - 3 / 2 + 1) - (ρ ^ 2) ^ (α / 2 - 3 / 2 + 1)) /
+          (α / 2 - 3 / 2 + 1)) ≤
+          ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
+        apply mul_le_mul_of_nonneg_left _ hρ.le
+        simp only [div_eq_mul_inv]
+        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
+        have hnn := Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)
+        simp only [div_eq_mul_inv] at hnn
+        linarith only [hnn]
+      _ = (2 / (1 - α)) * ρ ^ α := by
+        rw [← Real.rpow_natCast_mul hρ.le]
+        simp only [Nat.cast_ofNat]
+        rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
+        rw [Real.rpow_sub hρ, Real.rpow_one]
+        have hden : 1 - α ≠ 0 := by linarith
+        have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
+        field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
+        ring_nf
+        all_goals
+          have hi := mul_inv_cancel₀ (show -1 + α ≠ 0 by linarith)
+          nlinarith only [hi]
+  · rw [uIcc_of_le ht]
+    intro hz
+    exact (not_le.mpr hρ2) hz.1
+
+/-- Both observation points can use the same cancellation constant. -/
+theorem hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
+      ∫ y : E, (f (x - y) - f x) • Hess t (y + (z - x)) := by
+  have hi : Integrable (fun y : E => f y • Hess t (z - y)) :=
+    integrable_data_smul_hessian_sub ht hf hM z
+  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
+    ((integrable_hessian ht).comp_sub_left z).smul (f x)
+  have hz : (∫ y : E, Hess t (z - y)) = 0 := by
+    rw [integral_sub_left_eq_self, integral_hessian_eq_zero ht]
+  have he : (∫ y : E, (f y - f x) • Hess t (z - y)) =
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z := by
+    simp_rw [sub_smul]
+    rw [integral_sub hi hc, integral_smul, hz, smul_zero, sub_zero,
+      hessian_heatSolution_eq_integral ht hf hM]
+  rw [← he]
+  have hchange := integral_sub_left_eq_self
+    (fun y : E => (f y - f x) • Hess t (z - y)) volume x
+  have halg (y : E) : z - (x - y) = y + (z - x) := by abel
+  simpa only [halg] using hchange.symm
+
+/-- The Hessian increment is the cancelled integral of a kernel translation difference. -/
+theorem hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
+      ∫ y : E, (f (x - y) - f x) • (Hess t y - Hess t (y + (z - x))) := by
+  have hi := integrable_data_smul_hessian_sub ht hf hM z
+  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
+    ((integrable_hessian ht).comp_sub_left z).smul (f x)
+  have hij : Integrable (fun y : E => (f (x - y) - f x) • Hess t (y + (z - x))) := by
+    have h := (hi.sub hc).comp_sub_left x
+    have halg (y : E) : z - (x - y) = y + (z - x) := by abel
+    simpa only [Pi.sub_apply, halg, ← sub_smul] using h
+  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM x,
+    hessian_heatSolution_eq_common_cancelled_integral ht hf hM x z]
+  simp_rw [smul_sub]
+  rw [integral_sub (integrable_cancelled_hessian ht hf hM x) hij]
+
+/-- A translated Hessian difference is bounded by the third derivative along its segment. -/
+theorem norm_hessian_translation_le (t : ℝ) (y w : E) :
+    ‖Hess t (y + w) - Hess t y‖ ≤
+      ∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖ := by
+  have hH : ContDiff ℝ 1 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
+  have hD : Continuous (Third t) := (hH.fderiv_right (m := 0) (by norm_num)).continuous
+  have hline (r : ℝ) : HasDerivAt (fun q : ℝ => y + q • w) w r := by
+    simpa only [one_smul] using ((hasDerivAt_id r).smul_const w).const_add y
+  have hd (r : ℝ) : HasDerivAt (fun q : ℝ => Hess t (y + q • w))
+      (Third t (y + r • w) w) r :=
+    ((hH.differentiable (by norm_num) (y + r • w)).hasFDerivAt).comp_hasDerivAt r (hline r)
+  have hbound : Continuous (fun r : ℝ => ‖Third t (y + r • w)‖ * ‖w‖) :=
+    (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.mul continuous_const
+  have hi : IntervalIntegrable (fun r : ℝ => Third t (y + r • w) w) volume 0 1 :=
+    ((hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
+      continuous_const).intervalIntegrable 0 1
+  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
+    (fun r _ => hd r) hi
+  simp only [one_smul, zero_smul, add_zero] at he
+  rw [← he]
+  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
+    (Filter.Eventually.of_forall fun r _ => ContinuousLinearMap.le_opNorm _ _)
+    (hbound.intervalIntegrable 0 1)
+
+/-- Translating the third derivative costs one unweighted moment in addition to its weighted moment. -/
+theorem weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (ht : 0 < t) (w : E) :
+    Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) ∧
+    (∫ y : E, ‖Third t (y + w)‖ * ‖y‖ ^ α) ≤
+      (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖) := by
+  have hiα := (integrable_weighted_third hα hα1 ht).comp_add_right w
+  have hi0 : Integrable (fun y : E => ‖Third t y‖) := by
+    simpa using integrable_weighted_third (α := 0) (by norm_num) (by norm_num) ht
+  have hiw := (hi0.comp_add_right w).const_mul (‖w‖ ^ α)
+  have hmajor := hiα.add hiw
+  have hb (y : E) : ‖Third t (y + w)‖ * ‖y‖ ^ α ≤
+      ‖Third t (y + w)‖ * ‖y + w‖ ^ α + ‖w‖ ^ α * ‖Third t (y + w)‖ := by
+    have hnorm : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
+      simpa only [add_sub_cancel_right] using norm_sub_le (y + w) w
+    have hp : ‖y‖ ^ α ≤ ‖y + w‖ ^ α + ‖w‖ ^ α :=
+      (Real.rpow_le_rpow (norm_nonneg y) hnorm hα).trans
+        (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hα hα1)
+    calc
+      _ ≤ ‖Third t (y + w)‖ * (‖y + w‖ ^ α + ‖w‖ ^ α) :=
+        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
+      _ = _ := by ring
+  have hD : Continuous (Third t) :=
+    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)).continuous
+  have hi : Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) :=
+    hmajor.mono' ((hD.comp (continuous_id.add continuous_const)).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+      (Filter.Eventually.of_forall fun y => by
+        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+        exact hb y)
+  refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
+  simp only [Pi.add_apply]
+  rw [integral_add hiα hiw, integral_const_mul,
+    integral_add_right_eq_self (fun y : E => ‖Third t y‖ * ‖y‖ ^ α) w,
+    integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]
+
+/-- The segment parameter and the weighted spatial third derivative form an integrable product. -/
+theorem integrable_segment_weighted_third {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
+    Integrable (fun p : ℝ × E => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α)
+      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
+  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
+  have hD : Continuous (Third t) :=
+    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)).continuous
+  have hg : Continuous G :=
+    (hD.comp (continuous_snd.add (continuous_fst.smul continuous_const))).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
+  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
+  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
+  refine ⟨Filter.Eventually.of_forall fun r => (weighted_third_translation hα hα1 ht (r • w)).1, ?_⟩
+  have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
+  refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
+  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
+  have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
+    apply integral_congr_ae
+    exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
+      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+  rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
+  have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
+    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
+    rw [norm_smul_of_nonneg hr.1]
+    nlinarith [norm_nonneg w, hr.2]
+  exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
+    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
+      (integral_nonneg (fun y => norm_nonneg _))))
+
+/-- Integrating the segment estimate gives a weighted translation estimate for the Hessian. -/
+theorem weighted_hessian_translation {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
+    Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ∧
+    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
+      ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := by
+  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
+  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
+  have hg : Integrable G ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
+    integrable_segment_weighted_third hα hα1 ht w
+  have hiMajor := hg.integral_prod_right.const_mul ‖w‖
+  have hb (y : E) : ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α ≤
+      ‖w‖ * (∫ r in Icc (0 : ℝ) 1, G (r, y)) := by
+    calc
+      _ ≤ (∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖) * ‖y‖ ^ α :=
+        mul_le_mul_of_nonneg_right (norm_hessian_translation_le t y w)
+          (Real.rpow_nonneg (norm_nonneg _) _)
+      _ = _ := by
+        change _ = ‖w‖ * (∫ r in Icc (0 : ℝ) 1, ‖Third t (y + r • w)‖ * ‖y‖ ^ α)
+        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
+          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
+        ring
+  have hH : Continuous (Hess t) :=
+    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
+  have hi : Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) :=
+    hiMajor.mono' (((hH.comp (continuous_id.add continuous_const)).sub hH).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+      (Filter.Eventually.of_forall fun y => by
+        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+        exact hb y)
+  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
+  rw [integral_const_mul]
+  have hswap : (∫ y : E, ∫ r in Icc (0 : ℝ) 1, G (r, y)) =
+      ∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y) :=
+    (integral_integral_swap hg).symm
+  rw [hswap]
+  apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
+  calc
+    (∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc (0 : ℝ) 1, C := by
+      apply integral_mono_ae hg.integral_prod_left (integrable_const C)
+      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
+      have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
+        apply Real.rpow_le_rpow (norm_nonneg _) _ hα
+        rw [norm_smul_of_nonneg hr.1]
+        nlinarith [norm_nonneg w, hr.2]
+      exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
+        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
+          (integral_nonneg (fun y => norm_nonneg _))))
+    _ = C := by simp
+
+/-- Beyond the spatial time scale, both translation terms have the same time power. -/
+theorem weighted_hessian_translation_far {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) (hw : ‖w‖ ^ 2 ≤ t) :
+    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
+      ‖w‖ * t ^ (α / 2 - 3 / 2) *
+        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
+  have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
+    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (show 0 ≤ α / 2 by linarith)
+    rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
+    have he : (2 : ℝ) * (α / 2) = α := by ring
+    simpa only [Nat.cast_ofNat, he] using h
+  have hzero : (∫ y : E, ‖Third t y‖) =
+      t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖) := by
+    simpa using weighted_third_integral ht 0
+  have hJ : 0 ≤ ∫ y : E, ‖Third 1 y‖ := integral_nonneg (fun y => norm_nonneg _)
+  calc
+    _ ≤ ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) +
+        ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := (weighted_hessian_translation hα hα1 ht w).2
+    _ = ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
+        ‖w‖ ^ α * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
+      rw [weighted_third_integral ht, hzero]
+    _ ≤ ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
+        t ^ (α / 2) * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
+      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
+      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp
+        (mul_nonneg (Real.rpow_nonneg ht.le _) hJ))
+    _ = _ := by
+      rw [← mul_assoc (t ^ (α / 2)), ← Real.rpow_add ht]
+      rw [show α / 2 + -(3 / 2 : ℝ) = α / 2 - 3 / 2 by ring]
+      ring
+
+/-- The far-time spatial heat Hessian increment is linear in the observation distance. -/
+theorem norm_heat_hessian_difference_far_le {α t M K : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (hK0 : 0 ≤ K)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : ‖x - z‖ ^ 2 ≤ t) :
+    ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z‖ ≤
+      ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
+        K * ‖x - z‖ * t ^ (α / 2 - 3 / 2) := by
+  rw [hessian_heatSolution_difference_eq_integral ht hf hM x z]
+  have hi := (weighted_hessian_translation hα hα1 ht (z - x)).1.const_mul K
+  have hb (y : E) : ‖(f (x - y) - f x) • (Hess t y - Hess t (y + (z - x)))‖ ≤
+      K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := by
+    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
+      have he : x - y - x = -y := by abel
+      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
+    calc
+      _ ≤ ‖f (x - y) - f x‖ * ‖Hess t y - Hess t (y + (z - x))‖ :=
+        norm_real_smul_continuousLinearMap_two_le _ _
+      _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y - Hess t (y + (z - x))‖ :=
+        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
+      _ = _ := by rw [norm_sub_rev (Hess t y)]; ring
+  calc
+    _ ≤ ∫ y : E, K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) :=
+      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
+    _ = K * (∫ y : E, ‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := integral_const_mul _ _
+    _ ≤ K * (‖z - x‖ * t ^ (α / 2 - 3 / 2) *
+        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖))) :=
+      mul_le_mul_of_nonneg_left (weighted_hessian_translation_far hα hα1 ht (z - x)
+        (by simpa only [norm_sub_rev z x] using hscale)) hK0
+    _ = _ := by rw [norm_sub_rev z x]; ring
+
+/-- The far part of the cancelled Duhamel Hessian has the spatial Hölder bound. -/
+theorem far_hessian_difference_le {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hρ : 0 < ‖x - z‖) (hscale : ‖x - z‖ ^ 2 < t) :
+    ‖(∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
+        (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
+      (∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
+        (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
+      (((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
+        (2 / (1 - α))) * K * ‖x - z‖ ^ α := by
+  let a := t - ‖x - z‖ ^ 2
+  let J := (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)
+  let F := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
+  have ha : 0 < a := sub_pos.mpr hscale
+  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
+  have hρ2 : 0 < ‖x - z‖ ^ 2 := sq_pos_of_pos hρ
+  have hJ : 0 ≤ J := add_nonneg
+    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+    (integral_nonneg (fun y => norm_nonneg _))
+  have hFi (p : E) : IntervalIntegrable (fun s => F s p) volume 0 a :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
+      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
+        (Ioo_subset_Ioo le_rfl hat))
+  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 3 / 2)) volume (‖x - z‖ ^ 2) t := by
+    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
+    rw [uIcc_of_le hscale.le]
+    intro hz
+    exact (not_le.mpr hρ2) hz.1
+  have hiB : IntervalIntegrable
+      (fun s : ℝ => J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2)) volume 0 a := by
+    have h := (hip.comp_sub_left t).symm
+    simp only [sub_self] at h
+    exact h.const_mul (J * K * ‖x - z‖)
+  have hbound : ‖∫ s in (0 : ℝ)..a, F s x - F s z‖ ≤
+      ∫ s in (0 : ℝ)..a, J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2) := by
+    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
+    refine Filter.Eventually.of_forall fun s hs => ?_
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht.2⟩
+    have hsτ : ‖x - z‖ ^ 2 ≤ t - s := by dsimp [a] at hs; linarith [hs.2]
+    have hτ : 0 < t - s := hρ2.trans_le hsτ
+    have hfc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
+    dsimp only [F]
+    rw [← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs x,
+      ← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs z]
+    exact norm_heat_hessian_difference_far_le hα.le hα1.le hτ hK0
+      hfc.aestronglyMeasurable hMs (hK s hsT) x z hsτ
+  change ‖(∫ s in (0 : ℝ)..a, F s x) - (∫ s in (0 : ℝ)..a, F s z)‖ ≤ _
+  rw [← intervalIntegral.integral_sub (hFi x) (hFi z)]
+  refine hbound.trans ?_
+  rw [intervalIntegral.integral_const_mul]
+  calc
+    (J * K * ‖x - z‖) * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2)) =
+        (J * K) * (‖x - z‖ * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2))) := by ring
+    _ ≤ (J * K) * ((2 / (1 - α)) * ‖x - z‖ ^ α) :=
+      mul_le_mul_of_nonneg_left (far_time_power_integral_le hα1 hρ hscale.le) (mul_nonneg hJ hK0)
+    _ = _ := by ring
+
+/-- The spatial Hölder estimate for the actual Duhamel Hessian. -/
+theorem duhamel_hessian_spatial_holder :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ∀ t ∈ Icc 0 T, ∀ x z : E,
+    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α := by
+  intro α hα hα1
+  let N := 2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
+  let F := ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) * (2 / (1 - α))
+  have hN : 0 ≤ N := mul_nonneg
+    (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
+      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
+    (div_nonneg (by norm_num) hα.le)
+  have hF : 0 ≤ F := mul_nonneg
+    (add_nonneg (integral_nonneg (fun y =>
+      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+      (integral_nonneg (fun y => norm_nonneg _)))
+    (div_nonneg (by norm_num) (by linarith))
+  refine ⟨max 1 (N + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro T _ _ f M K _ hK0 hf hM hK
+  dsimp only
+  intro t ht x z
+  have hC : N + F ≤ max 1 (N + F) := le_max_right _ _
+  have hpow : 0 ≤ ‖x - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
+  suffices hraw : ‖fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x)) x -
+      fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x)) z‖ ≤ (N + F) * K * ‖x - z‖ ^ α by
+    exact hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hK0) hpow)
+  by_cases he : x = z
+  · subst z
+    simp [Real.zero_rpow hα.ne']
+  have hρ : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
+  by_cases htime : t ≤ ‖x - z‖ ^ 2
+  · exact (duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht hK0 hf hM hK x z htime).trans
+      (mul_le_mul_of_nonneg_right
+        (mul_le_mul_of_nonneg_right (show N ≤ N + F by linarith) hK0) hpow)
+  have hscale : ‖x - z‖ ^ 2 < t := lt_of_not_ge htime
+  let a := t - ‖x - z‖ ^ 2
+  let H := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
+  have ha : 0 < a := sub_pos.mpr hscale
+  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
+  have h0t (p : E) : IntervalIntegrable (fun s => H s p) volume 0 t :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
+      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK p)
+  have h0a (p : E) : IntervalIntegrable (fun s => H s p) volume 0 a :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
+      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
+        (Ioo_subset_Ioo le_rfl hat))
+  have hsplit (p : E) : (∫ s in (0 : ℝ)..t, H s p) =
+      (∫ s in (0 : ℝ)..a, H s p) + (∫ s in a..t, H s p) :=
+    (intervalIntegral.integral_add_adjacent_intervals (h0a p) ((h0a p).symm.trans (h0t p))).symm
+  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
+    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
+  change ‖(∫ s in (0 : ℝ)..t, H s x) - (∫ s in (0 : ℝ)..t, H s z)‖ ≤ _
+  rw [hsplit x, hsplit z]
+  have hnear : ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ ≤ N * K * ‖x - z‖ ^ α := by
+    apply near_hessian_difference_le hα hα1 hK0 hat
+    · intro s hs
+      exact hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht.2⟩
+    · dsimp only [a]
+      linarith
+  have hfar : ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ ≤ F * K * ‖x - z‖ ^ α :=
+    far_hessian_difference_le hα hα1 ht hK0 hf hM hK x z hρ hscale
+  calc
+    _ = ‖((∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)) +
+        ((∫ s in a..t, H s x) - (∫ s in a..t, H s z))‖ := by congr 1; abel
+    _ ≤ ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ +
+        ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ := norm_add_le _ _
+    _ ≤ F * K * ‖x - z‖ ^ α + N * K * ‖x - z‖ ^ α := add_le_add hfar hnear
+    _ = (N + F) * K * ‖x - z‖ ^ α := by ring
+
+end Poincare.HeatDuhamelHessianSpatialHolder
```

</details>

<details>
<summary>Probe 001-statement — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/holder-evidence/Statement.lean`.

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation
open Set MeasureTheory
noncomputable section
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
#check (
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t ∈ Icc 0 T, ∀ x z : E,
    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α : Prop)
```

Actual output:

```text
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × E → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Icc 0 T ×ˢ univ) →
                        (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                          (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t ∈ Icc 0 T,
                              ∀ (x z : E),
                                ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α : Prop
```

</details>

<details>
<summary>Probe 002-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 002-third-formula.lean
@@ -1,16 +1,55 @@
 import Poincare.Global.HeatDuhamelHessianDifferentiation
+
+set_option autoImplicit false
+
+noncomputable section
+
 open Set MeasureTheory
-noncomputable section
+open scoped Topology RealInnerProductSpace Interval
+
+namespace Poincare.HeatDuhamelHessianSpatialHolder
+
 local notation "E" => Poincare.ClosedSmoothModel 3
 local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-#check (
-  ∀ α : ℝ, 0 < α → α < 1 →
-  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
-  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
-  ContinuousOn f (Icc 0 T ×ˢ univ) →
-  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
-  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
-  let u : ℝ → E → ℝ := fun t x =>
-    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
-  ∀ t ∈ Icc 0 T, ∀ x z : E,
-    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α : Prop)
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+local notation "Third" => fun (t : ℝ) (x : E) => fderiv ℝ (Hess t) x
+
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+  HeatDuhamelHessianDifferentiation
+
+/-- The third derivative of the Gaussian, evaluated in three directions. -/
+theorem third_apply {t : ℝ} (ht : t ≠ 0) (x u v w : E) :
+    Third t x u v w = heatKernel t x *
+      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
+        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
+          ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2)) := by
+  have hH : ContDiff ℝ 1 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
+  have hd := (((hH.differentiable (by norm_num) x).hasFDerivAt.clm_apply
+    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x))
+  have he : (fun z : E => Hess t z v w) = fun z : E => heatKernel t z *
+      (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
+    funext z
+    simpa only [iteratedFDeriv_two_apply] using
+      iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht z v w
+  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
+  have hw := (innerSL ℝ w).hasFDerivAt (x := x)
+  have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
+    (((hv.mul hw).div_const (4 * t ^ 2)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
+  rw [he] at hd
+  have hp' : HasFDerivAt (fun z : E => heatKernel t z *
+      (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))) _ x := by
+    simpa only [innerSL_apply_apply, real_inner_comm] using hp
+  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp')
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
+    ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, smul_eq_mul,
+    innerSL_apply_apply] at h
+  rw [h]
+  simp only [heatKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
+    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
+  ring
+
+end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:24:15: error: unexpected identifier; expected ')', ',' or ':'
```

</details>

<details>
<summary>Probe 003-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 003-third-formula.lean
@@ -5,7 +5,7 @@
 noncomputable section
\u0020
 open Set MeasureTheory
-open scoped Topology RealInnerProductSpace Interval
+open scoped Topology InnerProductSpace Interval
\u0020
 namespace Poincare.HeatDuhamelHessianSpatialHolder
\u0020
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:40:18: error(lean.invalidField): Invalid field `div_const`: The environment does not contain `HasFDerivAtFilter.div_const`, so it is not possible to project the field `div_const` from an expression
  HasFDerivAt.mul hv hw
of type
  HasFDerivAtFilter (⇑((innerSL ℝ) v) * ⇑((innerSL ℝ) w))
    (((innerSL ℝ) v) x • (innerSL ℝ) w + ((innerSL ℝ) w) x • (innerSL ℝ) v) (𝓝 x ×ˢ pure x)
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:26:49: error: unsolved goals
t : ℝ
ht : t ≠ 0
x u v w : E
hH : ContDiff ℝ 1 ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t)
hd :
  HasFDerivAt (fun y => (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t y) v) w)
    ((((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v).comp 0 +
      (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x).comp 0 +
            (fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x).flip v).flip
        w)
    x
he :
  (fun z => (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t z) v) w) = fun z =>
    heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
hv : HasFDerivAt (⇑((innerSL ℝ) v)) ((innerSL ℝ) v) x
hw : HasFDerivAt (⇑((innerSL ℝ) w)) ((innerSL ℝ) w) x
⊢ ((((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t x) u) v) w =
    heatKernel t x *
      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ + ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2))
```

</details>

<details>
<summary>Probe 004-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 004-third-formula.lean
@@ -37,11 +37,11 @@
   have hv := (innerSL ℝ v).hasFDerivAt (x := x)
   have hw := (innerSL ℝ w).hasFDerivAt (x := x)
   have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
-    (((hv.mul hw).div_const (4 * t ^ 2)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
+    (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
   rw [he] at hd
   have hp' : HasFDerivAt (fun z : E => heatKernel t z *
       (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))) _ x := by
-    simpa only [innerSL_apply_apply, real_inner_comm] using hp
+    simpa only [innerSL_apply_apply, real_inner_comm, div_eq_mul_inv] using hp
   have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp')
   simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
     ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:42:13: error: typeclass instance problem is stuck
  Module ?m.563 ℝ

Note: Lean will not try to resolve this typeclass instance problem because the first and third type arguments to `Module` contain metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

</details>

<details>
<summary>Probe 005-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 005-third-formula.lean
@@ -39,7 +39,7 @@
   have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
     (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
   rw [he] at hd
-  have hp' : HasFDerivAt (fun z : E => heatKernel t z *
+  have hp' : HasFDerivAt (𝕜 := ℝ) (fun z : E => heatKernel t z *
       (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))) _ x := by
     simpa only [innerSL_apply_apply, real_inner_comm, div_eq_mul_inv] using hp
   have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp')
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:43:64: error: don't know how to synthesize placeholder for argument `f'`
context:
t : ℝ
ht : t ≠ 0
x u v w : E
hH : ContDiff ℝ 1 ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t)
hd :
  HasFDerivAt (fun z => heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)))
    ((((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v).comp 0 +
      (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x).comp 0 +
            (fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x).flip v).flip
        w)
    x
he :
  (fun z => (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t z) v) w) = fun z =>
    heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
hv : HasFDerivAt (⇑((innerSL ℝ) v)) ((innerSL ℝ) v) x
hw : HasFDerivAt (⇑((innerSL ℝ) w)) ((innerSL ℝ) w) x
hp :
  HasFDerivAt
    ((fun z => heatKernel t z) * fun x => (⇑((innerSL ℝ) v) * ⇑((innerSL ℝ) w)) x * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ / (2 * t))
    (heatKernel t x • (4 * t ^ 2)⁻¹ • (((innerSL ℝ) v) x • (innerSL ℝ) w + ((innerSL ℝ) w) x • (innerSL ℝ) v) +
      ((⇑((innerSL ℝ) v) * ⇑((innerSL ℝ) w)) x * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ / (2 * t)) •
        (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) / 2) •
          Real.exp (-‖x‖ ^ 2 / (4 * t)) • -(1 / (2 * t)) • (innerSL ℝ) x)
    x
⊢ E →L[ℝ] ℝ
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:26:49: error: unsolved goals
t : ℝ
ht : t ≠ 0
x u v w : E
hH : ContDiff ℝ 1 ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t)
hd :
  HasFDerivAt (fun z => heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)))
    ((((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v).comp 0 +
      (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x).comp 0 +
            (fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x).flip v).flip
        w)
    x
he :
  (fun z => (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t z) v) w) = fun z =>
    heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
hv : HasFDerivAt (⇑((innerSL ℝ) v)) ((innerSL ℝ) v) x
hw : HasFDerivAt (⇑((innerSL ℝ) w)) ((innerSL ℝ) w) x
hp :
  HasFDerivAt
    ((fun z => heatKernel t z) * fun x => (⇑((innerSL ℝ) v) * ⇑((innerSL ℝ) w)) x * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ / (2 * t))
    (heatKernel t x • (4 * t ^ 2)⁻¹ • (((innerSL ℝ) v) x • (innerSL ℝ) w + ((innerSL ℝ) w) x • (innerSL ℝ) v) +
      ((⇑((innerSL ℝ) v) * ⇑((innerSL ℝ) w)) x * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ / (2 * t)) •
        (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) / 2) •
          Real.exp (-‖x‖ ^ 2 / (4 * t)) • -(1 / (2 * t)) • (innerSL ℝ) x)
    x
⊢ ((((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t x) u) v) w =
    heatKernel t x *
      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ + ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2))
```

</details>

<details>
<summary>Probe 006-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 006-third-formula.lean
@@ -39,10 +39,9 @@
   have hp := (hasFDerivAt_heatKernel_spatial («E» := E) ht x).mul
     (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
   rw [he] at hd
-  have hp' : HasFDerivAt (𝕜 := ℝ) (fun z : E => heatKernel t z *
-      (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))) _ x := by
-    simpa only [innerSL_apply_apply, real_inner_comm, div_eq_mul_inv] using hp
-  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp')
+  simp only [Pi.mul_apply, innerSL_apply_apply, div_eq_mul_inv] at hp hd
+  simp_rw [real_inner_comm v, real_inner_comm w] at hp
+  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp)
   simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
     ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
     ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, smul_eq_mul,
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:43:11: error: `simp` made no progress
```

</details>

<details>
<summary>Probe 007-third-formula — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 007-third-formula.lean
@@ -40,7 +40,6 @@
     (((hv.mul hw).mul_const ((4 * t ^ 2)⁻¹)).sub_const (⟪v, w⟫_ℝ / (2 * t)))
   rw [he] at hd
   simp only [Pi.mul_apply, innerSL_apply_apply, div_eq_mul_inv] at hp hd
-  simp_rw [real_inner_comm v, real_inner_comm w] at hp
   have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp)
   simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
     ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:43:59: error: Application type mismatch: The argument
  hp
has type
  HasFDerivAt ((fun z => heatKernel t z) * fun x => ⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹)
    (heatKernel t x • (4 * t ^ 2)⁻¹ • (⟪v, x⟫_ℝ • (innerSL ℝ) w + ⟪w, x⟫_ℝ • (innerSL ℝ) v) +
      (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹) •
        (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) * 2⁻¹) •
          Real.exp (-‖x‖ ^ 2 * (4 * t)⁻¹) • -(1 * (2 * t)⁻¹) • (innerSL ℝ) x)
    x
but is expected to have type
  HasFDerivAt (fun z => heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹)) ?m.603 x
in the application
  HasFDerivAt.unique hd hp
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:26:49: error: unsolved goals
t : ℝ
ht : t ≠ 0
x u v w : E
hH : ContDiff ℝ 1 ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t)
he :
  (fun z => (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t z) v) w) = fun z =>
    heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
hv : HasFDerivAt (⇑((innerSL ℝ) v)) ((innerSL ℝ) v) x
hw : HasFDerivAt (⇑((innerSL ℝ) w)) ((innerSL ℝ) w) x
hp :
  HasFDerivAt ((fun z => heatKernel t z) * fun x => ⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹)
    (heatKernel t x • (4 * t ^ 2)⁻¹ • (⟪v, x⟫_ℝ • (innerSL ℝ) w + ⟪w, x⟫_ℝ • (innerSL ℝ) v) +
      (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹) •
        (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) * 2⁻¹) •
          Real.exp (-‖x‖ ^ 2 * (4 * t)⁻¹) • -(1 * (2 * t)⁻¹) • (innerSL ℝ) x)
    x
hd :
  HasFDerivAt (fun z => heatKernel t z * (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ * (4 * t ^ 2)⁻¹ - ⟪v, w⟫_ℝ * (2 * t)⁻¹))
    (((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) v).comp 0 +
      ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x).comp 0 +
            (fderiv ℝ (fun x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) x).flip v).flip
        w)
    x
⊢ ((((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t x) u) v) w =
    heatKernel t x *
      (-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / (8 * t ^ 3) +
        (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ + ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / (4 * t ^ 2))
```

</details>

<details>
<summary>Probe 008-third-formula — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 008-third-formula.lean
@@ -30,9 +30,9 @@
   have hd := (((hH.differentiable (by norm_num) x).hasFDerivAt.clm_apply
     (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x))
   have he : (fun z : E => Hess t z v w) = fun z : E => heatKernel t z *
-      (⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
+      (⟪v, z⟫_ℝ * ⟪w, z⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
     funext z
-    simpa only [iteratedFDeriv_two_apply] using
+    simpa only [iteratedFDeriv_two_apply, real_inner_comm] using
       iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht z v w
   have hv := (innerSL ℝ v).hasFDerivAt (x := x)
   have hw := (innerSL ℝ w).hasFDerivAt (x := x)
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:46:46: warning: This simp argument is unused:
  add_zero

Hint: Omit it from the simp argument list.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
  ̲  ̲ ̲ ̲map_zero, a̵d̵d̵_̵z̵e̵r̵o̵,̵ ̵zero_add, smul_eq_mul, innerSL_apply_apply] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:49:25: warning: This simp argument is unused:
  ContinuousLinearMap.sub_apply

Hint: Omit it from the simp argument list.
  simp only [heatKernel, C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵u̵b̵_̵a̵p̵p̵l̵y̵,̵ ̵ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
  ̲  ̲ ̲ ̲innerSL_apply_apply, smul_eq_mul, real_inner_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:49:56: warning: This simp argument is unused:
  ContinuousLinearMap.smulRight_apply

Hint: Omit it from the simp argument list.
  simp only [heatKernel, ContinuousLinearMap.sub_apply, C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵R̵i̵g̵h̵t̵_̵a̵p̵p̵l̵y̵,̵ContinuousLinearMap.id_apply,
      innerSL_apply_apply, smul_eq_mul, real_inner_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:50:4: warning: This simp argument is unused:
  ContinuousLinearMap.id_apply

Hint: Omit it from the simp argument list.
  simp only [heatKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵i̵d̵_̵a̵p̵p̵l̵y̵,̵ ̵innerSL_apply_apply, smul_eq_mul, real_inner_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:50:34: warning: This simp argument is unused:
  innerSL_apply_apply

Hint: Omit it from the simp argument list.
  simp only [heatKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, i̵n̵n̵e̵r̵S̵L̵_̵a̵p̵p̵l̵y̵_̵a̵p̵p̵l̵y̵,̵ ̵smul_eq_mul, real_inner_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:50:55: warning: This simp argument is unused:
  smul_eq_mul

Hint: Omit it from the simp argument list.
  simp only [heatKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, s̵m̵u̵l̵_̵e̵q̵_̵m̵u̵l̵,̵ ̵real_inner_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

</details>

<details>
<summary>Probe 009-third-formula-clean — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 009-third-formula-clean.lean
@@ -43,11 +43,10 @@
   have h := congrArg (fun L : E →L[ℝ] ℝ => L u) (hd.unique hp)
   simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
     ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
-    ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, smul_eq_mul,
+    ContinuousLinearMap.zero_apply, map_zero, zero_add, smul_eq_mul,
     innerSL_apply_apply] at h
   rw [h]
-  simp only [heatKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
-    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
+  simp only [heatKernel, real_inner_comm]
   ring
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 010-third-norm — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 010-third-norm.lean
@@ -49,4 +49,40 @@
   simp only [heatKernel, real_inner_comm]
   ring
\u0020
+/-- The unit-time third derivative has a cubic Gaussian envelope. -/
+theorem norm_third_one_le (x : E) :
+    ‖Third 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by
+  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
+  have hB : 0 ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) := by positivity
+  apply ContinuousLinearMap.opNorm_le_bound _ hB
+  intro u
+  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg u))
+  intro v
+  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+  intro w
+  rw [third_apply one_ne_zero]
+  norm_num only [one_pow, mul_one]
+  rw [norm_mul, Real.norm_of_nonneg hk]
+  calc
+    _ ≤ heatKernel 1 x *
+        (‖⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ‖ / 8 +
+          ((‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ‖ + ‖⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖) +
+            ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖) / 4) := by
+      gcongr
+      calc
+        _ ≤ ‖-(⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) / 8‖ +
+            ‖(⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ +
+              ⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ) / 4‖ := norm_add_le _ _
+        _ ≤ _ := by
+          simp only [norm_div, norm_neg, Real.norm_ofNat]
+          gcongr
+          exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
+    _ ≤ heatKernel 1 x *
+        (((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) / 8 +
+          (((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖)) +
+            (‖x‖ * ‖u‖) * (‖v‖ * ‖w‖)) / 4) := by
+      simp only [norm_mul]
+      gcongr <;> apply norm_inner_le_norm
+    _ = _ := by ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:54:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Norm (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

</details>

<details>
<summary>Probe 011-third-norm — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 011-third-norm.lean
@@ -11,6 +11,7 @@
\u0020
 local notation "E" => Poincare.ClosedSmoothModel 3
 local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
 local notation "Hess" => fun (t : ℝ) (x : E) =>
   fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
 local notation "Third" => fun (t : ℝ) (x : E) => fderiv ℝ (Hess t) x
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:14:67: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:58:2: error: Tactic `apply` failed: could not unify the conclusion of `ContinuousLinearMap.opNorm_le_bound ?m.182 hB`
  ‖?m.182‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)
with the goal
  ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) 1 x‖ ≤
    heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)

Note: The full type of `ContinuousLinearMap.opNorm_le_bound ?m.182 hB` is
  (∀ (x_1 : ?m.173), ‖?m.182 x_1‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4) * ‖x_1‖) →
    ‖?m.182‖ ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)

x : E
hk : 0 ≤ heatKernel 1 x
hB : 0 ≤ heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)
⊢ ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) 1 x‖ ≤
    heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)
```

</details>

<details>
<summary>Probe 012-third-norm — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 012-third-norm.lean
@@ -11,6 +11,8 @@
\u0020
 local notation "E" => Poincare.ClosedSmoothModel 3
 local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
 local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
 local notation "Hess" => fun (t : ℝ) (x : E) =>
   fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:82:40: error: Application type mismatch: The argument
  add_le_add_right (norm_add_le ?m.601 ?m.602) ?m.603
has type
  ?m.603 + ‖?m.601 + ?m.602‖ ≤ ?m.603 + (‖?m.601‖ + ‖?m.602‖)
but is expected to have type
  ‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖ + ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖ ≤
    ‖⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ‖ + ‖⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ‖ + ‖⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ‖
in the application
  LE.le.trans (norm_add_le (⟪u, v⟫_ℝ * ⟪x, w⟫_ℝ + ⟪x, v⟫_ℝ * ⟪u, w⟫_ℝ) (⟪x, u⟫_ℝ * ⟪v, w⟫_ℝ))
    (add_le_add_right (norm_add_le ?m.601 ?m.602) ?m.603)
```

</details>

<details>
<summary>Probe 013-third-norm — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 013-third-norm.lean
@@ -79,7 +79,7 @@
         _ ≤ _ := by
           simp only [norm_div, norm_neg, Real.norm_ofNat]
           gcongr
-          exact (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
+          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
     _ ≤ heatKernel 1 x *
         (((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) / 8 +
           (((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖)) +
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 014-third-integrable — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 014-third-integrable.lean
@@ -88,4 +88,49 @@
       gcongr <;> apply norm_inner_le_norm
     _ = _ := by ring
\u0020
+/-- The weighted third derivative is integrable at unit time. -/
+theorem integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
+    Integrable (fun x : E => ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
+  have hc : 0 ≤ c := by dsimp [c]; positivity
+  have hweight : Continuous (fun x : E => ‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))) :=
+    ((Real.continuous_rpow_const (by linarith : 0 ≤ α + 1)).comp continuous_norm).mul
+      (((continuous_norm.pow 2).div_const 8).neg.rexp)
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
+      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+      hweight.aestronglyMeasurable
+      (Filter.Eventually.of_forall fun x => show
+        ‖‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
+          rw [Real.norm_of_nonneg (by positivity)]
+          exact rpow_mul_gaussian_le_eight (by linarith) (by linarith) (norm_nonneg x))
+  have hcont : ContDiff ℝ 0 (Third 1) :=
+    (((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)
+  refine (hbound.const_mul c).mono'
+    (hcont.continuous.norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
+  refine Filter.Eventually.of_forall fun x => ?_
+  rw [Real.norm_of_nonneg (by positivity)]
+  have hK : heatKernel (1 : ℝ) x =
+      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
+    rw [← Real.exp_add]
+    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
+      Nat.cast_ofNat, mul_one]
+    congr 1
+    congr 1
+    ring
+  have hw : ‖x‖ ^ (α + 1) = ‖x‖ ^ α * ‖x‖ :=
+    Real.rpow_add_one' (norm_nonneg x) (by linarith)
+  calc
+    ‖Third 1 x‖ * ‖x‖ ^ α ≤
+        (heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)) * ‖x‖ ^ α :=
+      mul_le_mul_of_nonneg_right (norm_third_one_le x) (Real.rpow_nonneg (norm_nonneg x) α)
+    _ ≤ (heatKernel 1 x * (‖x‖ * (1 + ‖x‖ ^ 2))) * ‖x‖ ^ α := by
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
+      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
+      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg x) 3]
+    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
+        (‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK, hw]; ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 015-third-scaling — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 015-third-scaling.lean
@@ -133,4 +133,15 @@
     _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
         (‖x‖ ^ (α + 1) * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK, hw]; ring
\u0020
+/-- Parabolic dilation of the full third spatial derivative. -/
+theorem third_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    Third (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹) • Third 1 x := by
+  ext u v w
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
+  rw [third_apply (pow_ne_zero _ ha.ne'), third_apply one_ne_zero,
+    heatKernel_sq_smul a ha x]
+  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
+  field_simp
+  <;> ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:145:6: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:145:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
```

</details>

<details>
<summary>Probe 016-third-weight-scaling — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 016-third-weight-scaling.lean
@@ -142,6 +142,14 @@
     heatKernel_sq_smul a ha x]
   simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
   field_simp
-  <;> ring
+
+/-- Pointwise parabolic dilation including the radial weight. -/
+theorem weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
+    ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
+      ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (‖Third 1 x‖ * ‖x‖ ^ α) := by
+  rw [third_sq_smul a ha x,
+    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 3)⁻¹ by positivity) (Third 1 x),
+    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
+  ring
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 017-third-integral-scaling — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 017-third-integral-scaling.lean
@@ -152,4 +152,20 @@
     norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
   ring
\u0020
+/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
+theorem weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
+    (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
+      ((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Third (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ x : E, ‖Third (a ^ 2) x‖ * ‖x‖ ^ α) =
+        ∫ x : E, ‖Third (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+      simp_rw [weighted_third_sq_smul a ha]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α)) := by ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 018-third-integrable-positive — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 018-third-integrable-positive.lean
@@ -168,4 +168,14 @@
       rw [integral_const_mul]
     _ = (a ^ 3)⁻¹ * (((a ^ 3)⁻¹ * a ^ α) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α)) := by ring
\u0020
+/-- Weighted Bochner integrability at every positive time. -/
+theorem integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) := by
+  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
+  rw [← Real.sq_sqrt ht.le]
+  apply (integrable_comp_smul_iff volume _ ha.ne').1
+  simp_rw [weighted_third_sq_smul (Real.sqrt t) ha]
+  exact (integrable_weighted_third_one hα hα1).const_mul _
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 019-third-integral-positive — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 019-third-integral-positive.lean
@@ -178,4 +178,20 @@
   simp_rw [weighted_third_sq_smul (Real.sqrt t) ha]
   exact (integrable_weighted_third_one hα hα1).const_mul _
\u0020
+/-- Exact scaling of the third spatial derivative moment. -/
+theorem weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
+    (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) =
+      t ^ (α / 2 - 3 / 2) * (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α) := by
+  have h := weighted_third_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h]
+  congr 1
+  have hp : (Real.sqrt t) ^ 3 = t ^ ((3 : ℝ) / 2) := by
+    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
+    congr 1
+    norm_num
+  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht]
+  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
+  ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 020-third-moment-bound — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 020-third-moment-bound.lean
@@ -194,4 +194,18 @@
   rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
   ring
\u0020
+/-- The third Gaussian moment has a positive constant independent of time. -/
+theorem third_moment_bound :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
+      Integrable (fun x : E => ‖Third t x‖ * ‖x‖ ^ α) ∧
+      (∫ x : E, ‖Third t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 3 / 2) := by
+  intro α hα hα1
+  refine ⟨max 1 (∫ x : E, ‖Third 1 x‖ * ‖x‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t ht
+  refine ⟨integrable_weighted_third hα.le hα1.le ht, ?_⟩
+  rw [weighted_third_integral ht, mul_comm (t ^ (α / 2 - 3 / 2))]
+  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 021-near-interval — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 021-near-interval.lean
@@ -208,4 +208,23 @@
   rw [weighted_third_integral ht, mul_comm (t ^ (α / 2 - 3 / 2))]
   exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
\u0020
+/-- The near-time cancelled integral is bounded by the length of its time interval. -/
+theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hat : a ≤ t) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (t - a) ^ (α / 2) := by
+  have hb := norm_integral_cancelled_hessian_time_le hα hα1 (sub_nonneg.mpr hat)
+    (f := fun p => f (p.1 + a, p.2))
+    (fun s hs => hK (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩) x
+  have he := intervalIntegral.integral_comp_add_right
+    (a := (0 : ℝ)) (b := t - a)
+    (fun s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) a
+  simp only [zero_add, sub_add_cancel] at he
+  have htau (s : ℝ) : t - a - s = t - (s + a) := by ring
+  simp only [htau] at hb
+  rw [he] at hb
+  exact hb
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 022-near-difference — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 022-near-difference.lean
@@ -227,4 +227,36 @@
   rw [he] at hb
   exact hb
\u0020
+/-- The near part of the spatial increment has the required Hölder power. -/
+theorem near_hessian_difference_le {α K a t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
+    {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a t, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : t - a ≤ ‖x - z‖ ^ 2) :
+    ‖(∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
+      (∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
+      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
+  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
+  have hJ : 0 ≤ J := integral_nonneg (fun y => by positivity)
+  have hp : (t - a) ^ (α / 2) ≤ ‖x - z‖ ^ α := by
+    calc
+      (t - a) ^ (α / 2) ≤ (‖x - z‖ ^ 2) ^ (α / 2) :=
+        Real.rpow_le_rpow (sub_nonneg.mpr hat) hscale (by linarith)
+      _ = ‖x - z‖ ^ α := by
+        rw [← Real.rpow_natCast_mul (norm_nonneg (x - z))]
+        congr 1
+        norm_num
+  calc
+    _ ≤ ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ +
+        ‖∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y‖ :=
+      norm_sub_le _ _
+    _ ≤ (K * J) * (2 / α) * (t - a) ^ (α / 2) +
+        (K * J) * (2 / α) * (t - a) ^ (α / 2) :=
+      add_le_add (norm_integral_cancelled_hessian_near_le hα hα1 hat hK x)
+        (norm_integral_cancelled_hessian_near_le hα hα1 hat hK z)
+    _ = (2 * J * (2 / α)) * K * (t - a) ^ (α / 2) := by ring
+    _ ≤ (2 * J * (2 / α)) * K * ‖x - z‖ ^ α :=
+      mul_le_mul_of_nonneg_left hp (by positivity)
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:246:25: error: unsolved goals
case e_a
α K a t : ℝ
hα : 0 < α
hα1 : α < 1
hK0 : 0 ≤ K
hat : a ≤ t
f : ℝ × E → ℝ
hK : ∀ s ∈ Ioo a t, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x z : E
hscale : t - a ≤ ‖x - z‖ ^ 2
J : ℝ := ∫ (y : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 y‖ * ‖y‖ ^ α
hJ : 0 ≤ J
⊢ 2 * (α / 2) = α
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:260:39: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

</details>

<details>
<summary>Probe 023-near-difference — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 023-near-difference.lean
@@ -227,6 +227,7 @@
   rw [he] at hb
   exact hb
\u0020
+set_option maxHeartbeats 800000 in
 /-- The near part of the spatial increment has the required Hölder power. -/
 theorem near_hessian_difference_le {α K a t : ℝ}
     (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
@@ -247,6 +248,7 @@
         rw [← Real.rpow_natCast_mul (norm_nonneg (x - z))]
         congr 1
         norm_num
+        ring
   calc
     _ ≤ ‖∫ s in a..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ +
         ‖∫ s in a..t, ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y‖ :=
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:262:39: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

</details>

<details>
<summary>Probe 024-near-difference — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 024-near-difference.lean
@@ -259,6 +259,8 @@
         (norm_integral_cancelled_hessian_near_le hα hα1 hat hK z)
     _ = (2 * J * (2 / α)) * K * (t - a) ^ (α / 2) := by ring
     _ ≤ (2 * J * (2 / α)) * K * ‖x - z‖ ^ α :=
-      mul_le_mul_of_nonneg_left hp (by positivity)
+      mul_le_mul_of_nonneg_left hp
+        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ)
+          (div_nonneg (by norm_num) hα.le)) hK0)
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 025-large-distance — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 025-large-distance.lean
@@ -263,4 +263,22 @@
         (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ)
           (div_nonneg (by norm_num) hα.le)) hK0)
\u0020
+/-- The spatial Hölder estimate for the actual Duhamel Hessian when the near interval is all of time. -/
+theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : t ≤ ‖x - z‖ ^ 2) :
+    let u : E → ℝ := fun x => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x
+    ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
+      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * ‖x - z‖ ^ α := by
+  dsimp only
+  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
+    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
+  exact near_hessian_difference_le hα hα1 hK0 ht.1
+    (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x z (by simpa using hscale)
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

</details>

<details>
<summary>Probe 026-far-time — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 026-far-time.lean
@@ -281,4 +281,32 @@
   exact near_hessian_difference_le hα hα1 hK0 ht.1
     (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x z (by simpa using hscale)
\u0020
+/-- The far-time power integral supplies the factor two over one minus the exponent. -/
+theorem far_time_power_integral_le {α ρ t : ℝ}
+    (hα1 : α < 1) (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ t) :
+    ρ * (∫ s in (0 : ℝ)..(t - ρ ^ 2), (t - s) ^ (α / 2 - 3 / 2)) ≤
+      (2 / (1 - α)) * ρ ^ α := by
+  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
+  have hq : α / 2 - 3 / 2 + 1 < 0 := by linarith
+  rw [intervalIntegral.integral_comp_sub_left
+    (fun r : ℝ => r ^ (α / 2 - 3 / 2)) t, sub_sub_cancel, sub_zero]
+  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
+  · calc
+      ρ * ((t ^ (α / 2 - 3 / 2 + 1) - (ρ ^ 2) ^ (α / 2 - 3 / 2 + 1)) /
+          (α / 2 - 3 / 2 + 1)) ≤
+          ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
+        apply mul_le_mul_of_nonneg_left _ hρ.le
+        simp only [div_eq_mul_inv]
+        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
+        linarith [Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)]
+      _ = (2 / (1 - α)) * ρ ^ α := by
+        rw [← Real.rpow_natCast_mul hρ.le]
+        rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
+        rw [Real.rpow_sub hρ, Real.rpow_one]
+        field_simp
+        <;> ring
+  · rw [uIcc_of_le ht]
+    intro hz
+    exact (not_le.mpr hρ2) hz.1
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:301:8: error: linarith failed to find a contradiction
case h
α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
a✝ : t ^ (α * 2⁻¹ - 3 * 2⁻¹ + 1) - (ρ ^ 2) ^ (α * 2⁻¹ - 3 * 2⁻¹ + 1) < -(ρ ^ 2) ^ (α * 2⁻¹ - 3 * 2⁻¹ + 1)
⊢ False
failed
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:304:12: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  2 * (α / 2 - 3 / 2 + 1)
in the target expression
  ρ * (-ρ ^ (↑2 * (α / 2 - 3 / 2 + 1)) / (α / 2 - 3 / 2 + 1)) = 2 / (1 - α) * ρ ^ α

α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
⊢ ρ * (-ρ ^ (↑2 * (α / 2 - 3 / 2 + 1)) / (α / 2 - 3 / 2 + 1)) = 2 / (1 - α) * ρ ^ α
```

</details>

<details>
<summary>Probe 027-far-time — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 027-far-time.lean
@@ -296,11 +296,12 @@
           (α / 2 - 3 / 2 + 1)) ≤
           ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
         apply mul_le_mul_of_nonneg_left _ hρ.le
-        simp only [div_eq_mul_inv]
+        rw [div_eq_mul_inv, div_eq_mul_inv]
         apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
         linarith [Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)]
       _ = (2 / (1 - α)) * ρ ^ α := by
         rw [← Real.rpow_natCast_mul hρ.le]
+        simp only [Nat.cast_ofNat]
         rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
         rw [Real.rpow_sub hρ, Real.rpow_one]
         field_simp
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:301:8: error: linarith failed to find a contradiction
case h
α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
a✝ : t ^ (α * 2⁻¹ - 3 / 2 + 1) - (ρ ^ 2) ^ (α * 2⁻¹ - 3 / 2 + 1) < -(ρ ^ 2) ^ (α * 2⁻¹ - 3 / 2 + 1)
⊢ False
failed
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:302:35: error: unsolved goals
α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
⊢ -(-1 + α)⁻¹ = (1 - α)⁻¹
```

</details>

<details>
<summary>Probe 028-far-time — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 028-far-time.lean
@@ -296,15 +296,19 @@
           (α / 2 - 3 / 2 + 1)) ≤
           ρ * (-(ρ ^ 2) ^ (α / 2 - 3 / 2 + 1) / (α / 2 - 3 / 2 + 1)) := by
         apply mul_le_mul_of_nonneg_left _ hρ.le
-        rw [div_eq_mul_inv, div_eq_mul_inv]
+        simp only [div_eq_mul_inv]
         apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
-        linarith [Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)]
+        have hnn := Real.rpow_nonneg (hρ2.le.trans ht) (α / 2 - 3 / 2 + 1)
+        simp only [div_eq_mul_inv] at hnn
+        linarith only [hnn]
       _ = (2 / (1 - α)) * ρ ^ α := by
         rw [← Real.rpow_natCast_mul hρ.le]
         simp only [Nat.cast_ofNat]
         rw [show (2 : ℝ) * (α / 2 - 3 / 2 + 1) = α - 1 by ring]
         rw [Real.rpow_sub hρ, Real.rpow_one]
-        field_simp
+        have hden : 1 - α ≠ 0 := by linarith
+        have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
+        field_simp [hρ.ne', hden, hden']
         <;> ring
   · rw [uIcc_of_le ht]
     intro hz
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:304:35: error: unsolved goals
α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
hden : 1 - α ≠ 0
hden' : α / 2 - 3 / 2 + 1 ≠ 0
⊢ α * (-1 + α)⁻¹ - (-1 + α)⁻¹ = 1
```

</details>

<details>
<summary>Probe 029-far-time — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 029-far-time.lean
@@ -308,7 +308,7 @@
         rw [Real.rpow_sub hρ, Real.rpow_one]
         have hden : 1 - α ≠ 0 := by linarith
         have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
-        field_simp [hρ.ne', hden, hden']
+        field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
         <;> ring
   · rw [uIcc_of_le ht]
     intro hz
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:304:35: error: unsolved goals
α ρ t : ℝ
hα1 : α < 1
hρ : 0 < ρ
ht : ρ ^ 2 ≤ t
hρ2 : 0 < ρ ^ 2
hq : α / 2 - 3 / 2 + 1 < 0
hden : 1 - α ≠ 0
hden' : α / 2 - 3 / 2 + 1 ≠ 0
⊢ α * (-1 + α)⁻¹ - (-1 + α)⁻¹ = 1
```

</details>

<details>
<summary>Probe 030-far-time — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 030-far-time.lean
@@ -309,7 +309,10 @@
         have hden : 1 - α ≠ 0 := by linarith
         have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
         field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
-        <;> ring
+        <;> ring_nf
+        all_goals
+          have hi := mul_inv_cancel₀ (show -1 + α ≠ 0 by linarith)
+          nlinarith only [hi]
   · rw [uIcc_of_le ht]
     intro hz
     exact (not_le.mpr hρ2) hz.1
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:312:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 031-translation — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 031-translation.lean
@@ -317,4 +317,27 @@
     intro hz
     exact (not_le.mpr hρ2) hz.1
\u0020
+/-- Both observation points can use the same cancellation constant. -/
+theorem hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
+      ∫ y : E, (f (x - y) - f x) • Hess t (y + (z - x)) := by
+  have hi : Integrable (fun y : E => f y • Hess t (z - y)) :=
+    integrable_data_smul_hessian_sub ht hf hM z
+  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
+    ((integrable_hessian ht).comp_sub_left z).smul (f x)
+  have hz : (∫ y : E, Hess t (z - y)) = 0 := by
+    rw [integral_sub_left_eq_self, integral_hessian_eq_zero ht]
+  have he : (∫ y : E, (f y - f x) • Hess t (z - y)) =
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z := by
+    simp_rw [sub_smul]
+    rw [integral_sub hi hc, integral_smul, hz, smul_zero, sub_zero,
+      hessian_heatSolution_eq_integral ht hf hM]
+  rw [← he]
+  have hchange := integral_sub_left_eq_self
+    (fun y : E => (f y - f x) • Hess t (z - y)) volume x
+  have halg (y : E) : z - (x - y) = y + (z - x) := by abel
+  simpa only [halg] using hchange.symm
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:312:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 032-difference-identity — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 032-difference-identity.lean
@@ -340,4 +340,23 @@
   have halg (y : E) : z - (x - y) = y + (z - x) := by abel
   simpa only [halg] using hchange.symm
\u0020
+/-- The Hessian increment is the cancelled integral of a kernel translation difference. -/
+theorem hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x z : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z =
+      ∫ y : E, (f (x - y) - f x) • (Hess t y - Hess t (y + (z - x))) := by
+  have hi := integrable_data_smul_hessian_sub ht hf hM z
+  have hc : Integrable (fun y : E => f x • Hess t (z - y)) :=
+    ((integrable_hessian ht).comp_sub_left z).smul (f x)
+  have hij : Integrable (fun y : E => (f (x - y) - f x) • Hess t (y + (z - x))) := by
+    have h := (hi.sub hc).comp_sub_left x
+    have halg (y : E) : z - (x - y) = y + (z - x) := by abel
+    simpa only [halg, ← sub_smul] using h
+  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM x,
+    hessian_heatSolution_eq_common_cancelled_integral ht hf hM x z]
+  simp_rw [smul_sub]
+  rw [integral_sub (integrable_cancelled_hessian ht hf hM x) hij]
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:312:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:356:4: error: Type mismatch: After simplification, term
  h
 has type
  Integrable
    (fun t_1 =>
      ((fun y => f y • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) (z - y)) - fun y =>
          f x • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) (z - y))
        (x - t_1))
    volume
but is expected to have type
  Integrable (fun y => (f (x - y) - f x) • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) (y + (z - x))) volume
```

</details>

<details>
<summary>Probe 033-difference-identity — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 033-difference-identity.lean
@@ -353,7 +353,7 @@
   have hij : Integrable (fun y : E => (f (x - y) - f x) • Hess t (y + (z - x))) := by
     have h := (hi.sub hc).comp_sub_left x
     have halg (y : E) : z - (x - y) = y + (z - x) := by abel
-    simpa only [halg, ← sub_smul] using h
+    simpa only [Pi.sub_apply, halg, ← sub_smul] using h
   rw [hessian_heatSolution_eq_cancelled_integral ht hf hM x,
     hessian_heatSolution_eq_common_cancelled_integral ht hf hM x z]
   simp_rw [smul_sub]
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:312:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 034-segment-bound — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 034-segment-bound.lean
@@ -1,4 +1,5 @@
 import Poincare.Global.HeatDuhamelHessianDifferentiation
+import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
\u0020
 set_option autoImplicit false
\u0020
@@ -359,4 +360,29 @@
   simp_rw [smul_sub]
   rw [integral_sub (integrable_cancelled_hessian ht hf hM x) hij]
\u0020
+/-- A translated Hessian difference is bounded by the third derivative along its segment. -/
+theorem norm_hessian_translation_le (t : ℝ) (y w : E) :
+    ‖Hess t (y + w) - Hess t y‖ ≤
+      ∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖ := by
+  have hH : ContDiff ℝ 1 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
+  have hD : Continuous (Third t) := (hH.fderiv_right (m := 0) (by norm_num)).continuous
+  have hline (r : ℝ) : HasDerivAt (fun q : ℝ => y + q • w) w r := by
+    simpa only [one_smul] using ((hasDerivAt_id r).smul_const w).const_add y
+  have hd (r : ℝ) : HasDerivAt (fun q : ℝ => Hess t (y + q • w))
+      (Third t (y + r • w) w) r :=
+    ((hH.differentiable (by norm_num) (y + r • w)).hasFDerivAt).comp_hasDerivAt r (hline r)
+  have hbound : Continuous (fun r : ℝ => ‖Third t (y + r • w)‖ * ‖w‖) :=
+    (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.mul continuous_const
+  have h := intervalIntegral.norm_sub_le_integral_of_norm_deriv_le_of_le
+    (f := fun r : ℝ => Hess t (y + r • w)) zero_le_one
+    (hH.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
+    (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
+    (Filter.Eventually.of_forall fun r _ => by
+      rw [(hd r).deriv]
+      exact ContinuousLinearMap.le_opNorm _ _)
+    (hbound.intervalIntegrable 0 1)
+  simpa only [one_smul, zero_smul, add_zero] using h
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:1:0: error: object file '/private/tmp/poincare-workers/heat-duhamel-hessian-spatial-holder/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.olean' of module Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral does not exist
```

</details>

<details>
<summary>Probe 035-segment-ftc — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 035-segment-ftc.lean
@@ -1,5 +1,4 @@
 import Poincare.Global.HeatDuhamelHessianDifferentiation
-import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
\u0020
 set_option autoImplicit false
\u0020
@@ -375,14 +374,15 @@
     ((hH.differentiable (by norm_num) (y + r • w)).hasFDerivAt).comp_hasDerivAt r (hline r)
   have hbound : Continuous (fun r : ℝ => ‖Third t (y + r • w)‖ * ‖w‖) :=
     (hD.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.mul continuous_const
-  have h := intervalIntegral.norm_sub_le_integral_of_norm_deriv_le_of_le
-    (f := fun r : ℝ => Hess t (y + r • w)) zero_le_one
-    (hH.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
-    (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
-    (Filter.Eventually.of_forall fun r _ => by
-      rw [(hd r).deriv]
-      exact ContinuousLinearMap.le_opNorm _ _)
+  have hi : IntervalIntegrable (fun r : ℝ => Third t (y + r • w) w) volume 0 1 :=
+    ((hD.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
+      continuous_const).intervalIntegrable 0 1
+  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
+    (fun r _ => hd r) hi
+  simp only [one_smul, zero_smul, add_zero] at he
+  rw [← he]
+  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
+    (Filter.Eventually.of_forall fun r _ => ContinuousLinearMap.le_opNorm _ _)
     (hbound.intervalIntegrable 0 1)
-  simpa only [one_smul, zero_smul, add_zero] using h
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:312:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 036-translated-third — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 036-translated-third.lean
@@ -1,4 +1,5 @@
 import Poincare.Global.HeatDuhamelHessianDifferentiation
+import Mathlib.Analysis.MeanInequalitiesPow
\u0020
 set_option autoImplicit false
\u0020
@@ -385,4 +386,40 @@
     (Filter.Eventually.of_forall fun r _ => ContinuousLinearMap.le_opNorm _ _)
     (hbound.intervalIntegrable 0 1)
\u0020
+/-- Translating the third derivative costs one unweighted moment in addition to its weighted moment. -/
+theorem weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (ht : 0 < t) (w : E) :
+    Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) ∧
+    (∫ y : E, ‖Third t (y + w)‖ * ‖y‖ ^ α) ≤
+      (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖) := by
+  have hiα := (integrable_weighted_third hα hα1 ht).comp_add_right w
+  have hi0 : Integrable (fun y : E => ‖Third t y‖) := by
+    simpa using integrable_weighted_third (α := 0) (by norm_num) (by norm_num) ht
+  have hiw := (hi0.comp_add_right w).const_mul (‖w‖ ^ α)
+  have hmajor := hiα.add hiw
+  have hb (y : E) : ‖Third t (y + w)‖ * ‖y‖ ^ α ≤
+      ‖Third t (y + w)‖ * ‖y + w‖ ^ α + ‖w‖ ^ α * ‖Third t (y + w)‖ := by
+    have hnorm : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
+      simpa only [add_sub_cancel_right] using norm_sub_le (y + w) w
+    have hp : ‖y‖ ^ α ≤ ‖y + w‖ ^ α + ‖w‖ ^ α :=
+      (Real.rpow_le_rpow (norm_nonneg y) hnorm hα).trans
+        (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hα hα1)
+    calc
+      _ ≤ ‖Third t (y + w)‖ * (‖y + w‖ ^ α + ‖w‖ ^ α) :=
+        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
+      _ = _ := by ring
+  have hD : Continuous (Third t) :=
+    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)).continuous
+  have hi : Integrable (fun y : E => ‖Third t (y + w)‖ * ‖y‖ ^ α) :=
+    hmajor.mono' ((hD.comp (continuous_id.add continuous_const)).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+      (Filter.Eventually.of_forall fun y => by
+        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+        exact hb y)
+  refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
+  rw [integral_add hiα hiw, integral_const_mul,
+    integral_add_right_eq_self, integral_add_right_eq_self]
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:422:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : E),
    ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖ * ‖a + w‖ ^ α +
      ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖
in the target expression
  ∫ (x : E),
      ((fun t_1 =>
            ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
              ‖t_1 + w‖ ^ α) +
          fun x =>
          ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
        x =
    (∫ (y : E),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖ * ‖y‖ ^ α) +
      ‖w‖ ^ α * ∫ (y : E), ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖

α t : ℝ
hα : 0 ≤ α
hα1 : α ≤ 1
ht : 0 < t
w : E
hiα :
  Integrable
    (fun t_1 =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
        ‖t_1 + w‖ ^ α)
    volume
hi0 :
  Integrable (fun y => ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖)
    volume
hiw :
  Integrable
    (fun x =>
      ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
    volume
hmajor :
  Integrable
    ((fun t_1 =>
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
          ‖t_1 + w‖ ^ α) +
      fun x =>
      ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
    volume
hb :
  ∀ (y : E),
    ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y‖ ^ α ≤
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y + w‖ ^ α +
        ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖
hD : Continuous ((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t)
hi :
  Integrable
    (fun y =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y‖ ^ α)
    volume
⊢ ∫ (x : E),
      ((fun t_1 =>
            ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
              ‖t_1 + w‖ ^ α) +
          fun x =>
          ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
        x =
    (∫ (y : E),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖ * ‖y‖ ^ α) +
      ‖w‖ ^ α * ∫ (y : E), ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖
```

</details>

<details>
<summary>Probe 037-translated-third — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 037-translated-third.lean
@@ -419,6 +419,7 @@
         rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
         exact hb y)
   refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
+  simp only [Pi.add_apply]
   rw [integral_add hiα hiw, integral_const_mul,
     integral_add_right_eq_self, integral_add_right_eq_self]
\u0020
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:424:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : ?m.1013), ?f (x + ?g) ∂?m.1018
in the target expression
  (∫ (a : E),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖ *
          ‖a + w‖ ^ α) +
      ‖w‖ ^ α *
        ∫ (a : E), ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖ =
    (∫ (y : E), ‖fderiv ℝ (fun x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) y‖ * ‖y‖ ^ α) +
      ‖w‖ ^ α * ∫ (y : E), ‖fderiv ℝ (fun x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) y‖

α t : ℝ
hα : 0 ≤ α
hα1 : α ≤ 1
ht : 0 < t
w : E
hiα :
  Integrable
    (fun t_1 =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
        ‖t_1 + w‖ ^ α)
    volume
hi0 :
  Integrable (fun y => ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t y‖)
    volume
hiw :
  Integrable
    (fun x =>
      ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
    volume
hmajor :
  Integrable
    ((fun t_1 =>
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (t_1 + w)‖ *
          ‖t_1 + w‖ ^ α) +
      fun x =>
      ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (x + w)‖)
    volume
hb :
  ∀ (y : E),
    ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y‖ ^ α ≤
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y + w‖ ^ α +
        ‖w‖ ^ α * ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖
hD : Continuous ((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t)
hi :
  Integrable
    (fun y =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (y + w)‖ * ‖y‖ ^ α)
    volume
⊢ (∫ (a : E),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖ *
          ‖a + w‖ ^ α) +
      ‖w‖ ^ α *
        ∫ (a : E), ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t) x) t (a + w)‖ =
    (∫ (y : E), ‖fderiv ℝ (fun x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) y‖ * ‖y‖ ^ α) +
      ‖w‖ ^ α * ∫ (y : E), ‖fderiv ℝ (fun x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) y‖
```

</details>

<details>
<summary>Probe 038-translated-third — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 038-translated-third.lean
@@ -421,6 +421,7 @@
   refine ⟨hi, (integral_mono hi hmajor hb).trans_eq ?_⟩
   simp only [Pi.add_apply]
   rw [integral_add hiα hiw, integral_const_mul,
-    integral_add_right_eq_self, integral_add_right_eq_self]
+    integral_add_right_eq_self (fun y : E => ‖Third t y‖ * ‖y‖ ^ α) w,
+    integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 039-dependencies — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/holder-evidence/Dependencies.lean`.

```diff
--- previous-probe
+++ 039-dependencies.lean
@@ -425,3 +425,15 @@
     integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let mut count := 0
+  for (n, _) in env.constants.toList do
+    if n.toString.startsWith "Poincare.HeatDuhamelHessianSpatialHolder." && !n.isInternal then
+      let axs ← liftCoreM (collectAxioms n)
+      logInfo m!"{n}: {axs}"
+      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected dependency set for {n}"
+      count := count + 1
+  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
/private/tmp/holder-evidence/Dependencies.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_apply: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin_1: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCY_SCAN declarations=20 PASS
```

</details>

<details>
<summary>Probe 040-product-integrability — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 040-product-integrability.lean
@@ -424,16 +424,36 @@
     integral_add_right_eq_self (fun y : E => ‖Third t y‖ * ‖y‖ ^ α) w,
     integral_add_right_eq_self (fun y : E => ‖Third t y‖) w]
\u0020
+/-- The segment parameter and the weighted spatial third derivative form an integrable product. -/
+theorem integrable_segment_weighted_third {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
+    Integrable (fun p : ℝ × E => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α)
+      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
+  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
+  have hD : Continuous (Third t) :=
+    ((((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).fderiv_right
+        (m := 0) (by norm_num)).continuous
+  have hg : Continuous G :=
+    (hD.comp (continuous_snd.add (continuous_fst.smul continuous_const))).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
+  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
+  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
+  refine ⟨Filter.Eventually.of_forall fun r => (weighted_third_translation hα hα1 ht (r • w)).1, ?_⟩
+  have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
+  refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
+  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
+  have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
+    apply integral_congr_ae
+    exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
+      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+  rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
+  have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
+    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
+    rw [norm_smul_of_nonneg hr.1]
+    nlinarith [norm_nonneg w, hr.2]
+  exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
+    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
+      (integral_nonneg (fun y => norm_nonneg _))))
+
 end Poincare.HeatDuhamelHessianSpatialHolder
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let mut count := 0
-  for (n, _) in env.constants.toList do
-    if n.toString.startsWith "Poincare.HeatDuhamelHessianSpatialHolder." && !n.isInternal then
-      let axs ← liftCoreM (collectAxioms n)
-      logInfo m!"{n}: {axs}"
-      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected dependency set for {n}"
-      count := count + 1
-  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 041-weighted-hessian-translation — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 041-weighted-hessian-translation.lean
@@ -456,4 +456,55 @@
     (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
       (integral_nonneg (fun y => norm_nonneg _))))
\u0020
+/-- Integrating the segment estimate gives a weighted translation estimate for the Hessian. -/
+theorem weighted_hessian_translation {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) :
+    Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ∧
+    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
+      ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := by
+  let G : ℝ × E → ℝ := fun p => ‖Third t (p.2 + p.1 • w)‖ * ‖p.2‖ ^ α
+  let C := (∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) + ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)
+  have hg : Integrable G ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
+    integrable_segment_weighted_third hα hα1 ht w
+  have hiMajor := hg.integral_prod_right.const_mul ‖w‖
+  have hb (y : E) : ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α ≤
+      ‖w‖ * (∫ r in Icc (0 : ℝ) 1, G (r, y)) := by
+    calc
+      _ ≤ (∫ r in (0 : ℝ)..1, ‖Third t (y + r • w)‖ * ‖w‖) * ‖y‖ ^ α :=
+        mul_le_mul_of_nonneg_right (norm_hessian_translation_le t y w)
+          (Real.rpow_nonneg (norm_nonneg _) _)
+      _ = _ := by
+        change _ = ‖w‖ * (∫ r in Icc (0 : ℝ) 1, ‖Third t (y + r • w)‖ * ‖y‖ ^ α)
+        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
+          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
+        ring
+  have hH : Continuous (Hess t) :=
+    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
+  have hi : Integrable (fun y : E => ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) :=
+    hiMajor.mono' (((hH.comp (continuous_id.add continuous_const)).sub hH).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+      (Filter.Eventually.of_forall fun y => by
+        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+        exact hb y)
+  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
+  rw [integral_const_mul]
+  have hswap : (∫ y : E, ∫ r in Icc (0 : ℝ) 1, G (r, y)) =
+      ∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y) :=
+    (integral_integral_swap hg).symm
+  rw [hswap]
+  apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
+  calc
+    (∫ r in Icc (0 : ℝ) 1, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc (0 : ℝ) 1, C := by
+      apply integral_mono_ae hg.integral_prod_left (integrable_const C)
+      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
+      have hwp : ‖r • w‖ ^ α ≤ ‖w‖ ^ α := by
+        apply Real.rpow_le_rpow (norm_nonneg _) _ hα
+        rw [norm_smul_of_nonneg hr.1]
+        nlinarith [norm_nonneg w, hr.2]
+      exact (weighted_third_translation hα hα1 ht (r • w)).2.trans
+        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwp
+          (integral_nonneg (fun y => norm_nonneg _))))
+    _ = C := by simp
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 042-far-kernel — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 042-far-kernel.lean
@@ -507,4 +507,35 @@
           (integral_nonneg (fun y => norm_nonneg _))))
     _ = C := by simp
\u0020
+/-- Beyond the spatial time scale, both translation terms have the same time power. -/
+theorem weighted_hessian_translation_far {α t : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (w : E) (hw : ‖w‖ ^ 2 ≤ t) :
+    (∫ y : E, ‖Hess t (y + w) - Hess t y‖ * ‖y‖ ^ α) ≤
+      ‖w‖ * t ^ (α / 2 - 3 / 2) *
+        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
+  have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
+    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (half_nonneg hα)
+    rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
+    have he : (2 : ℝ) * (α / 2) = α := by ring
+    simpa only [Nat.cast_ofNat, he] using h
+  have hzero : (∫ y : E, ‖Third t y‖) =
+      t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖) := by
+    simpa using weighted_third_integral ht 0
+  have hJ : 0 ≤ ∫ y : E, ‖Third 1 y‖ := integral_nonneg (fun y => norm_nonneg _)
+  calc
+    _ ≤ ‖w‖ * ((∫ y : E, ‖Third t y‖ * ‖y‖ ^ α) +
+        ‖w‖ ^ α * (∫ y : E, ‖Third t y‖)) := (weighted_hessian_translation hα hα1 ht w).2
+    _ = ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
+        ‖w‖ ^ α * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
+      rw [weighted_third_integral ht, hzero]
+    _ ≤ ‖w‖ * (t ^ (α / 2 - 3 / 2) * (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) +
+        t ^ (α / 2) * (t ^ (-(3 / 2 : ℝ)) * (∫ y : E, ‖Third 1 y‖))) := by
+      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
+      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hp
+        (mul_nonneg (Real.rpow_nonneg ht.le _) hJ))
+    _ = _ := by
+      rw [← mul_assoc (t ^ (α / 2)), ← Real.rpow_add ht]
+      rw [show α / 2 + -(3 / 2 : ℝ) = α / 2 - 3 / 2 by ring]
+      ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:517:52: error(lean.unknownIdentifier): Unknown identifier `half_nonneg`
```

</details>

<details>
<summary>Probe 043-far-kernel — exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 043-far-kernel.lean
@@ -514,7 +514,7 @@
       ‖w‖ * t ^ (α / 2 - 3 / 2) *
         ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
   have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
-    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (half_nonneg hα)
+    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (div_nonneg hα (by norm_num))
     rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
     have he : (2 : ℝ) * (α / 2) = α := by ring
     simpa only [Nat.cast_ofNat, he] using h
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:517:67: error: unsolved goals
α t : ℝ
hα : 0 ≤ α
hα1 : α ≤ 1
ht : 0 < t
w : E
hw : ‖w‖ ^ 2 ≤ t
⊢ 0 ≤ ?m.298
```

</details>

<details>
<summary>Probe 044-far-kernel — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 044-far-kernel.lean
@@ -514,7 +514,7 @@
       ‖w‖ * t ^ (α / 2 - 3 / 2) *
         ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) := by
   have hp : ‖w‖ ^ α ≤ t ^ (α / 2) := by
-    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (div_nonneg hα (by norm_num))
+    have h := Real.rpow_le_rpow (sq_nonneg ‖w‖) hw (show 0 ≤ α / 2 by linarith)
     rw [← Real.rpow_natCast_mul (norm_nonneg w)] at h
     have he : (2 : ℝ) * (α / 2) = α := by ring
     simpa only [Nat.cast_ofNat, he] using h
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 045-far-heat — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 045-far-heat.lean
@@ -538,4 +538,37 @@
       rw [show α / 2 + -(3 / 2 : ℝ) = α / 2 - 3 / 2 by ring]
       ring
\u0020
+/-- The far-time spatial heat Hessian increment is linear in the observation distance. -/
+theorem norm_heat_hessian_difference_far_le {α t M K : ℝ}
+    (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) (hK0 : 0 ≤ K)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hscale : ‖x - z‖ ^ 2 ≤ t) :
+    ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x -
+      fderiv ℝ (fderiv ℝ (heatSolution t f)) z‖ ≤
+      ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
+        K * ‖x - z‖ * t ^ (α / 2 - 3 / 2) := by
+  rw [hessian_heatSolution_difference_eq_integral ht hf hM x z]
+  have hi := (weighted_hessian_translation hα hα1 ht (z - x)).1.const_mul K
+  have hb (y : E) : ‖(f (x - y) - f x) • (Hess t y - Hess t (y + (z - x)))‖ ≤
+      K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := by
+    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
+      have he : x - y - x = -y := by abel
+      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
+    calc
+      _ ≤ ‖f (x - y) - f x‖ * ‖Hess t y - Hess t (y + (z - x))‖ :=
+        norm_real_smul_continuousLinearMap_two_le _ _
+      _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y - Hess t (y + (z - x))‖ :=
+        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
+      _ = _ := by rw [norm_sub_rev (Hess t y)]; ring
+  calc
+    _ ≤ ∫ y : E, K * (‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) :=
+      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
+    _ = K * (∫ y : E, ‖Hess t (y + (z - x)) - Hess t y‖ * ‖y‖ ^ α) := integral_const_mul _ _
+    _ ≤ K * (‖z - x‖ * t ^ (α / 2 - 3 / 2) *
+        ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖))) :=
+      mul_le_mul_of_nonneg_left (weighted_hessian_translation_far hα hα1 ht (z - x)
+        (by simpa only [norm_sub_rev z x] using hscale)) hK0
+    _ = _ := by rw [norm_sub_rev z x]; ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 046-far-duhamel — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 046-far-duhamel.lean
@@ -571,4 +571,68 @@
         (by simpa only [norm_sub_rev z x] using hscale)) hK0
     _ = _ := by rw [norm_sub_rev z x]; ring
\u0020
+/-- The far part of the cancelled Duhamel Hessian has the spatial Hölder bound. -/
+theorem far_hessian_difference_le {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x z : E) (hρ : 0 < ‖x - z‖) (hscale : ‖x - z‖ ^ 2 < t) :
+    ‖(∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
+        (f (s, x - y) - f (s, x)) • Hess (t - s) y) -
+      (∫ s in (0 : ℝ)..(t - ‖x - z‖ ^ 2), ∫ y : E,
+        (f (s, z - y) - f (s, z)) • Hess (t - s) y)‖ ≤
+      (((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) *
+        (2 / (1 - α))) * K * ‖x - z‖ ^ α := by
+  let a := t - ‖x - z‖ ^ 2
+  let J := (∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)
+  let F := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
+  have ha : 0 < a := sub_pos.mpr hscale
+  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
+  have hρ2 : 0 < ‖x - z‖ ^ 2 := sq_pos_of_pos hρ
+  have hJ : 0 ≤ J := add_nonneg
+    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+    (integral_nonneg (fun y => norm_nonneg _))
+  have hFi (p : E) : IntervalIntegrable (fun s => F s p) volume 0 a :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
+      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
+        (Ioo_subset_Ioo le_rfl hat))
+  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 3 / 2)) volume (‖x - z‖ ^ 2) t := by
+    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
+    rw [uIcc_of_le hscale.le]
+    intro hz
+    exact (not_le.mpr hρ2) hz.1
+  have hiB : IntervalIntegrable
+      (fun s : ℝ => J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2)) volume 0 a := by
+    have h := (hip.comp_sub_left t).symm
+    simp only [sub_self] at h
+    exact h.const_mul (J * K * ‖x - z‖)
+  have hbound : ‖∫ s in (0 : ℝ)..a, F s x - F s z‖ ≤
+      ∫ s in (0 : ℝ)..a, J * K * ‖x - z‖ * (t - s) ^ (α / 2 - 3 / 2) := by
+    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
+    refine Filter.Eventually.of_forall fun s hs => ?_
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht.2⟩
+    have hsτ : ‖x - z‖ ^ 2 ≤ t - s := by dsimp [a] at hs; linarith [hs.2]
+    have hτ : 0 < t - s := hρ2.trans_le hsτ
+    have hfc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
+    dsimp only [F]
+    rw [← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs x,
+      ← hessian_heatSolution_eq_cancelled_integral hτ hfc.aestronglyMeasurable hMs z]
+    exact norm_heat_hessian_difference_far_le hα.le hα1.le hτ hK0
+      hfc.aestronglyMeasurable hMs (hK s hsT) x z hsτ
+  change ‖(∫ s in (0 : ℝ)..a, F s x) - (∫ s in (0 : ℝ)..a, F s z)‖ ≤ _
+  rw [← intervalIntegral.integral_sub (hFi x) (hFi z)]
+  refine hbound.trans ?_
+  rw [intervalIntegral.integral_const_mul]
+  calc
+    (J * K * ‖x - z‖) * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2)) =
+        (J * K) * (‖x - z‖ * (∫ s in (0 : ℝ)..a, (t - s) ^ (α / 2 - 3 / 2))) := by ring
+    _ ≤ (J * K) * ((2 / (1 - α)) * ‖x - z‖ ^ α) :=
+      mul_le_mul_of_nonneg_left (far_time_power_integral_le hα1 hρ hscale.le) (mul_nonneg hJ hK0)
+    _ = _ := by ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 047-assembly — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 047-assembly.lean
@@ -635,4 +635,82 @@
       mul_le_mul_of_nonneg_left (far_time_power_integral_le hα1 hρ hscale.le) (mul_nonneg hJ hK0)
     _ = _ := by ring
\u0020
+/-- The spatial Hölder estimate for the actual Duhamel Hessian. -/
+theorem duhamel_hessian_spatial_holder :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ∀ t ∈ Icc 0 T, ∀ x z : E,
+    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α := by
+  intro α hα hα1
+  let N := 2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
+  let F := ((∫ y : E, ‖Third 1 y‖ * ‖y‖ ^ α) + (∫ y : E, ‖Third 1 y‖)) * (2 / (1 - α))
+  have hN : 0 ≤ N := mul_nonneg
+    (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
+      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
+    (div_nonneg (by norm_num) hα.le)
+  have hF : 0 ≤ F := mul_nonneg
+    (add_nonneg (integral_nonneg (fun y =>
+      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+      (integral_nonneg (fun y => norm_nonneg _)))
+    (div_nonneg (by norm_num) (by linarith))
+  refine ⟨max 1 (N + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro T _ _ f M K _ hK0 hf hM hK
+  dsimp only
+  intro t ht x z
+  have hC : N + F ≤ max 1 (N + F) := le_max_right _ _
+  have hpow : 0 ≤ ‖x - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
+  suffices hraw : ‖fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x)) x -
+      fderiv ℝ (fderiv ℝ (fun x : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) x)) z‖ ≤ (N + F) * K * ‖x - z‖ ^ α by
+    exact hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hK0) hpow)
+  by_cases he : x = z
+  · subst z
+    simp [Real.zero_rpow hα.ne']
+  have hρ : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
+  by_cases htime : t ≤ ‖x - z‖ ^ 2
+  · exact (duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht hK0 hf hM hK x z htime).trans
+      (mul_le_mul_of_nonneg_right
+        (mul_le_mul_of_nonneg_right (show N ≤ N + F by linarith) hK0) hpow)
+  have hscale : ‖x - z‖ ^ 2 < t := lt_of_not_ge htime
+  let a := t - ‖x - z‖ ^ 2
+  let H := fun (s : ℝ) (p : E) => ∫ y : E, (f (s, p - y) - f (s, p)) • Hess (t - s) y
+  have ha : 0 < a := sub_pos.mpr hscale
+  have hat : a ≤ t := sub_le_self t (sq_nonneg _)
+  have h0t (p : E) : IntervalIntegrable (fun s => H s p) volume 0 t :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
+      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK p)
+  have h0a (p : E) : IntervalIntegrable (fun s => H s p) volume 0 a :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
+      ((integrableOn_cancelled_hessian_time hα hα1 ht hf hK p).mono_set
+        (Ioo_subset_Ioo le_rfl hat))
+  have hsplit (p : E) : (∫ s in (0 : ℝ)..t, H s p) =
+      (∫ s in (0 : ℝ)..a, H s p) + (∫ s in a..t, H s p) :=
+    (intervalIntegral.integral_add_adjacent_intervals (h0a p) ((h0a p).symm.trans (h0t p))).symm
+  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
+    hessian_duhamel_eq_integral hα hα1 ht hf hM hK z]
+  change ‖(∫ s in (0 : ℝ)..t, H s x) - (∫ s in (0 : ℝ)..t, H s z)‖ ≤ _
+  rw [hsplit x, hsplit z]
+  have hnear : ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ ≤ N * K * ‖x - z‖ ^ α := by
+    apply near_hessian_difference_le hα hα1 hK0 hat
+    · intro s hs
+      exact hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht.2⟩
+    · dsimp only [a]
+      linarith
+  have hfar : ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ ≤ F * K * ‖x - z‖ ^ α :=
+    far_hessian_difference_le hα hα1 ht hK0 hf hM hK x z hρ hscale
+  calc
+    _ = ‖((∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)) +
+        ((∫ s in a..t, H s x) - (∫ s in a..t, H s z))‖ := by congr 1; abel
+    _ ≤ ‖(∫ s in (0 : ℝ)..a, H s x) - (∫ s in (0 : ℝ)..a, H s z)‖ +
+        ‖(∫ s in a..t, H s x) - (∫ s in a..t, H s z)‖ := norm_add_le _ _
+    _ ≤ F * K * ‖x - z‖ ^ α + N * K * ‖x - z‖ ^ α := add_le_add hfar hnear
+    _ = (N + F) * K * ‖x - z‖ ^ α := by ring
+
 end Poincare.HeatDuhamelHessianSpatialHolder
```

Actual output:

```text
Try this:
  [apply] ring_nf
\u0020\u0020
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
\u0020\u0020\u0020\u0020
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:313:8: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Probe 048-clean-gate — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`.

```diff
--- previous-probe
+++ 048-clean-gate.lean
@@ -51,7 +51,7 @@
     innerSL_apply_apply] at h
   rw [h]
   simp only [heatKernel, real_inner_comm]
-  ring
+  ring_nf
\u0020
 /-- The unit-time third derivative has a cubic Gaussian envelope. -/
 theorem norm_third_one_le (x : E) :
@@ -228,7 +228,6 @@
   rw [he] at hb
   exact hb
\u0020
-set_option maxHeartbeats 800000 in
 /-- The near part of the spatial increment has the required Hölder power. -/
 theorem near_hessian_difference_le {α K a t : ℝ}
     (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hat : a ≤ t)
@@ -310,7 +309,7 @@
         have hden : 1 - α ≠ 0 := by linarith
         have hden' : α / 2 - 3 / 2 + 1 ≠ 0 := hq.ne
         field_simp [hρ.ne', hden, hden', show -1 + α ≠ 0 by linarith]
-        <;> ring_nf
+        ring_nf
         all_goals
           have hi := mul_inv_cancel₀ (show -1 + α ≠ 0 by linarith)
           nlinarith only [hi]
```

Actual output:

```text
```

</details>

<details>
<summary>Probe 049-final-dependencies — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/holder-evidence/FinalDependencies.lean`.

```diff
--- previous-probe
+++ 049-final-dependencies.lean
@@ -713,3 +713,41 @@
     _ = (N + F) * K * ‖x - z‖ ^ α := by ring
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_apply
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin_1
+#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let mut count := 0
+  for (n, _) in env.constants.toList do
+    if n.toString.startsWith "Poincare.HeatDuhamelHessianSpatialHolder." && !n.isInternal then
+      let axs ← liftCoreM (collectAxioms n)
+      logInfo m!"{n}: {axs}"
+      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected dependency set for {n}"
+      count := count + 1
+  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
```

Actual output:

```text
'Poincare.HeatDuhamelHessianSpatialHolder.third_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_apply: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin_1: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCY_SCAN declarations=26 PASS
```

</details>

<details>
<summary>Probe 050-frozen-target — exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/holder-evidence/ExactTarget.lean`.

```diff
--- previous-probe
+++ 050-frozen-target.lean
@@ -713,41 +713,19 @@
     _ = (N + F) * K * ‖x - z‖ ^ α := by ring
\u0020
 end Poincare.HeatDuhamelHessianSpatialHolder
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_apply
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin_1
-#print axioms Poincare.HeatDuhamelHessianSpatialHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let mut count := 0
-  for (n, _) in env.constants.toList do
-    if n.toString.startsWith "Poincare.HeatDuhamelHessianSpatialHolder." && !n.isInternal then
-      let axs ← liftCoreM (collectAxioms n)
-      logInfo m!"{n}: {axs}"
-      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected dependency set for {n}"
-      count := count + 1
-  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
+
+namespace FrozenTargetProbe
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+example :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ∀ t ∈ Icc 0 T, ∀ x z : E,
+    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α := Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder
+end FrozenTargetProbe
```

Actual output:

```text
```

</details>

<details>
<summary>Source-name grep inventory</summary>

The following declaration-line grep searches the identifiers used by the final source in the repository and pinned Mathlib. Generated additive aliases also have their multiplicative source in `Mathlib/MeasureTheory/Group/Integral.lean`. All final identifiers additionally elaborate in the focused Lean gate.

Command: `rg -n --glob '*.lean' '^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|alias|class|structure|instance)\s+(?:[A-Za-z][A-Za-z0-9_]*\.)*(?:ClosedSmoothModel|HeatDuhamelHessianDifferentiation|HeatDuhamelHessianSpatialHolder|Ioo_subset_Ioo|MeanInequalitiesPow|add|add_apply|add_le_add|add_nonneg|add_sub_cancel_right|add_zero|ae_restrict_mem|aestronglyMeasurable|all_goals|by_cases|cast_ofNat|clm_apply|comp|comp_add_right|comp_apply|comp_continuous|comp_hasDerivAt|comp_sub_left|conj_trivial|const_add|const_mul|contDiff_heatKernel_spatial|continuous_const|continuous_id|continuous_norm|continuous_rpow_const|differentiable|div_const|div_eq_mul_inv|div_nonneg|duhamel_hessian_spatial_holder|duhamel_hessian_spatial_holder_of_time_le_dist_sq|exp|exp_add|far_hessian_difference_le|far_time_power_integral_le|fderiv_right|field_simp|filter_upwards|finrank_euclideanSpace_fin|flip_apply|hasDerivAt_id|hasFDerivAt_const|hasFDerivAt_heatKernel_spatial|heatKernel|heatKernel_nonneg|heatKernel_sq_smul|heatSolution|hessian_duhamel_eq_integral|hessian_heatSolution_difference_eq_integral|hessian_heatSolution_eq_cancelled_integral|hessian_heatSolution_eq_common_cancelled_integral|hessian_heatSolution_eq_integral|innerSL_apply_apply|inner_smul_left|inr|integrableOn_cancelled_hessian_time|integrable_cancelled_hessian|integrable_comp_smul_iff|integrable_const|integrable_data_smul_hessian_sub|integrable_hessian|integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq|integrable_prod_iff|integrable_segment_weighted_third|integrable_weighted_third|integrable_weighted_third_one|integral_Icc_eq_integral_Ioc|integral_add|integral_add_adjacent_intervals|integral_add_right_eq_self|integral_comp_add_right|integral_comp_smul_of_nonneg|integral_comp_sub_left|integral_congr_ae|integral_const_mul|integral_eq_sub_of_hasDerivAt|integral_hessian_eq_zero|integral_integral_swap|integral_mono|integral_mono_ae|integral_mul_const|integral_nonneg|integral_of_le|integral_prod_left|integral_prod_right|integral_rpow|integral_smul|integral_sub|integral_sub_left_eq_self|intervalIntegrable|intervalIntegrable_iff_integrableOn_Ioo_of_le|intervalIntegrable_rpow|inv_ne_zero|iteratedFDeriv_two_apply|iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination|le|le_max_left|le_max_right|le_opNorm|le_rfl|lt_of_lt_of_le|lt_of_not_ge|map_zero|measurableSet_Icc|mem_univ|mono|mono_set|mpr|mul|mul_apply|mul_assoc|mul_bdd|mul_comm|mul_const|mul_inv_cancel|mul_le_mul_of_nonneg_left|mul_le_mul_of_nonneg_right|mul_le_mul_of_nonpos_right|mul_left_cancel|mul_nonneg|mul_one|mul_rpow|ne|near_hessian_difference_le|norm|norm_add_le|norm_div|norm_eq_abs|norm_heat_hessian_difference_far_le|norm_hessian_translation_le|norm_inner_le_norm|norm_integral_cancelled_hessian_near_le|norm_integral_cancelled_hessian_time_le|norm_integral_le_of_norm_le|norm_mul|norm_neg|norm_nonneg|norm_num|norm_ofNat|norm_of_nonneg|norm_real_smul_continuousLinearMap_two_le|norm_smul_le|norm_smul_of_nonneg|norm_sub_le|norm_sub_rev|norm_third_one_le|of_forall|one_ne_zero|one_pow|one_smul|opNorm_le_bound|pi|pow|pow_ne_zero|pow_nonneg|prodMk|real_inner_comm|restrict|rexp|ring_nf|rpow_add|rpow_add_le_add_rpow|rpow_add_one|rpow_le_rpow|rpow_mul|rpow_mul_gaussian_le_eight|rpow_mul_natCast|rpow_natCast_mul|rpow_nonneg|rpow_one|rpow_sub|set_option|simp_rw|smul|smul_apply|smul_const|smul_eq_mul|smul_sub|smul_zero|sq_nonneg|sq_pos_of_pos|sq_sqrt|sqrt|sqrt_eq_rpow|sqrt_pos|sub|sub_add_cancel|sub_apply|sub_const|sub_le_self|sub_self|sub_smul|sub_sub_cancel|sub_zero|symm|third_apply|third_moment_bound|third_sq_smul|trans|trans_eq|trans_le|uIcc_of_le|unique|weighted_hessian_translation|weighted_hessian_translation_far|weighted_third_integral|weighted_third_integral_sq|weighted_third_sq_smul|weighted_third_translation|zero_add|zero_apply|zero_le_one|zero_lt_one|zero_rpow|zero_smul)\b' Poincare .lake/packages/mathlib/Mathlib`. Exit 0.

```text
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:256:protected theorem map_zero (f : A →ₛₙₐ[φ] B) : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:284:theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:296:def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:304:theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:409:def inr : B →ₙₐ[R] A × B :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:247:def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:255:theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:348:theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/StrictPositivity.lean:118:protected lemma smul [Semifield 𝕜] [PartialOrder 𝕜] [Algebra 𝕜 A] [PosSMulMono 𝕜 A] {c : 𝕜}
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean:377:lemma quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean:473:protected theorem map_zero (h : QuasispectrumRestricts a f) : f 0 = 0 := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean:514:protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
.lake/packages/mathlib/Mathlib/Algebra/NeZero.lean:46:lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := one_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Unitization.lean:126:def inr [Zero R] (a : A) : Unitization R A :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean:401:theorem smul_eq_mul (x y : R) : x • y = x * y :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean:424:theorem algebraMap.smul [SMul A C] [IsScalarTower A B C] :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean:427:theorem algebraMap.smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C] :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Associated.lean:49:protected theorem symm [Monoid M] : ∀ {x y : M}, x ~ᵤ y → y ~ᵤ x
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Associated.lean:59:protected theorem trans [Monoid M] : ∀ {x y z : M}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
.lake/packages/mathlib/Mathlib/Computability/PartrecBasis.lean:98:theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
.lake/packages/mathlib/Mathlib/Computability/PartrecBasis.lean:101:theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:56:theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:91:theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:151:theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:156:theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:168:theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:173:theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:188:theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:192:theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:241:def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:364:def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:653:theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:89:def inr [Zero R] (m : M) : tsze R M :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:185:instance add [Add R] [Add M] : Add (tsze R M) :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:188:instance sub [Sub R] [Sub M] : Sub (tsze R M) :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:215:instance smul [SMul S R] [SMul S M] : SMul S (tsze R M) :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:407:instance mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M) :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:800:protected theorem mul_inv_cancel {x : tsze R M} (hx : fst x ≠ 0) : x * x⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:36:def mul : A →ₗ[R] A →ₗ[R] A :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:40:def mul' : A ⊗[R] A →ₗ[R] A :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:49:theorem mul_apply' (a b : A) : mul R A a b = a * b :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:53:theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:179:lemma mul'_comp_comm : mul' R A ∘ₗ TensorProduct.comm R A A = mul' R A := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:182:lemma mul'_comm (x : A ⊗[R] A) : mul' R A (TensorProduct.comm R A A x) = mul' R A x :=
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Config.lean:240:theorem exists_code.comp {m n} {f : List.Vector ℕ n →. ℕ} {g : Fin n → List.Vector ℕ m →. ℕ}
.lake/packages/mathlib/Mathlib/Algebra/Colimit/Ring.lean:329:protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * inv G f p = 1 := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean:153:protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean:178:def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean:186:lemma comp_apply (g : β →*₀ γ) (f : α →*₀ β) (x : α) : g.comp f x = g (f x) := rfl
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:51:theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:88:theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ → BlankRel l₂ l₁ :=
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:92:theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
.lake/packages/mathlib/Mathlib/Algebra/Colimit/Module.lean:81:instance unique [IsEmpty ι] : Unique (DirectLimit G f) :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Pi.lean:32:def pi (s : Set ι) (t : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Equiv.lean:68:def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Equiv.lean:89:def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:352:def comp {K : Type*} [Add K] {c : K} (g : H →+c[b, c] K) (f : G →+c[a, b] H) :
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:431:def smul [DistribSMul K H] (c : K) (f : G →+c[a, b] H) : G →+c[a, c • b] H where
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:102:theorem add : Nat.Primrec (unpaired (· + ·)) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:106:theorem sub : Nat.Primrec (unpaired (· - ·)) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:110:theorem mul : Nat.Primrec (unpaired (· * ·)) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:114:theorem pow : Nat.Primrec (unpaired (· ^ ·)) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:216:theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:397:theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:422:theorem PrimrecPred.comp {p : β → Prop} {f : α → β} :
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:439:theorem PrimrecRel.comp {R : β → γ → Prop} {f : α → β} {g : α → γ}
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:443:theorem PrimrecRel.comp₂ {R : γ → δ → Prop} {f : α → β → γ} {g : α → β → δ} :
.lake/packages/mathlib/Mathlib/Algebra/Regular/Basic.lean:63:theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
.lake/packages/mathlib/Mathlib/Algebra/Regular/Basic.lean:69:theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
.lake/packages/mathlib/Mathlib/Algebra/Regular/Basic.lean:75:theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
.lake/packages/mathlib/Mathlib/Algebra/Regular/Basic.lean:187:lemma IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
.lake/packages/mathlib/Mathlib/Algebra/Regular/Basic.lean:192:lemma IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/NeZero.lean:48:theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:655:theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:658:theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:662:theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @Primrec' 2 fun v => f v.head v.tail.head) {n g h}
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:673:theorem add : @Primrec' 2 fun v => v.head + v.tail.head :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:677:theorem sub : @Primrec' 2 fun v => v.head - v.tail.head := by
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:684:theorem mul : @Primrec' 2 fun v => v.head * v.tail.head :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:704:theorem sqrt : @Primrec' 1 fun v => v.head.sqrt := by
.lake/packages/mathlib/Mathlib/Algebra/Regular/Prod.lean:37:theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
.lake/packages/mathlib/Mathlib/Algebra/Regular/Prod.lean:41:theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
.lake/packages/mathlib/Mathlib/Algebra/Regular/Prod.lean:45:theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:157:def symm {f g : C ⟶ D} (h : Homotopy f g) : Homotopy g f where
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:165:def trans {e f g : C ⟶ D} (h : Homotopy e f) (k : Homotopy f g) : Homotopy e g where
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:172:def add {f₁ g₁ f₂ g₂ : C ⟶ D} (h₁ : Homotopy f₁ g₁) (h₂ : Homotopy f₂ g₂) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:180:def smul {R : Type*} [Semiring R] [Linear R V] (h : Homotopy f g) (a : R) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:209:def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:702:def symm {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) : HomotopyEquiv D C where
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:710:def trans {C D E : HomologicalComplex V c} (f : HomotopyEquiv C D) (g : HomotopyEquiv D E) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Range.lean:146:lemma restrict₀_of_ne_zero {a : A} (h : f a ≠ 0) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Range.lean:151:lemma restrict₀_eq_zero_iff {a : A} : restrict₀ f a = 0 ↔ f a = 0 := by simp [restrict₀_apply]
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Range.lean:154:lemma restrict₀_eq_one_iff {a : A} : restrict₀ f a = 1 ↔ f a = 1 := by
.lake/packages/mathlib/Mathlib/Algebra/Regular/SMul.lean:81:theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
.lake/packages/mathlib/Mathlib/Algebra/Regular/SMul.lean:105:theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
.lake/packages/mathlib/Mathlib/Algebra/Regular/SMul.lean:150:theorem pow (n : ℕ) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
.lake/packages/mathlib/Mathlib/Computability/StateTransition.lean:275:def EvalsTo.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
.lake/packages/mathlib/Mathlib/Computability/StateTransition.lean:285:def EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Divisibility.lean:124:theorem IsPrimal.mul {α} [CommMonoidWithZero α] [IsCancelMulZero α] {m n : α}
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCofiber.lean:241:noncomputable def inr : G ⟶ homotopyCofiber φ where
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:199:protected theorem one_smul : (1 : Submodule R A) • N = N := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:214:instance mul : Mul (Submodule R A) where
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:439:protected theorem mul_one : M * 1 = M := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:789:protected theorem mul_comm : M * N = N * M :=
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:251:protected lemma norm (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => ‖f x‖) := by
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:272:protected lemma GrowsPolynomially.mul {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:326:lemma GrowsPolynomially.const_mul {f : ℝ → ℝ} {c : ℝ} (hf : GrowsPolynomially f) :
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:330:protected lemma GrowsPolynomially.add {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:584:protected lemma GrowsPolynomially.pow (p : ℕ) (hf : GrowsPolynomially f)
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Degree.lean:557:lemma Monic.mul
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Degree.lean:568:lemma Monic.pow
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Defs.lean:55:theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Defs.lean:239:lemma mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:288:lemma smul_apply (a : A) (x : R[M]) (m : M) : (a • x) m = a • x m := rfl
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:438:lemma mul_apply [DecidableEq M] (x y : R[M]) (m : M) :
.lake/packages/mathlib/Mathlib/Computability/RecursiveIn.lean:212:theorem mono {O₁ O₂} (hsub : O₁ ⊆ O₂) (hf : RecursiveIn O₁ f) : RecursiveIn O₂ f :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/ComplexShapeSigns.lean:277:def TotalComplexShape.symm [TotalComplexShape c₁ c₂ c₁₂] :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean:57:lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean:74:lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
.lake/packages/mathlib/Mathlib/Computability/DFA.lean:389:theorem IsRegular.add {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/SemiDirect.lean:110:def inr : L →ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Finset.lean:66:lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Finset.lean:84:lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
.lake/packages/mathlib/Mathlib/Computability/TuringDegree.lean:79:theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h :=
.lake/packages/mathlib/Mathlib/Computability/TuringDegree.lean:94:theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
.lake/packages/mathlib/Mathlib/Computability/TuringDegree.lean:98:theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Sl2.lean:52:lemma symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/MapDomain.lean:76:protected lemma map_zero (f : R →+ S) : map f (0 : R[M]) = 0 := mapRange_zero (hf := f.map_zero)
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean:59:theorem smul_zero (a : M) : a • (0 : A) = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean:133:theorem zero_smul (m : A) : (0 : M₀) • m = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean:415:theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:388:theorem zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:426:def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:431:theorem comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:597:def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:620:def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:728:theorem zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:762:def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:767:theorem comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:803:theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:810:theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:853:theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:968:def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:993:def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:220:def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:919:protected lemma map_zero : (0 : Cochain K L n).map Φ = 0 := by cat_disch
.lake/packages/mathlib/Mathlib/Computability/Partrec.lean:449:theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
.lake/packages/mathlib/Mathlib/Computability/Partrec.lean:464:theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
.lake/packages/mathlib/Mathlib/Computability/Partrec.lean:481:theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
.lake/packages/mathlib/Mathlib/Algebra/Vertex/HVertexOperator.lean:138:def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
.lake/packages/mathlib/Mathlib/Computability/ContextFreeGrammar.lean:160:lemma Derives.trans {u v w : List (Symbol T g.NT)} (huv : g.Derives u v) (hvw : g.Derives v w) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/Prod.lean:78:def inr : L₂ →ₗ⁅R⁆ L₁ × L₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/MappingCocone.lean:55:noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subsemiring/Basic.lean:726:def restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) : s' →+* s :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subsemiring/Basic.lean:893:instance smul [SMul R' α] (S : Subsemiring R') : SMul S α :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:75:noncomputable def inr : G ⟶ mappingCone φ := homotopyCofiber.inr φ
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:91:instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:258:lemma pow_ne_zero (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 := mt eq_zero_of_pow_eq_zero h
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:260:instance NeZero.pow [NeZero a] : NeZero (a ^ n) := ⟨pow_ne_zero n NeZero.out⟩
.lake/packages/mathlib/Mathlib/Algebra/Lie/Weights/Basic.lean:245:lemma zero_apply [Nontrivial (genWeightSpace M (0 : L → R))] (x) : (0 : Weight R L M) x = 0 := rfl
.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean:76:theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean:140:theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean:177:theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
.lake/packages/mathlib/Mathlib/Control/ULiftable.lean:60:abbrev symm (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) [ULiftable f g] : ULiftable g f where
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:164:theorem zero_apply (a : L) : (0 : LieDerivation R L M) a = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:184:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:223:theorem sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:252:theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:397:noncomputable def exp (h : IsNilpotent D.toLinearMap) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/ProdHom.lean:68:def inr [DecidablePred fun x : H₀ ↦ x = 0] : H₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Parity.lean:148:lemma Odd.pow {n : ℕ} (ha : Odd a) : Odd (a ^ n) := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean:187:instance pow : Pow (WithZero α) ℕ where
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean:363:def exp (a : M) : Mᵐ⁰ := coe <| .ofAdd a
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:51:protected theorem Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:59:protected theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:86:protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:113:theorem Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:124:theorem Periodic.sub_const [SubtractionCommMonoid α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:364:theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:375:theorem Antiperiodic.sub_const [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:379:theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:390:theorem Antiperiodic.add [AddSemigroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:393:theorem Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
.lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:412:theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
.lake/packages/mathlib/Mathlib/Control/Traversable/Basic.lean:162:def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
.lake/packages/mathlib/Mathlib/Control/Traversable/Basic.lean:169:theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:249:protected def symm (e : R ≃+* S) : S ≃+* R :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:341:protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:435:protected theorem map_zero : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:130:noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/IsFormallyReal.lean:45:theorem IsSumNonzeroSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
.lake/packages/mathlib/Mathlib/Algebra/PresentedMonoid/Basic.lean:131:theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subring/Basic.lean:961:def restrict {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
.lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:165:lemma mul_le_mul_of_nonpos_right {a b c : EReal} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
.lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:461:lemma div_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean:72:alias Dvd.dvd.trans := dvd_trans
.lake/packages/mathlib/Mathlib/Algebra/Divisibility/Basic.lean:142:alias Dvd.dvd.pow := dvd_pow
.lake/packages/mathlib/Mathlib/Algebra/RingQuot.lean:84:theorem Rel.smul {r : A → A → Prop} (k : S) ⦃a b : A⦄ (h : Rel r a b) : Rel r (k • a) (k • b) := by
.lake/packages/mathlib/Mathlib/Algebra/RingQuot.lean:196:def smul [Algebra S R] (n : S) : RingQuot r → RingQuot r
.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:367:lemma sub_self {x : EReal} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) : x - x = 0 := by
.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:422:lemma add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a := by
.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:429:lemma sub_add_cancel {a : EReal} {b : Real} : a - b + b = a := by
.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:652:protected lemma mul_nonneg {a b : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:131:protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:135:protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:146:protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:150:protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:162:protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
.lake/packages/mathlib/Mathlib/Logic/Relator.lean:166:protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:175:def comp (g f : CentroidHom α) : CentroidHom α :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:186:theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:298:theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:306:theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:310:theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:314:theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:589:theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean:132:protected def mul : EReal → EReal → EReal
.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean:188:protected theorem mul_comm (x y : EReal) : x * y = y * x := by
.lake/packages/mathlib/Mathlib/Data/Ordmap/Invariants.lean:152:theorem BalancedSz.symm {l r : ℕ} : BalancedSz l r → BalancedSz r l :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:283:theorem integral_add {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:290:theorem integral_sub {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:294:theorem integral_smul [DistribSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:325:lemma integral_nonneg {f : α →ₛ F} (hf : 0 ≤ᵐ[μ] f) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:339:lemma integral_mono {f g : α →ₛ F} (h : f ≤ᵐ[μ] g) (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:432:theorem integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:435:theorem integral_smul (c : 𝕜) (f : α →₁ₛ[μ] E) : integral (c • f) = c • integral f :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:577:theorem integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:587:theorem integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:592:theorem integral_smul (c : 𝕜) (f : α →₁[μ] E) : integral (c • f) = c • integral f := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean:151:theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean:203:theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean:773:lemma QuotientMeasureEqMeasurePreimage.unique
.lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:40:lemma HasFiniteMulSupport.comp {N : Type*} [One N] {g : M → N} {f : α → M}
.lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:56:lemma HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
.lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:64:lemma HasFiniteMulSupport.mul {M : Type*} [MulOneClass M] {f g : α → M}
.lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:88:lemma HasFiniteMulSupport.pow {M : Type*} [Monoid M] {f : α → M} (hf : HasFiniteMulSupport f)
.lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:136:lemma HasFiniteMulSupport.pi {ι : Type*} [Finite α] {f : ι → α → M}
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean:311:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
.lake/packages/mathlib/Mathlib/Data/Subtype.lean:111:def restrict {α} {β : α → Type*} (p : α → Prop) (f : ∀ x, β x) (x : Subtype p) : β x.1 :=
.lake/packages/mathlib/Mathlib/Data/Subtype.lean:187:protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
.lake/packages/mathlib/Mathlib/Data/Subtype.lean:190:protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subgroup.lean:29:protected def mul : Mul (AddSubgroup R) where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.lean:36:lemma ShortComplex.zero_apply
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Measure.lean:782:theorem IsHaarMeasure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : IsHaarMeasure (c • μ) :=
.lake/packages/mathlib/Mathlib/Data/Setoid/Partition.lean:254:instance Partition.le : LE (Partitions α) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:659:theorem integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:689:theorem integral_Icc_eq_integral_Ioc : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
Poincare/Global/DifferentialSuccessorAdjacentContinuation.lean:177:theorem CrossHistorySuccessorAgreement.symm
Poincare/Global/DifferentialSuccessorAdjacentContinuation.lean:188:theorem CrossHistorySuccessorAgreement.trans
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Action.lean:46:instance add [SMulInvariantMeasure M α μ] [SMulInvariantMeasure M α ν] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Action.lean:53:instance smul [SMulInvariantMeasure M α μ] (c : ℝ≥0∞) : SMulInvariantMeasure M α (c • μ) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Action.lean:304:theorem NullMeasurableSet.smul {s} (hs : NullMeasurableSet s μ) (c : G) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean:446:def comp (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
.lake/packages/mathlib/Mathlib/Data/Setoid/Basic.lean:62:theorem symm' (r : Setoid α) : ∀ {x y}, r x y → r y x := r.iseqv.symm
.lake/packages/mathlib/Mathlib/Data/Setoid/Basic.lean:65:theorem trans' (r : Setoid α) : ∀ {x y z}, r x y → r y z → r x z := r.iseqv.trans
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean:53:def smul (c : G) : α ≃ᵐ α where
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/MeasurableEquiv.lean:68:def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:357:theorem mono {p : α → α → Prop} (hp : ∀ a b, r a b → p a b) : ∀ {a b}, ReflGen r a b → ReflGen p a b
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:406:theorem symm : SymmGen r a b → SymmGen r b a :=
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:426:theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:660:theorem TransGen.mono {p : α → α → Prop} :
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:700:theorem ReflTransGen.mono {p : α → α → Prop} : (∀ a b, r a b → p a b) →
.lake/packages/mathlib/Mathlib/Logic/Relation.lean:794:theorem mono {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) (h : EqvGen r a b) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Homology.lean:266:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
.lake/packages/mathlib/Mathlib/Data/PEquiv.lean:99:protected def symm (f : α ≃. β) : β ≃. α where
.lake/packages/mathlib/Mathlib/Data/PEquiv.lean:112:protected def trans (f : α ≃. β) (g : β ≃. γ) :
.lake/packages/mathlib/Mathlib/Data/Prod/Basic.lean:163:theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
.lake/packages/mathlib/Mathlib/Data/FP/Basic.lean:209:unsafe def add (mode : RMode) : Float → Float → Float
.lake/packages/mathlib/Mathlib/Data/FP/Basic.lean:225:unsafe def sub (mode : RMode) (f1 f2 : Float) : Float :=
.lake/packages/mathlib/Mathlib/Data/FP/Basic.lean:232:unsafe def mul (mode : RMode) : Float → Float → Float
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:237:theorem integral_add {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:244:theorem integral_add' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:267:theorem integral_sub {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:274:theorem integral_sub' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:283:theorem integral_smul [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α → G) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:290:theorem Integrable.integral_smul {R : Type*} [NormedRing R] [Module R G] [IsBoundedSMul R G]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:298:theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:302:theorem integral_mul_const {L : Type*} [RCLike L] (r : L) (f : α → L) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:309:theorem integral_congr_ae {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:315:lemma integral_congr_ae₂ {β : Type*} {_ : MeasurableSpace β} {ν : Measure β} {f g : α → β → G}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:630:lemma integral_nonneg {f : α → E} (hf : 0 ≤ f) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:645:lemma integral_mono_ae {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:653:lemma integral_mono {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:965:theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ} (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/Algebra/Symmetrized.lean:289:theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
.lake/packages/mathlib/Mathlib/Logic/Unique.lean:166:instance Pi.unique {β : α → Sort v} [∀ a, Unique (β a)] : Unique (∀ a, β a) where
.lake/packages/mathlib/Mathlib/Logic/Unique.lean:202:protected def Surjective.unique {α : Sort u} (f : α → β) (hf : Surjective f) [Unique.{u} α] :
.lake/packages/mathlib/Mathlib/Logic/Unique.lean:208:protected def Injective.unique [Inhabited α] [Subsingleton β] (hf : Injective f) : Unique α :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/FoelnerFilter.lean:114:theorem mono {l' : Filter ι} (hfoel : IsFoelner G μ l F) (hle : l' ≤ l) :
.lake/packages/mathlib/Mathlib/Data/PSigma/Order.lean:51:instance le [LT ι] [∀ i, LE (α i)] : LE (Σₗ' i, α i) :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Hom.lean:84:theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Hom.lean:124:protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R →+ M →+ M :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:98:theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:103:theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:108:theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:113:theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:118:theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:125:lemma Measurable.mul' [MeasurableMul₂ M] {f g : α → β → M} {h : α → β} (hf : Measurable ↿f)
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:130:theorem AEMeasurable.mul' [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:135:theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:185:theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:189:theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:261:theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:266:theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:545:theorem Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable g) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:552:lemma Measurable.smul' [MeasurableSMul₂ M X] {f : α → β → M} {g : α → β → X} {h : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:557:theorem AEMeasurable.smul [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:568:theorem Measurable.smul_const (hf : Measurable f) (y : X) : Measurable fun x => f x • y :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean:572:theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : X) :
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:122:def comp (f : B →⋆* C) (g : A →⋆* B) : A →⋆* C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:131:theorem comp_apply (f : B →⋆* C) (g : A →⋆* B) (a : A) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:272:def trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : A ≃⋆* C :=
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:82:theorem smul {c : K} (hc : c ≠ 0) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Basic.lean:80:def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:163:def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:172:theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:225:theorem zero_apply (a : A) : (0 : A →⋆ₙ+* B) a = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:390:def trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:92:def add : LeftHomologyMapData (φ + φ') h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:200:def add : RightHomologyMapData (φ + φ') h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:310:def add : HomologyMapData (φ + φ') h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:414:def symm (h : Homotopy φ₁ φ₂) : Homotopy φ₂ φ₁ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:436:def trans (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃) : Homotopy φ₁ φ₃ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:447:def add (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ + φ₃) (φ₂ + φ₄) where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:458:def sub (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ - φ₃) (φ₂ - φ₄) where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:492:def comp (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:708:def symm (e : HomotopyEquiv S₁ S₂) : HomotopyEquiv S₂ S₁ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:716:def trans (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Linear.lean:65:def smul (a : R) : LeftHomologyMapData (a • φ) h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Linear.lean:119:def smul (a : R) : RightHomologyMapData (a • φ) h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Linear.lean:173:def smul (a : R) : HomologyMapData (a • φ) h₁ h₂ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Linear.lean:201:def Homotopy.smul {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) (a : R) :
.lake/packages/mathlib/Mathlib/Algebra/Star/StarProjection.lean:90:theorem add [NonUnitalNonAssocSemiring R] [StarRing R]
.lake/packages/mathlib/Mathlib/Algebra/Star/StarProjection.lean:99:theorem mul [NonUnitalSemiring R] [StarRing R]
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:114:theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0 := rfl
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:120:theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:124:theorem sub_apply [∀ i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:128:theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)]
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean:406:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:402:theorem integral_add {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:407:theorem integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:468:theorem integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:478:theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:298:theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:307:theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:458:protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:482:protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
.lake/packages/mathlib/Mathlib/Logic/Function/CompTypeclasses.lean:54:theorem comp {M N P : Type*}
.lake/packages/mathlib/Mathlib/Logic/Function/CompTypeclasses.lean:64:lemma comp_apply {M N P : Type*}
.lake/packages/mathlib/Mathlib/Data/Matrix/Composition.lean:37:def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:282:theorem intervalIntegrable {t : ℝ} (h₁f : Function.Periodic f T)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:332:theorem intervalIntegrable₀ (h₁f : Function.Periodic f T) (hT : T ≠ 0)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1149:theorem integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
.lake/packages/mathlib/Mathlib/Logic/Function/Defs.lean:59:theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:82:theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:222:def trans (ab : α ≃ᵐ β) (bc : β ≃ᵐ γ) : α ≃ᵐ γ where
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:230:def symm (ab : α ≃ᵐ β) : β ≃ᵐ α where
.lake/packages/mathlib/Mathlib/Algebra/Module/Lattice.lean:88:instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:140:theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NoAtoms μ]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:149:theorem MeasureTheory.Integrable.intervalIntegrable (hf : Integrable f μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:154:theorem MeasureTheory.IntegrableOn.intervalIntegrable (hf : IntegrableOn f [[a, b]] μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:199:theorem trans {a b c : ℝ} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:229:theorem norm {f : ℝ → E} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (‖f ·‖) μ a b :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:246:theorem mono (hf : IntervalIntegrable f ν a b) (h1 : [[c, d]] ⊆ [[a, b]]) (h2 : μ ≤ ν) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:253:theorem mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] ⊆ [[a, b]]) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:261:theorem mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d ⊆ Ι a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:287:protected theorem aestronglyMeasurable (h : IntervalIntegrable f μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:292:protected theorem aestronglyMeasurable' (h : IntervalIntegrable f μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:307:theorem smul {R : Type*} [NormedAddCommGroup R] [SMulZeroClass R E] [IsBoundedSMul R E] {f : ℝ → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:313:theorem add [ContinuousAdd ε] (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:318:theorem sub {f g : ℝ → E} (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:352:theorem const_mul {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:357:theorem mul_const {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:380:theorem div_const {𝕜 : Type*} {f : ℝ → 𝕜} [NormedDivisionRing 𝕜] (h : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:417:theorem comp_add_right (hf : IntervalIntegrable f volume a b) (c : ℝ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:473:theorem comp_sub_left {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (c : ℝ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:493:theorem ContinuousOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : ContinuousOn u (uIcc a b)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:503:theorem Continuous.intervalIntegrable {u : ℝ → E} (hu : Continuous u) (a b : ℝ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:517:theorem MonotoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : MonotoneOn u (uIcc a b)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:522:theorem AntitoneOn.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : AntitoneOn u (uIcc a b)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:526:theorem Monotone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Monotone u) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:530:theorem Antitone.intervalIntegrable {u : ℝ → E} {a b : ℝ} (hu : Antitone u) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:667:theorem integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:746:theorem norm_integral_le_of_norm_le {g : ℝ → ℝ} (hab : a ≤ b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:781:theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:807:theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:812:theorem integral_mul_const {𝕜 : Type*} [RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:927:theorem integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1027:theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1068:theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1210:theorem integral_congr_ae' (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1215:theorem integral_congr_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1349:theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1388:theorem integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1405:theorem integral_mono (h : f ≤ g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Basic.lean:78:def mul : R →+ R →+ R where
.lake/packages/mathlib/Mathlib/Algebra/Ring/Basic.lean:83:lemma mul_apply (x y : R) : mul x y = x * y := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:521:protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:535:theorem Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m ≤ m0)
.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean:414:theorem IsPartialInv.comp {α β γ} {f : α → β} {g : β → Option α} {h : β → γ} {i : γ → Option β}
.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean:436:theorem LeftInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : LeftInverse f g)
.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean:440:theorem RightInverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : RightInverse f g)
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:180:def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:191:theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:246:theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:415:def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:426:theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:551:def inr : B →⋆ₙₐ[R] A × B :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:789:def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:405:theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:563:instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (X a)] : MeasurableSpace (∀ a, X a) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:692:protected theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (X i)} (hs : s.Countable)
.lake/packages/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean:296:instance pi {ι : Type*} (M : ι → Type*)
.lake/packages/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean:317:lemma Module.FinitePresentation.trans (S : Type*) [CommRing S] [Algebra R S]
.lake/packages/mathlib/Mathlib/Logic/Function/DependsOn.lean:84:lemma DependsOn.mono {s t : Set ι} (hst : s ⊆ t) (hf : DependsOn f s) : DependsOn f t :=
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:193:theorem Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : MeasurableSpace β} {f : α → β}
.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean:280:private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/Divisibility/Basic.lean:73:alias Dvd.dvd.add := dvd_add
.lake/packages/mathlib/Mathlib/Algebra/Ring/Divisibility/Basic.lean:125:alias Dvd.dvd.sub := dvd_sub
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Pi.lean:37:theorem IsPiSystem.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Pi.lean:53:theorem IsCountablySpanning.pi {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i)) :
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:129:theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:143:theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:195:theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:245:theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:332:theorem smul [Star R] [Star A] [SMul R A] [StarModule R A]
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:634:protected instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
.lake/packages/mathlib/Mathlib/Logic/Function/Conjugate.lean:58:protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
.lake/packages/mathlib/Mathlib/Logic/Function/Conjugate.lean:127:theorem symm (h : Commute f g) : Commute g f := fun x ↦ (h x).symm
.lake/packages/mathlib/Mathlib/Logic/Function/Conjugate.lean:170:theorem comp {f' : β → γ} {gc : γ → γ → γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb) :
.lake/packages/mathlib/Mathlib/Algebra/Module/Torsion/Free.lean:87:lemma Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:124:theorem mono {ν : Measure α} {φ : ι → Set α} (hφ : AECover μ l φ) (hle : ν ≤ μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:302:protected theorem AECover.restrict {φ : ι → Set α} (hφ : AECover μ l φ) {s : Set α} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:333:theorem AECover.aestronglyMeasurable {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
.lake/packages/mathlib/Mathlib/Logic/Basic.lean:160:theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
.lake/packages/mathlib/Mathlib/Logic/Basic.lean:215:protected lemma Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
.lake/packages/mathlib/Mathlib/Logic/Basic.lean:387:alias Ne.trans_eq := ne_of_ne_of_eq
.lake/packages/mathlib/Mathlib/Logic/Basic.lean:737:alias by_cases := byCases -- TODO: remove? rename in core?
.lake/packages/mathlib/Mathlib/Algebra/Ring/Submonoid/Pointwise.lean:77:protected def smul : SMul (AddSubmonoid R) (AddSubmonoid A) where
.lake/packages/mathlib/Mathlib/Algebra/Ring/Submonoid/Pointwise.lean:137:protected def mul : Mul (AddSubmonoid R) := ⟨fun M N => ⨆ s : M, N.map (AddMonoidHom.mul s.1)⟩
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:206:protected theorem CurveIntegrable.symm (h : CurveIntegrable ω γ) : CurveIntegrable ω γ.symm := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:269:protected theorem CurveIntegrable.trans (h₁ : CurveIntegrable ω γab) (h₂ : CurveIntegrable ω γbc) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:357:protected theorem CurveIntegrable.add (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:418:protected theorem CurveIntegrable.sub (h₁ : CurveIntegrable ω₁ γ) (h₂ : CurveIntegrable ω₂ γ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:463:theorem CurveIntegrable.smul (h : CurveIntegrable ω γ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean:168:theorem SeparatesPoints.mono {m m' : MeasurableSpace α} [hsep : @SeparatesPoints _ m] (h : m ≤ m') :
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean:203:theorem CountablySeparated.mono {m m' : MeasurableSpace α} [hsep : @CountablySeparated _ m]
.lake/packages/mathlib/Mathlib/Logic/Embedding/Basic.lean:132:protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
.lake/packages/mathlib/Mathlib/Logic/Embedding/Basic.lean:297:def inr {α β : Type*} : β ↪ α ⊕ β :=
.lake/packages/mathlib/Mathlib/Logic/UnivLE.lean:64:theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} where
.lake/packages/mathlib/Mathlib/Logic/ExistsUnique.lean:91:theorem ExistsUnique.unique {p : α → Prop}
.lake/packages/mathlib/Mathlib/Logic/ExistsUnique.lean:145:theorem ExistsUnique.unique₂ {p : α → Sort*} [∀ x, Subsingleton (p x)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:76:theorem MeasureTheory.StronglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α → β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:124:theorem MeasureTheory.StronglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:131:theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α → β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:137:theorem MeasureTheory.StronglyMeasurable.integral_prod_left' [SFinite μ] ⦃f : α × β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:189:theorem MeasureTheory.AEStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace ℝ E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:278:theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:286:theorem integrable_prod_iff' [SFinite μ] ⦃f : α × β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:380:theorem Integrable.integral_prod_left ⦃f : α × β → E⦄ (hf : Integrable f (μ.prod ν)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:389:theorem Integrable.integral_prod_right [SFinite μ] ⦃f : α × β → E⦄
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:532:theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:325:protected theorem map_zero : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:486:def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:503:theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:674:theorem map_zero {f : M → M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂) :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:750:theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:792:theorem zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:834:theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:882:theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/FundamentalSequence.lean:87:protected theorem comp (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/FundamentalSequence.lean:190:theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
.lake/packages/mathlib/Mathlib/Data/Multiset/MapFold.lean:69:theorem map_zero (f : α → β) : map f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Aut.lean:80:theorem mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean:59:theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:147:protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:161:protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:187:protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:223:protected abbrev unique [Unique β] (e : α ≃ β) : Unique α := e.symm.surjective.unique
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:929:protected abbrev le [LE β] : LE α where
.lake/packages/mathlib/Mathlib/Algebra/Homology/Embedding/AreComplementary.lean:50:lemma symm : AreComplementary e₂ e₁ where
.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:93:theorem Perm.subtypeCongr.symm : (ep.subtypeCongr en).symm = Perm.subtypeCongr ep.symm en.symm :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:97:theorem Perm.subtypeCongr.trans :
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:175:protected theorem zero_lt_one : (0 : ONote) < 1 := by
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:242:theorem NFBelow.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NFBelow o b₁) : NFBelow o b₂ := by
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:374:def add : ONote → ONote → ONote
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:382:theorem zero_add (o : ONote) : 0 + o = o :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:389:def sub : ONote → ONote → ONote
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:506:def mul : ONote → ONote → ONote
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Basic.lean:222:protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Basic.lean:818:instance add : Add Ordinal.{u} :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:193:theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:212:def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:225:theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:456:protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:541:def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:553:theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
.lake/packages/mathlib/Mathlib/Algebra/Module/Injective.lean:466:instance Module.Injective.pi
.lake/packages/mathlib/Mathlib/Data/Multiset/Defs.lean:162:theorem Subset.trans {s t u : Multiset α} : s ⊆ t → t ⊆ u → s ⊆ u := fun h₁ h₂ _ m => h₂ (h₁ m)
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:147:protected def symm : PartialEquiv β α where
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:323:protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:575:protected def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:590:protected def trans : PartialEquiv α γ :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:693:theorem EqOnSource.symm' {e e' : PartialEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:704:theorem EqOnSource.trans' {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:849:protected def pi (ei : ∀ i, PartialEquiv (αi i) (βi i)) : PartialEquiv (∀ i, αi i) (∀ i, βi i) where
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:403:theorem IsNormal.trans {f g} (H₁ : Ordinal.IsNormal f) (H₂ : Ordinal.IsNormal g) :
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:416:instance sub : Sub Ordinal where
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:448:theorem sub_le_self (a b : Ordinal) : a - b ≤ a := sub_le.2 le_add_self
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:457:theorem sub_zero (a : Ordinal) : a - 0 = a := by simpa only [zero_add] using add_sub_cancel 0 a
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:463:theorem sub_self (a : Ordinal) : a - a = 0 := by simpa only [add_zero] using add_sub_cancel a 0
.lake/packages/mathlib/Mathlib/Logic/Nontrivial/Basic.lean:88:protected theorem Subsingleton.le [Preorder α] [Subsingleton α] (x y : α) : x ≤ y :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Topology.lean:220:theorem IsAcc.mono {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
.lake/packages/mathlib/Mathlib/Logic/Pairwise.lean:37:theorem Pairwise.mono (hr : Pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : Pairwise p :=
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:51:protected theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:63:theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:67:theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:74:theorem Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:143:theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:155:theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
.lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:159:theorem Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
.lake/packages/mathlib/Mathlib/Algebra/Module/Defs.lean:150:theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:259:def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:271:theorem smul_apply (r : R) (v : VectorMeasure α M) (i : Set α) : (r • v) i = r • v i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:288:theorem zero_apply (i : Set α) : (0 : VectorMeasure α M) i = 0 := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:293:def add (v w : VectorMeasure α M) : VectorMeasure α M where
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:305:theorem add_apply (v w : VectorMeasure α M) (i : Set α) : (v + w) i = v i + w i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:339:def sub (v w : VectorMeasure α M) : VectorMeasure α M where
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:351:theorem sub_apply (v w : VectorMeasure α M) (i : Set α) : (v - w) i = v i - w i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:579:theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 := by
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:652:def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:1043:theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:1061:theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:1066:theorem sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:1072:theorem smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:1123:theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:211:def comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap ρ τ where
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:220:lemma comp_apply (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) (v : V) :
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:317:def symm (φ : Equiv ρ σ) : Equiv σ ρ where
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:343:def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ where
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:404:lemma smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) :
.lake/packages/mathlib/Mathlib/SetTheory/Lists.lean:282:theorem Equiv.symm {l₁ l₂ : Lists α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
.lake/packages/mathlib/Mathlib/SetTheory/Lists.lean:285:theorem Equiv.trans : ∀ {l₁ l₂ l₃ : Lists α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ := by
.lake/packages/mathlib/Mathlib/SetTheory/Lists.lean:403:theorem Subset.trans {l₁ l₂ l₃ : Lists' α true} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
.lake/packages/mathlib/Mathlib/Data/Multiset/Pi.lean:108:def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
.lake/packages/mathlib/Mathlib/Data/Multiset/Pi.lean:140:protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Idempotent.lean:93:theorem add [NonUnitalNonAssocSemiring R]
.lake/packages/mathlib/Mathlib/Algebra/Ring/Idempotent.lean:109:lemma sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:50:protected def add (s₁ s₂ : Multiset α) : Multiset α :=
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:81:protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ ↦ rfl
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:84:protected lemma add_zero (s : Multiset α) : s + 0 = s :=
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:278:protected def sub (s t : Multiset α) : Multiset α :=
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:291:protected lemma sub_zero (s : Multiset α) : s - 0 = s :=
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:321:protected theorem sub_le_self (s t : Multiset α) : s - t ≤ s := by
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:331:protected lemma sub_add_cancel (hts : t ≤ s) : s - t + t = s := by
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:342:protected lemma add_sub_cancel_right : s + t - t = s := by ext a; simp
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:372:theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/SumsOfSquares.lean:62:theorem IsSumSq.add [AddMonoid R] [Mul R] {s₁ s₂ : R}
.lake/packages/mathlib/Mathlib/Algebra/Ring/SumsOfSquares.lean:178:theorem IsSumSq.mul [NonUnitalCommSemiring R] {s₁ s₂ : R}
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/PSet.lean:99:protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/PSet.lean:106:protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomologicalComplex.lean:237:def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where
.lake/packages/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean:118:lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
.lake/packages/mathlib/Mathlib/RepresentationTheory/Rep/Basic.lean:837:def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:59:private def add :
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:64:private def smul {S : Type*} [SMulZeroClass S k] :
.lake/packages/mathlib/Mathlib/RepresentationTheory/Basic.lean:282:def norm : Module.End k V := ∑ g : G, ρ g
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:70:theorem add_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ + m₂) s = m₁ s + m₂ s :=
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:93:theorem smul_apply (c : R) (m : OuterMeasure α) (s : Set α) : (c • m) s = c • m s :=
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:201:theorem mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) :
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:296:def restrict (s : Set α) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure α :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:252:def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:308:def trans
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:504:protected theorem map_zero : e 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Basic.lean:434:theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
.lake/packages/mathlib/Mathlib/Data/Multiset/ZeroCons.lean:528:theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t)
.lake/packages/mathlib/Mathlib/Data/Multiset/ZeroCons.lean:594:theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:124:theorem IntegrableOn.mono (h : IntegrableOn f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) : IntegrableOn f s μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:128:theorem IntegrableOn.mono_set (h : IntegrableOn f t μ) (hst : s ⊆ t) : IntegrableOn f s μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:178:theorem IntegrableOn.restrict (h : IntegrableOn f s μ) : IntegrableOn f s (μ.restrict t) := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:266:theorem IntegrableOn.add [ContinuousAdd ε'] {f g : α → ε'}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:271:theorem IntegrableOn.sub {f g : α → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:542:protected theorem IntegrableAtFilter.add [ContinuousAdd ε'] {f g : α → ε'}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:555:protected theorem IntegrableAtFilter.sub {f g : α → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:561:protected theorem IntegrableAtFilter.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:571:protected theorem IntegrableAtFilter.norm {f : α → E} (hf : IntegrableAtFilter f l μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:723:theorem ContinuousOn.aestronglyMeasurable [TopologicalSpace α] [TopologicalSpace β]
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/Class.lean:91:theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
.lake/packages/mathlib/Mathlib/Algebra/Quandle.lean:344:def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ where
.lake/packages/mathlib/Mathlib/Algebra/Quandle.lean:349:theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
.lake/packages/mathlib/Mathlib/Algebra/Quandle.lean:567:theorem PreEnvelGroupRel.symm {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
.lake/packages/mathlib/Mathlib/Algebra/Quandle.lean:572:theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean:65:theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean:71:theorem smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean:163:theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean:169:theorem smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
.lake/packages/mathlib/Mathlib/Algebra/Field/Rat.lean:50:protected lemma div_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
.lake/packages/mathlib/Mathlib/Algebra/Module/PUnit.lean:25:instance smul : SMul R PUnit :=
Poincare/Global/HeatEnvelopes.lean:46:theorem integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/ComplexShape.lean:92:def symm (c : ComplexShape ι) : ComplexShape ι where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ComplexShape.lean:109:def trans (c₁ c₂ : ComplexShape ι) : ComplexShape ι where
.lake/packages/mathlib/Mathlib/MeasureTheory/Covering/VitaliFamily.lean:92:def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
.lake/packages/mathlib/Mathlib/Data/Multiset/DershowitzManna.lean:54:lemma IsDershowitzMannaLT.trans :
.lake/packages/mathlib/Mathlib/Algebra/BrauerGroup/Defs.lean:66:lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A :=
.lake/packages/mathlib/Mathlib/Algebra/BrauerGroup/Defs.lean:72:lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean:113:lemma le₀₁' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ) {i₀ i₁ : ι}
.lake/packages/mathlib/Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean:120:lemma le₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') :
.lake/packages/mathlib/Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean:124:lemma le₂₃' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ)
.lake/packages/mathlib/Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean:131:lemma le₃₃' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:67:lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean:344:instance unique' [Subsingleton R] : Unique (Submodule R M) := by
.lake/packages/mathlib/Mathlib/Data/PNat/Prime.lean:166:theorem Coprime.mul {k m n : ℕ+} : m.Coprime k → n.Coprime k → (m * n).Coprime k := by
.lake/packages/mathlib/Mathlib/Data/PNat/Prime.lean:218:theorem Coprime.symm {m n : ℕ+} : m.Coprime n → n.Coprime m := by
.lake/packages/mathlib/Mathlib/Data/PNat/Prime.lean:262:theorem Coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.Coprime n) : (m ^ k : ℕ).Coprime (n ^ l) := by
.lake/packages/mathlib/Mathlib/Geometry/Manifold/LocalInvariantProperties.lean:661:theorem HasGroupoid.comp
.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Basic.lean:168:lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/LinearMap.lean:203:def restrict (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean:238:instance add : Add p :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean:247:instance smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean:98:protected theorem map_zero : X 0 = 0 := by simp
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Basic.lean:148:protected lemma map_zero [Zero S] (f : ZeroHom R S) : (0 : R⟦Γ⟧).map f = 0 := by
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Map.lean:113:protected theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:123:theorem ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:132:theorem ContMDiffOn.mul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (f * g) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:136:theorem ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f * g) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:461:theorem ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:471:theorem ContMDiffOn.pow (hg : CMDiff[s] n g) (m : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:476:theorem ContMDiff.pow (hg : CMDiff n g) (m : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:507:theorem ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:517:theorem ContMDiffOn.div_const (hf : CMDiff[s] n f) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:521:theorem ContMDiff.div_const (hf : CMDiff n f) :
.lake/packages/mathlib/Mathlib/Data/Set/Countable.lean:115:theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hs : s₂.Countable) : s₁.Countable :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean:333:theorem zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} : (0 : R⟦Γ⟧) • x = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean:338:theorem one_smul' {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean:595:private theorem mul_assoc' [NonUnitalSemiring R] (x y z : R⟦Γ⟧) : x * y * z = x * (y * z) := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:518:protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:523:protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/HasGroupoid.lean:368:def Structomorph.symm (e : Structomorph G M M') : Structomorph G M' M :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/HasGroupoid.lean:378:def Structomorph.trans (e : Structomorph G M M') (e' : Structomorph G M' M'') :
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Invariant.lean:182:protected lemma comp {p : Submodule R M} {g : End R M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/StructureGroupoid.lean:161:theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/StructureGroupoid.lean:165:theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean:50:instance Measure.restrict.instNoAtoms (s : Set α) : NoAtoms (μ.restrict s) := by
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Cover/Directed.lean:59:def trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j := LocallyDirected.trans hij
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:51:lemma sqrt.iter_sq_le (n guess : ℕ) : sqrt.iter n guess * sqrt.iter n guess ≤ n := by
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:60:lemma sqrt.lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:158:lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:366:protected theorem IsFiniteMeasureOnCompacts.smul [TopologicalSpace α] (μ : Measure α)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:484:protected theorem mono (hf : f ≤ g) (hμ : μ ≤ ν) : ν.FiniteAtFilter g → μ.FiniteAtFilter f :=
.lake/packages/mathlib/Mathlib/Data/Set/Subsingleton.lean:172:theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s ⊆ t) : t.Nontrivial :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:235:protected def symm : PartialEquiv E H :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:529:def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Sub.lean:60:protected theorem sub_self : μ - μ = 0 :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Sub.lean:64:protected theorem sub_zero : μ - 0 = μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Sub.lean:72:theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν ≤ μ) :
.lake/packages/mathlib/Mathlib/Algebra/Prime/Lemmas.lean:163:theorem DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p ≠ q := by
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:130:theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:137:theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:162:theorem smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s a :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:355:theorem sub_apply : (s - t) a = s a - t a :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:428:def smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) : SummableFamily Γ' V (α × β) where
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:493:theorem smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} :
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:546:def mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
.lake/packages/mathlib/Mathlib/Data/Set/Monotone.lean:115:protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun _ _ hxy =>
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean:134:theorem mono : Monotone f :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean:184:protected def add (f g : StieltjesFunction R) : StieltjesFunction R where
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/DenomsClearable.lean:57:theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
.lake/packages/mathlib/Mathlib/RingTheory/EssentialFiniteness.lean:140:lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/PreVariation.lean:113:lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean:162:protected def mul {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R}
.lake/packages/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean:371:theorem smul'_mk (r : R) (s : S) (m : M) : r • mk m s = mk (r • m) s := by
.lake/packages/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean:397:theorem smul'_mul {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:57:theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun _ hx => (h hx).symm
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:71:theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:82:theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun _ hx => hf (hs hx)
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:149:theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun _ h =>
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:170:theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:273:theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun _ hx _ hy H =>
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:306:theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:488:theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:513:theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:676:theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:807:theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:813:theorem mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun _ hx =>
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:866:theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:870:theorem mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:910:lemma comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:916:theorem symm (h : InvOn f' f s t) : InvOn f f' t s :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:919:theorem mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:1105:lemma BijOn.symm {g : β → α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:1271:lemma MapsTo.prodMk (h₁ : MapsTo f₁ s t₁) (h₂ : MapsTo f₂ s t₂) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean:73:theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean:78:protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean:232:theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean:159:theorem trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean:211:protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean:648:instance unique [Subsingleton R] : Unique (FractionRing R) := inferInstance
.lake/packages/mathlib/Mathlib/Algebra/Module/GradedModule.lean:108:private theorem one_smul' [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:88:protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] :=
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:92:protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] :=
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:147:protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:151:protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:159:protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:195:protected lemma sub' (h : c ≤ a ↔ d ≤ b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:209:protected lemma sub (hca : c ≤ a) (hdb : d ≤ b) (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
.lake/packages/mathlib/Mathlib/Data/Nat/ModEq.lean:223:protected theorem mul_left_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:325:abbrev restrict (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] : X.Modules :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean:59:theorem mono_set {s t} (h : s ⊆ t) (ht : AEMeasurable f (μ.restrict t)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean:64:protected theorem mono' (h : AEMeasurable f μ) (h' : ν ≪ μ) : AEMeasurable f ν :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean:192:theorem prodMk {f : α → β} {g : α → γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean:302:theorem AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.restrict s) :=
.lake/packages/mathlib/Mathlib/Data/Set/Pairwise/Basic.lean:74:theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r :=
.lake/packages/mathlib/Mathlib/Data/Set/Pairwise/Basic.lean:77:theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
.lake/packages/mathlib/Mathlib/Data/Set/Pairwise/Basic.lean:232:theorem PairwiseDisjoint.mono (hs : s.PairwiseDisjoint f) (h : g ≤ f) : s.PairwiseDisjoint g :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean:121:lemma GeometricallyIrreducible.comp
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Geometrically/Connected.lean:112:lemma GeometricallyConnected.comp
.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean:100:theorem mem_univ (x : α) : x ∈ @univ α := trivial
.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean:262:def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) := {f | ∀ i ∈ s, f i ∈ t i}
.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean:284:def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/LocalDiffeomorph.lean:113:protected def symm : PartialDiffeomorph J I N M n where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean:188:protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) : M ≃ₘ^n⟮I, J⟯ N where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean:207:protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M where
.lake/packages/mathlib/Mathlib/Data/Set/Basic.lean:271:theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun _ h => bc <| ab h
.lake/packages/mathlib/Mathlib/Data/Set/Basic.lean:382:theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean:373:def comp (p q : R[X]) : R[X] :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean:503:protected theorem map_zero : (0 : R[X]).map f = 0 :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Content.lean:103:theorem mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) ⊆ K₂) : μ K₁ ≤ μ K₂ := by
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:184:theorem ContMDiffWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:201:theorem ContMDiffOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:205:theorem ContMDiff.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:271:theorem ContMDiffWithinAt.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiffWithinAt I 𝓘(𝕜) n f s x)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:280:theorem ContMDiffOn.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiffOn I 𝓘(𝕜) n f s)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:284:theorem ContMDiff.smul {f : M → 𝕜} {g : M → V} (hf : ContMDiff I 𝓘(𝕜) n f)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:652:theorem ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:690:theorem ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t ⊆ s) : ContMDiffOn I I' n f t :=
.lake/packages/mathlib/Mathlib/Data/Set/Restrict.lean:32:def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
.lake/packages/mathlib/Mathlib/Data/Set/Restrict.lean:106:def restrict₂ {s t : Set α} (hst : s ⊆ t) (f : ∀ a : t, π a) : ∀ a : s, π a :=
.lake/packages/mathlib/Mathlib/Data/Set/Restrict.lean:109:theorem restrict₂_def {s t : Set α} (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Data/Set/Restrict.lean:112:theorem restrict₂_comp_restrict {s t : Set α} (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Data/Set/Restrict.lean:115:theorem restrict₂_comp_restrict₂ {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean:59:protected theorem Splits.mul {f g : R[X]} (hf : Splits f) (hg : Splits g) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean:71:protected theorem Splits.pow {f : R[X]} (hf : Splits f) (n : ℕ) : Splits (f ^ n) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:56:theorem ContMDiffWithinAt.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffWithinAt I I' n f s x)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:77:theorem ContMDiffOn.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffOn I I' n f s)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:224:theorem ContMDiffWithinAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:232:theorem ContMDiffWithinAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:241:theorem ContMDiffAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:247:theorem ContMDiffAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M} {y : M' × N'}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Constructions.lean:405:lemma ContMDiff.inr : ContMDiff I I n (@Sum.inr M M') := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean:85:protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 <| h2 hs
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean:98:protected theorem smul [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν) (c : R) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean:104:protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
.lake/packages/mathlib/Mathlib/Data/TwoPointing.lean:80:def pi : TwoPointing (α → β) where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean:57:theorem ContMDiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean:93:theorem ContMDiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean:98:theorem ContMDiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean:103:theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Basic.lean:109:theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Monic.lean:85:theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Monic.lean:95:theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Monic.lean:119:lemma comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
.lake/packages/mathlib/Mathlib/Data/PFun.lean:156:def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x =>
.lake/packages/mathlib/Mathlib/Data/PFun.lean:476:def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
.lake/packages/mathlib/Mathlib/Data/PFun.lean:479:theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/GroupRingAction.lean:95:theorem prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul G R x :=
.lake/packages/mathlib/Mathlib/RingTheory/Localization/Away/Basic.lean:259:lemma mul (T : Type*) [CommSemiring T] [Algebra S T]
.lake/packages/mathlib/Mathlib/RingTheory/Localization/Away/Basic.lean:284:lemma mul' (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (x y : R)
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/RationalMap.lean:81:def restrict (f : X.PartialMap Y) (U : X.Opens)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:50:noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:234:instance restrict.neZero [NeZero (μ s)] : NeZero (μ.restrict s) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:419:theorem QuasiMeasurePreserving.restrict {ν : Measure β} {f : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:511:lemma AbsolutelyContinuous.restrict (h : μ ≪ ν) (s : Set α) : μ.restrict s ≪ ν.restrict s := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:634:theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean:637:theorem ae_restrict_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
.lake/packages/mathlib/Mathlib/Data/Seq/Computation.lean:828:theorem Equiv.symm {s t : Computation α} : s ~ t → t ~ s := fun h a => (h a).symm
.lake/packages/mathlib/Mathlib/Data/Seq/Computation.lean:831:theorem Equiv.trans {s t u : Computation α} : s ~ t → t ~ u → s ~ u := fun h1 h2 a =>
.lake/packages/mathlib/Mathlib/Data/Seq/Computation.lean:886:theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
.lake/packages/mathlib/Mathlib/Data/Seq/Computation.lean:895:instance LiftRel.trans (R : α → α → Prop) [IsTrans α R] : IsTrans _ (LiftRel R) :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Scheme.lean:380:theorem comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Map.lean:107:protected theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
.lake/packages/mathlib/Mathlib/Data/Set/Finite/Basic.lean:519:protected lemma Infinite.mono {s t : Set α} (h : s ⊆ t) : s.Infinite → t.Infinite :=
.lake/packages/mathlib/Mathlib/Data/Real/Hom.lean:39:instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:127:lemma mono
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:210:theorem smul_const (hcov : IsCovariantDerivativeOn F cov s)
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/IsMonicOfDegree.lean:72:lemma IsMonicOfDegree.mul {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/IsMonicOfDegree.lean:84:lemma IsMonicOfDegree.pow {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/IsMonicOfDegree.lean:149:lemma IsMonicOfDegree.comp {p q : R[X]} {m n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p m)
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/IsMonicOfDegree.lean:226:lemma IsMonicOfDegree.sub {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:281:theorem smul_apply [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:286:def restrict (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω where
.lake/packages/mathlib/Mathlib/Data/Real/Basic.lean:351:protected theorem zero_lt_one : (0 : ℝ) < 1 := by
.lake/packages/mathlib/Mathlib/Data/Set/FiniteExhaustion.lean:57:protected theorem mono {m n : ℕ} (h : m ≤ n) : K m ⊆ K n :=
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:77:protected lemma symm : q.HolderTriple p r where
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:87:protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:103:protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:147:protected lemma symm : q.HolderConjugate p := HolderTriple.symm h
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:261:protected lemma symm : q.HolderTriple p r where
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:271:protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:287:protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
.lake/packages/mathlib/Mathlib/Data/Real/ConjExponents.lean:330:protected lemma symm : q.HolderConjugate p := HolderTriple.symm h
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/LocalFrame.lean:151:lemma mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' ⊆ u) : IsLocalFrameOn I F n s u' where
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:884:theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:914:theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:46:noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:178:theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:276:theorem sq_sqrt' : √x ^ 2 = max x 0 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:286:theorem sqrt_pos : 0 < √x ↔ 0 < x :=
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:443:theorem Filter.Tendsto.sqrt {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) :
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:458:theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) s :=
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:462:theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x) :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ColimitsOver.lean:60:def trans {i j : 𝒰.I₀} (hij : i ⟶ j) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean:319:instance unique [Subsingleton R] : Unique R[X] :=
.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:664:protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:275:protected theorem mul_one : φ * 1 = φ :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:286:protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:170:theorem MDifferentiableWithinAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:181:theorem MDifferentiableAt.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:189:theorem MDifferentiableOn.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : Set M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:193:theorem MDifferentiable.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:271:lemma HasMFDerivAt.smul
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:288:theorem MDifferentiableWithinAt.smul
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:294:theorem MDifferentiableAt.smul (hf : MDiffAt f x)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:298:theorem MDifferentiableOn.smul (hf : MDiff[s] f)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean:302:theorem MDifferentiable.smul (hf : MDiff f) (hg : MDiff g) : MDiff fun p ↦ f p • g p :=
.lake/packages/mathlib/Mathlib/Data/Set/Equitable.lean:113:theorem EquitableOn.le (h : EquitableOn (s : Set α) f) (ha : a ∈ s) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:194:lemma structureSheafInType.add_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:198:lemma structureSheafInType.mul_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:202:lemma structureSheafInType.smul_apply {U : Opens (PrimeSpectrum.Top R)}
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:325:theorem const_add (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:330:theorem smul_const (f : M) (r g : R) (U hu) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/StructureSheaf.lean:335:theorem const_mul (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:216:theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:223:theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:240:theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:246:theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:262:theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDiff[s] f) (hg : MDiff[s] g) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:265:theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDiff f) (hg : MDiff g) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:765:theorem HasMFDerivWithinAt.add {s : Set M}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:770:theorem HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:774:theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:778:theorem MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f + g) z :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:781:theorem MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f + g) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:784:theorem MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:868:theorem HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:872:theorem MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f - g) z :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:875:theorem MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:891:theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:896:theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:901:theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:906:theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:910:theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:914:theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:918:theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:924:theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:928:theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:931:theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:942:theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean:947:theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:795:def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : X.OpenCover) (U : Opens X) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Evaluation.lean:71:theorem HasEval.mono {S : Type*} [CommRing S] {a : σ → S}
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Evaluation.lean:81:theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Evaluation.lean:120:theorem HasEval.pow (x : σ → S) (ha : HasEval x) {p : ℕ} (hp : 0 < p) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Order.lean:561:protected theorem IsWeightedHomogeneous.add {f g : MvPowerSeries σ R} {p : ℕ}
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Order.lean:569:protected theorem IsWeightedHomogeneous.mul {f g : MvPowerSeries σ R} {p q : ℕ}
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Order.lean:692:protected theorem IsHomogeneous.add {f g : MvPowerSeries σ R} {p : ℕ}
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Order.lean:697:protected theorem IsHomogeneous.mul {f g : MvPowerSeries σ R} {p q : ℕ}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:79:theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:113:theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:142:theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:584:theorem HasMFDerivWithinAt.mono (h : HasMFDerivWithinAt I I' f t x f') (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1118:theorem HasMFDerivWithinAt.comp (hg : HasMFDerivWithinAt I' I'' g u (f x) g')
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1145:theorem HasMFDerivAt.comp (hg : HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1156:theorem MDifferentiableWithinAt.comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1183:theorem MDifferentiableAt.comp (hg : MDifferentiableAt I' I'' g (f x))
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1273:theorem MDifferentiableOn.comp (hg : MDifferentiableOn I' I'' g u) (hf : MDifferentiableOn I I' f s)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean:1282:theorem MDifferentiable.comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:57:theorem zero_apply (i : ℕ) : (0 : PolynomialModule R M) i = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:60:theorem add_apply (g₁ g₂ : PolynomialModule R M) (a : ℕ) : (g₁ + g₂) a = g₁ a + g₂ a :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:151:theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:305:def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean:215:theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:275:theorem smul (H : InnerRegularWRT μ p q) (c : ℝ≥0∞) : InnerRegularWRT (c • μ) p q := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:280:theorem trans {q' : Set α → Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:292:theorem mono {p' q' : Set α → Prop} (H : InnerRegularWRT μ p q)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:416:protected theorem smul (μ : Measure α) [OuterRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:528:lemma restrict (h : InnerRegularWRT μ p (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞)) (A : Set α) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:709:instance smul [h : InnerRegular μ] (c : ℝ≥0∞) : InnerRegular (c • μ) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:877:instance restrict [h : InnerRegularCompactLTTop μ] (A : Set α) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:962:instance smul [h : InnerRegularCompactLTTop μ] (c : ℝ≥0∞) : InnerRegularCompactLTTop (c • μ) := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:1077:protected theorem smul [WeaklyRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).WeaklyRegular := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean:1143:protected theorem smul [Regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).Regular := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEDisjoint.lean:55:protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [AEDisjoint, inter_comm]
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/AEDisjoint.lean:76:protected theorem mono (h : AEDisjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : AEDisjoint μ u v :=
.lake/packages/mathlib/Mathlib/Algebra/IsPrimePow.lean:58:theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Inverse.lean:237:protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff φ ≠ 0) :
.lake/packages/mathlib/Mathlib/Data/Fintype/Defs.lean:96:theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
.lake/packages/mathlib/Mathlib/Data/ENNReal/Inv.lean:102:protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/Data/ENNReal/Inv.lean:219:protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Substitution.lean:104:theorem HasSubst.add {a b : σ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Substitution.lean:122:theorem HasSubst.smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Substitution.lean:163:protected lemma HasSubst.pow {n : ℕ} (hn : n ≠ 0) {a : σ → MvPowerSeries τ S} (h : HasSubst a) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Substitution.lean:420:theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean:127:lemma IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' ⊆ s) :
.lake/packages/mathlib/Mathlib/Data/ENNReal/Operations.lean:114:protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
.lake/packages/mathlib/Mathlib/Data/ENNReal/Operations.lean:349:protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a := by
.lake/packages/mathlib/Mathlib/Data/ENNReal/Operations.lean:412:theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
.lake/packages/mathlib/Mathlib/Data/ENNReal/Holder.lean:62:instance symm {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r where
.lake/packages/mathlib/Mathlib/Data/ENNReal/Holder.lean:75:lemma unique (r' : ℝ≥0∞) [hr' : HolderTriple p q r'] : r = r' := by
.lake/packages/mathlib/Mathlib/Data/ENNReal/Holder.lean:87:lemma le : r ≤ p := by
.lake/packages/mathlib/Mathlib/Data/ENNReal/Holder.lean:130:instance symm {p q : ℝ≥0∞} [hpq : HolderConjugate p q] : HolderConjugate q p :=
.lake/packages/mathlib/Mathlib/Data/ENNReal/Holder.lean:157:lemma unique (q' : ℝ≥0∞) [hq' : HolderConjugate p q'] : q = q' :=
Poincare/Global/CartanCanonicalFamilyComparedCanonicalContinuation.lean:191:theorem CanonicalNormalRadiusAdmissible.mono
.lake/packages/mathlib/Mathlib/Data/TypeVec.lean:75:def comp (g : β ⟹ γ) (f : α ⟹ β)
.lake/packages/mathlib/Mathlib/Data/TypeVec.lean:174:def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/OpenImmersion.lean:40:instance IsOpenImmersion.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/OpenImmersion.lean:376:def Scheme.restrict : Scheme :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/OpenImmersion.lean:486:instance mono : Mono f :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:114:theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:174:theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
.lake/packages/mathlib/Mathlib/Data/Fintype/Pi.lean:200:theorem Finite.pi (ht : ∀ i, (t i).Finite) : (pi univ t).Finite := by
.lake/packages/mathlib/Mathlib/Data/Fintype/Pi.lean:209:lemma Finite.pi' (ht : ∀ i, (t i).Finite) : {f : ∀ i, κ i | ∀ i, f i ∈ t i}.Finite := by
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiffMap.lean:83:def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiffMap.lean:88:theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiffMap.lean:108:def prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
Poincare/Global/HeatCauchyTheorem.lean:32:theorem hasFDerivAt_heatKernel_spatial {t : ℝ} (ht : t ≠ 0) (u : E) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasurePi.lean:44:noncomputable def pi (μ : Π i, FiniteMeasure (α i)) : FiniteMeasure (Π i, α i) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasurePi.lean:72:noncomputable def pi (μ : Π i, ProbabilityMeasure (α i)) : ProbabilityMeasure (Π i, α i) :=
.lake/packages/mathlib/Mathlib/RingTheory/Idempotents.lean:102:lemma OrthogonalIdempotents.unique [Unique I] :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ChartedSpace.lean:286:def ChartedSpace.comp (H : Type*) [TopologicalSpace H] (H' : Type*) [TopologicalSpace H']
.lake/packages/mathlib/Mathlib/Data/List/Rotate.lean:376:theorem IsRotated.symm (h : l ~r l') : l' ~r l := by
.lake/packages/mathlib/Mathlib/Data/List/Rotate.lean:392:theorem IsRotated.trans : ∀ {l l' l'' : List α}, l ~r l' → l' ~r l'' → l ~r l''
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean:182:noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean:414:noncomputable def add (P Q : W.Point) : W.Point :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MutuallySingular.lean:81:theorem symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MutuallySingular.lean:100:theorem mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MutuallySingular.lean:138:theorem smul (r : ℝ≥0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MutuallySingular.lean:144:lemma restrict (h : μ ⟂ₘ ν) (s : Set α) : μ.restrict s ⟂ₘ ν := by
.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Defs.lean:87:theorem comp (f : ι' → ι) (hf : Function.Injective f) : AlgebraicIndependent R (x ∘ f) := by
.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Defs.lean:117:lemma AlgebraicIndepOn.mono {s t : Set ι} (H : AlgebraicIndepOn R x t) (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Defs.lean:127:theorem mono {t s : Set A} (h : t ⊆ s)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:22:theorem integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:37:theorem hessian_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:81:theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:97:theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:202:theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:236:theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:284:theorem Pointed.mono (h : C₁ ≤ C₂) : C₁.Pointed → C₂.Pointed := @h _
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:301:theorem Flat.mono (h : C₁ ≤ C₂) : C₁.Flat → C₂.Flat
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:464:theorem IsGenerating.mono {C₁ C₂ : ConvexCone R M} (h : C₁ ≤ C₂) (hgen : C₁.IsGenerating) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:141:lemma smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:644:def add : W.Point → W.Point → W.Point
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:793:lemma map_zero : map f (0 : (W'⁄F).Point) = 0 :=
.lake/packages/mathlib/Mathlib/Data/List/Lattice.lean:44:theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:369:lemma sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a * χ (-a) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:405:lemma sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:137:theorem MemLp.add [ContinuousAdd ε] (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f + g) p μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:140:theorem MemLp.sub {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f - g) p μ := by
.lake/packages/mathlib/Mathlib/Data/Finset/Slice.lean:49:theorem Sized.mono (h : A ⊆ B) (hB : B.Sized r) : A.Sized r := fun _x hx => hB <| h hx
.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean:153:instance Additive.add [Mul α] : Add (Additive α) where
.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean:156:instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean:390:instance Additive.sub [Div α] : Sub (Additive α) where
.lake/packages/mathlib/Mathlib/Algebra/CharP/Pi.lean:22:instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : ℕ) [CharP R p] :
.lake/packages/mathlib/Mathlib/Algebra/CharP/Pi.lean:34:instance pi' (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : ℕ) [CharP R p] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:307:theorem MemLp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:320:theorem MemLp.mul (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:326:theorem MemLp.mul' (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Eisenstein/Distinguished.lean:37:lemma mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:122:theorem MemLp.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞} (h : MemLp f p μ) :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:192:noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:428:noncomputable def add (P Q : W.Point) : W.Point :=
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:72:theorem mul (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:510:alias MemLp.mono := MemLp.of_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:512:theorem MemLp.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:516:theorem MemLp.mono' {f : α → E} {g : α → ℝ} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:616:theorem MemLp.restrict (s : Set α) {f : α → ε} (hf : MemLp f p μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:735:theorem MemLp.norm {f : α → E} (h : MemLp f p μ) : MemLp (fun x => ‖f x‖) p μ :=
.lake/packages/mathlib/Mathlib/Data/Finset/MulAntidiagonal.lean:28:theorem IsPWO.mul [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
.lake/packages/mathlib/Mathlib/Data/Finset/MulAntidiagonal.lean:36:theorem IsWF.mul (hs : s.IsWF) (ht : t.IsWF) : IsWF (s * t) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Subsemigroup/Operations.lean:601:def restrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Preimmersion.lean:59:instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean:50:theorem MemLp.const_mul {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean:53:theorem MemLp.mul_const {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean:81:theorem MemLp.const_mul' {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/Tangent.lean:345:lemma IsExtTangentAt.symm {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/Tangent.lean:393:lemma IsExtTangent.symm {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) : s₂.IsExtTangent s₁ := by
.lake/packages/mathlib/Mathlib/Data/Finset/Finsupp.lean:89:def pi (f : ι →₀ Finset α) : Finset (ι →₀ α) :=
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/Basic.lean:258:protected lemma IsDiameter.symm (h : s.IsDiameter p₁ p₂) : s.IsDiameter p₂ p₁ :=
.lake/packages/mathlib/Mathlib/Data/Finset/Defs.lean:238:theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
.lake/packages/mathlib/Mathlib/Data/Finset/Defs.lean:241:theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h =>
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:144:instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:66:instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean:57:instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:296:protected def mul : Mul (Set α) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:334:theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:668:lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:732:lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:751:lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean:1048:lemma MapsTo.mul [Mul β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean:419:protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean:526:protected theorem aestronglyMeasurable (f : Lp.simpleFunc E p μ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean:76:protected def smul [SMul α β] : SMul (Set α) (Set β) where smul := image2 (· • ·)
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Content.lean:357:theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:54:theorem LocallyIntegrableOn.mono_set (hf : LocallyIntegrableOn f s μ) {t : Set X}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:63:theorem LocallyIntegrableOn.norm {f : X → E} (hf : LocallyIntegrableOn f s μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:75:theorem LocallyIntegrableOn.mono {f : X → E} (hf : LocallyIntegrableOn f s μ) {g : X → F}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:178:theorem LocallyIntegrableOn.aestronglyMeasurable [PseudoMetrizableSpace ε]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:205:protected theorem LocallyIntegrableOn.add [ContinuousAdd ε''] {f g : X → ε''}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:210:protected theorem LocallyIntegrableOn.sub
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:245:theorem LocallyIntegrable.mono {f : X → E} (hf : LocallyIntegrable f μ) {g : X → F}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:321:theorem LocallyIntegrable.aestronglyMeasurable [PseudoMetrizableSpace ε] [SecondCountableTopology X]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:385:protected theorem LocallyIntegrable.add [ContinuousAdd ε''] {f g : X → ε''}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:389:protected theorem LocallyIntegrable.sub {f g : X → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:396:protected theorem LocallyIntegrable.smul {f : X → E} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:85:instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f]
.lake/packages/mathlib/Mathlib/Data/List/Pi.lean:77:def pi : ∀ l : List ι, (∀ i, List (α i)) → List (∀ i, i ∈ l → α i)
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:141:theorem restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U) :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:252:lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:523:theorem restrict (hf : P f) (U : Y.affineOpens) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Finite.lean:39:theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Finite.lean:75:theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
.lake/packages/mathlib/Mathlib/Data/Finset/Lattice/Lemmas.lean:65:theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s ∪ t).Nonempty :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:323:protected def mul : Mul (Finset α) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:373:theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:848:lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:1150:lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:1214:lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/LocalClosure.lean:46:lemma le [W.ContainsIdentities] [W.RespectsIso] : P ≤ sourceLocalClosure W P :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Scalar.lean:68:protected def smul : SMul (Finset α) (Finset β) := ⟨image₂ (· • ·)⟩
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Scalar.lean:99:lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image₂
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:179:protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:309:theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:50:def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:161:def restrict (s : Finset ι) (f : (i : ι) → π i) : (i : s) → π i := fun x ↦ f x
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:176:def restrict₂ (hst : s ⊆ t) (f : (i : t) → π i) (i : s) : π i := f ⟨i.1, hst i.2⟩
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:178:theorem restrict₂_def (hst : s ⊆ t) : restrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:180:theorem restrict₂_comp_restrict (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:183:theorem restrict₂_comp_restrict₂ (hst : s ⊆ t) (htu : t ⊆ u) :
.lake/packages/mathlib/Mathlib/Data/Finset/Pi.lean:201:lemma restrict₂_preimage [DecidablePred (· ∈ s)] (hst : s ⊆ t) (u : (i : s) → Set (π i)) :
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:342:theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean:883:def restrict : IntermediateField K E :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:134:protected theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:154:protected theorem Measurable.sqrt : Measurable fun x => √(f x) := continuous_sqrt.measurable.comp hf
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:166:protected lemma AEMeasurable.exp : AEMeasurable (fun x ↦ exp (f x)) μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Basic.lean:190:protected lemma AEMeasurable.sqrt : AEMeasurable (fun x ↦ √(f x)) μ :=
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/IsPoly.lean:196:instance comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] :
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/IsPoly.lean:242:instance IsPoly.comp₂ {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f] :
.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Basic.lean:159:theorem mul_inv_cancel : ∀ {p : K⟮X⟯}, p ≠ 0 → p * p⁻¹ = 1
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Defs.lean:491:instance mul : Mul H :=
.lake/packages/mathlib/Mathlib/Data/Finset/SMulAntidiagonal.lean:33:theorem IsPWO.smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
.lake/packages/mathlib/Mathlib/Data/Finset/SMulAntidiagonal.lean:39:theorem IsWF.smul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedSMul G P] {s : Set G}
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Basic.lean:176:def pi (I : Set η) (H : ∀ i, Subgroup (f i)) : Subgroup (∀ i, f i) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:174:theorem symm (hf : AbsolutelyContinuousOnInterval f a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:178:theorem mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d ⊆ uIcc a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:187:theorem add (hf : AbsolutelyContinuousOnInterval f a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:204:theorem sub (hf : AbsolutelyContinuousOnInterval f a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:216:theorem const_mul {f : ℝ → ℝ} (α : ℝ) (hf : AbsolutelyContinuousOnInterval f a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:257:theorem smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean:288:theorem mul {f g : ℝ → ℝ}
.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Valuation.lean:54:theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Basic.lean:103:theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Basic.lean:105:theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Basic.lean:107:theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Basic.lean:115:theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:155:lemma mono {v : Filter ι} (huv : v ≤ l) (hg : TendstoInMeasure μ f l g) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:158:lemma comp {v : Filter κ} {ns : κ → ι} (hg : TendstoInMeasure μ f l g)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:386:theorem TendstoInMeasure.aestronglyMeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
.lake/packages/mathlib/Mathlib/FieldTheory/Fixed.lean:117:theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:385:theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
.lake/packages/mathlib/Mathlib/Data/Semiquot.lean:197:theorem IsPure.mono {s t : Semiquot α} (st : s ≤ t) (h : IsPure t) : IsPure s
.lake/packages/mathlib/Mathlib/Data/Semiquot.lean:217:theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
.lake/packages/mathlib/Mathlib/FieldTheory/Separable.lean:195:theorem Separable.mul {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g) :
.lake/packages/mathlib/Mathlib/Geometry/Diffeology/Basic.lean:251:theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
.lake/packages/mathlib/Mathlib/Geometry/Diffeology/Basic.lean:256:theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Holder.lean:188:protected lemma norm_smul_le (f : Lp 𝕜 p μ) (g : Lp E q μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Holder.lean:217:protected lemma smul_zero (f : Lp 𝕜 p μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Holder.lean:227:protected lemma zero_smul (f : Lp E q μ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/EvenFunction.lean:68:lemma Even.add [Add β] {f g : α → β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
.lake/packages/mathlib/Mathlib/Algebra/Group/EvenFunction.lean:72:lemma Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
.lake/packages/mathlib/Mathlib/Algebra/Group/EvenFunction.lean:158:lemma Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]
Poincare/Global/HeatKernel.lean:27:def heatKernel [FiniteDimensional ℝ E] (t : ℝ) (x : E) : ℝ :=
Poincare/Global/HeatKernel.lean:39:theorem heatKernel_nonneg [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
Poincare/Global/HeatKernel.lean:49:theorem contDiff_heatKernel_spatial [FiniteDimensional ℝ E] (t : ℝ) :
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean:219:protected alias vle.trans := vle_trans
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean:228:protected alias vle.trans' := vle_trans'
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean:828:lemma vlt.trans (hab : a <ᵥ b) (hbc : b <ᵥ c) : a <ᵥ c :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UniformIntegrable.lean:78:protected theorem aestronglyMeasurable {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UniformIntegrable.lean:105:protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UniformIntegrable.lean:125:protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UniformIntegrable.lean:153:protected theorem restrict (hf : UnifIntegrable f p μ) (E : Set α) :
.lake/packages/mathlib/Mathlib/Data/Sum/Order.lean:58:theorem LiftRel.trans [IsTrans α r] [IsTrans β s] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:69:theorem Integrable.aestronglyMeasurable {f : α → ε} (hf : Integrable f μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:86:theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:96:theorem Integrable.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:100:theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:162:theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c) μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:412:theorem Integrable.add' {f g : α → ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:420:theorem Integrable.add [ContinuousAdd ε']
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:540:theorem Integrable.sub {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:544:theorem Integrable.sub' {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:552:theorem Integrable.norm {f : α → β} (hf : Integrable f μ) : Integrable (fun a => ‖f a‖) μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:649:theorem Integrable.prodMk {f : α → β} {g : α → γ} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:963:theorem Integrable.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1011:theorem Integrable.smul_const {f : α → 𝕜} (hf : Integrable f μ) (c : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1037:theorem Integrable.const_mul {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1041:theorem Integrable.const_mul' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1046:theorem Integrable.mul_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1050:theorem Integrable.mul_const' {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1070:theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1095:theorem Integrable.div_const {f : α → 𝕜} (h : Integrable f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1171:lemma Integrable.restrict (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:148:protected theorem map_zero : v 0 = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:461:def restrict : Valuation R (MonoidWithZeroHom.ValueGroup₀ (v : R →*₀ Γ₀)) where
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:565:lemma IsEquiv.restrict {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:710:theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:713:theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ =>
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:1150:theorem map_zero : v 0 = (⊤ : Γ₀) :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:1312:theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:1316:theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/PresheafedSpace.lean:102:def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/PresheafedSpace.lean:264:def restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
.lake/packages/mathlib/Mathlib/Algebra/Group/Commute/Defs.lean:64:protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Commute/Defs.lean:191:protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:181:def exp (hI : DividedPowers I) (a : A) : PowerSeries A :=
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:185:theorem exp_add' (dp : ℕ → A → A)
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:193:theorem exp_add (hI : DividedPowers I) (ha : a ∈ I) (hb : b ∈ I) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:114:theorem HasFiniteIntegral.mono {f : α → β} {g : α → γ} (hg : HasFiniteIntegral g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:126:theorem HasFiniteIntegral.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : HasFiniteIntegral g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:130:theorem HasFiniteIntegral.mono' {f : α → β} {g : α → ℝ} (hg : HasFiniteIntegral g μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:266:theorem HasFiniteIntegral.norm {f : α → β} (hfi : HasFiniteIntegral f μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:455:theorem HasFiniteIntegral.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:488:theorem HasFiniteIntegral.const_mul [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:493:theorem HasFiniteIntegral.mul_const [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean:520:lemma HasFiniteIntegral.restrict (h : HasFiniteIntegral f μ) {s : Set α} :
.lake/packages/mathlib/Mathlib/FieldTheory/Galois/Basic.lean:292:instance fixedField.smul : SMul K (fixedField (fixingSubgroup K)) where
.lake/packages/mathlib/Mathlib/Data/Rel/Cover.lean:59:lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover U s N₁) : IsCover U s N₂ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean:76:theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean:81:theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean:91:theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/DPMorphism.lean:90:theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/DPMorphism.lean:223:protected def comp (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:129:def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:245:def restrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
.lake/packages/mathlib/Mathlib/FieldTheory/LinearDisjoint.lean:175:theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
.lake/packages/mathlib/Mathlib/FieldTheory/LinearDisjoint.lean:187:theorem LinearDisjoint.symm' (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/OpenImmersion.lean:151:instance mono : Mono f := by
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/OpenImmersion.lean:160:instance comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/OpenImmersion.lean:632:instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/OpenImmersion.lean:978:instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/OpenImmersion.lean:982:instance mono : Mono f :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Even.lean:141:lemma IsSquare.pow (n : ℕ) (ha : IsSquare a) : IsSquare (a ^ n) := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Even.lean:150:lemma IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) :=
.lake/packages/mathlib/Mathlib/Data/Holor.lean:130:def mul [Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t =>
.lake/packages/mathlib/Mathlib/Data/Holor.lean:157:theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/SheafedSpace.lean:178:def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Finsupp.lean:56:lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/Finsupp.lean:418:lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:288:def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:422:theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:478:theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:556:lemma smul_const [SMul K β] (k : K) (b : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:737:def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:1200:protected theorem add {β} [AddZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:1205:protected theorem mul {β} [MulZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Basic.lean:435:noncomputable def comp : Presentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:125:theorem mul_left_cancel : a * b = a * c → b = c :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:191:theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:224:lemma mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:258:theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:414:theorem mul_one : ∀ a : M, a * 1 = a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:978:def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:1077:theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:1224:theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/Stalks.lean:120:theorem comp {X Y Z : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:108:protected theorem StronglyMeasurable.aestronglyMeasurable (hf : StronglyMeasurable[m] f) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:135:theorem SimpleFunc.aestronglyMeasurable (f : α →ₛ β) : AEStronglyMeasurable f μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:185:theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:189:lemma mono {m'} (hm : m ≤ m') (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m'] f μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:197:protected theorem restrict (hfm : AEStronglyMeasurable[m] f μ) {s} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:231:protected theorem prodMk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable[m] f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:276:protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:281:protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:286:protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (c : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:321:protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:327:protected theorem pow [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable[m] f μ) (n : ℕ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:342:protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:461:protected theorem norm {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:837:protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:843:protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:854:protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:261:noncomputable def comp : PreSubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:539:noncomputable def comp : SubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:333:protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:353:protected theorem prodMk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:395:protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:400:theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:405:theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:410:protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : ℕ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:457:protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:473:protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:907:protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:1120:protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:1129:protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:1146:protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Generators.lean:218:def comp [Algebra S T] [IsScalarTower R S T]
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Generators.lean:466:noncomputable def Hom.comp [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Field.lean:54:theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:226:theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Basic.lean:263:noncomputable def Hom.comp (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Basic.lean:141:theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UnifTight.lean:95:protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/UnifTight.lean:123:protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Units.lean:95:lemma smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Units.lean:166:lemma IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommClass G M M] [IsScalarTower G M M]
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/TypeTags.lean:33:instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a := (a.toAdd +ᵥ ·)
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean:296:theorem mul_apply (φ ψ : A →ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Basic.lean:251:def Hom.sub (f g : Hom P P') : P.CotangentSpace →ₗ[S] P'.Cotangent := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/AEMeasurable.lean:105:theorem lpMeas.aestronglyMeasurable {m _ : MeasurableSpace α} {μ : Measure α}
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Equiv.lean:232:def symm (e : A ≃ₐc[R] B) : B ≃ₐc[R] A :=
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Equiv.lean:260:def trans (e₁₂ : A ≃ₐc[R] B) (e₂₃ : B ≃ₐc[R] C) : A ≃ₐc[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Equidecomp.lean:107:theorem IsDecompOn.mono {f f' : X → X} {A A' : Set X} {S : Finset G} (h : IsDecompOn f A S)
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Equidecomp.lean:153:theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Equidecomp.lean:163:theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Equidecomp.lean:171:noncomputable def trans (f g : Equidecomp X G) : Equidecomp X G where
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Equidecomp.lean:191:noncomputable def symm (f : Equidecomp X G) : Equidecomp X G where
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:73:lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:176:lemma SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul N α] [SMulCommClass M N α] :
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:287:def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:297:abbrev comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:313:lemma comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:324:lemma comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:335:lemma comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:416:lemma one_smul (b : α) : (1 : M) • b = b := MulAction.one_smul _
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/Basic.lean:148:def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/Basic.lean:153:def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/Basic.lean:158:def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α) :
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/GroupLike.lean:32:lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/GroupLike.lean:45:lemma IsGroupLikeElem.pow {n : ℕ} (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (a ^ n) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Pi.lean:34:instance smul' [∀ i, SMul (α i) (β i)] : SMul (∀ i, α i) (∀ i, β i) where smul s x i := s i • x i
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Pi.lean:41:lemma smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i :=
.lake/packages/mathlib/Mathlib/Data/Int/Cast/Basic.lean:75:theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:146:protected theorem aestronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:327:def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:415:def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:420:theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:426:theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:430:theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:450:def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:455:theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:462:theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:466:theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:518:theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:522:theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:114:def comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m where
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:121:def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:125:def comp.get (x : comp P Q α) : P (fun i => Q i α) :=
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:128:theorem comp.get_map (f : α ⟹ β) (x : comp P Q α) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:133:theorem comp.get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x := by
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:137:theorem comp.mk_get (x : comp P Q α) : comp.mk (comp.get x) = x := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Faithful.lean:122:lemma FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOneClass T]
.lake/packages/mathlib/Mathlib/Data/WSeq/Relation.lean:121:theorem LiftRel.symm (R : α → α → Prop) (H : Symmetric R) : Symmetric (LiftRel R) :=
.lake/packages/mathlib/Mathlib/Data/WSeq/Relation.lean:124:instance LiftRel.trans (R : α → α → Prop) [IsTrans α R] : IsTrans _ (LiftRel R) := by
.lake/packages/mathlib/Mathlib/Data/WSeq/Relation.lean:174:theorem Equiv.symm : ∀ {s t : WSeq α}, s ~ʷ t → t ~ʷ s :=
.lake/packages/mathlib/Mathlib/Data/WSeq/Relation.lean:178:theorem Equiv.trans : ∀ {s t u : WSeq α}, s ~ʷ t → t ~ʷ u → s ~ʷ u :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:123:theorem measurableSet_Icc [OrderClosedTopology α] : MeasurableSet (Icc a b) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:176:theorem Measurable.le' {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
.lake/packages/mathlib/Mathlib/Data/Int/Sqrt.lean:27:def sqrt (z : ℤ) : ℤ :=
.lake/packages/mathlib/Mathlib/Data/Rel.lean:148:def comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ := {(a, c) | ∃ b, a ~[R] b ∧ b ~[S] c}
.lake/packages/mathlib/Mathlib/Data/Rel.lean:372:instance IsRefl.comp [R₁.IsRefl] [R₂.IsRefl] : (R₁.comp R₂).IsRefl where
.lake/packages/mathlib/Mathlib/Data/Rel.lean:419:protected lemma symm [R.IsSymm] (hab : a ~[R] b) : b ~[R] a := symm_of (· ~[R] ·) hab
.lake/packages/mathlib/Mathlib/Data/Rel.lean:494:protected lemma trans [R.IsTrans] (hab : a ~[R] b) (hbc : b ~[R] c) : a ~[R] c :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean:248:theorem Measurable.norm {f : β → α} (hf : Measurable f) : Measurable fun a => norm (f a) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean:252:theorem AEMeasurable.norm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
.lake/packages/mathlib/Mathlib/FieldTheory/SplittingField/IsSplittingField.lean:94:theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:125:noncomputable def add : M →ₚₗ[R] N where
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:138:def smul : M →ₚₗ[R] N where
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:153:theorem zero_smul : (0 : R) • f = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:156:theorem one_smul : (1 : R) • f = f := by
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:267:def comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : M →ₚₗ[R] P where
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Projective.lean:151:theorem unique [∀ i, IsFiniteMeasure (P i)]
.lake/packages/mathlib/Mathlib/Data/Int/Order/Basic.lean:25:theorem le.elim (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
.lake/packages/mathlib/Mathlib/FieldTheory/PolynomialGaloisGroup.lean:115:def restrict [Fact ((p.map (algebraMap F E)).Splits)] : Gal(E/F) →* p.Gal :=
.lake/packages/mathlib/Mathlib/FieldTheory/PolynomialGaloisGroup.lean:153:instance smul [Fact ((p.map (algebraMap F E)).Splits)] : SMul p.Gal (rootSet p E) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/SMul.lean:47:theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl
.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean:140:theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
.lake/packages/mathlib/Mathlib/FieldTheory/IsPerfectClosure.lean:173:theorem IsPRadical.trans [IsPRadical i p] [IsPRadical f p] :
.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:100:theorem intValuation.map_zero' : v.intValuationDef 0 = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Lemmas.lean:324:theorem SemiconjBy.pi {x y z : ∀ i, f i} (h : ∀ i, SemiconjBy (x i) (y i) (z i)) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Pi/Lemmas.lean:333:theorem Commute.pi {x y : ∀ i, f i} (h : ∀ i, Commute (x i) (y i)) : Commute x y := SemiconjBy.pi h
.lake/packages/mathlib/Mathlib/FieldTheory/Perfect.lean:60:instance mul : PerfectRing M (p * q) :=
.lake/packages/mathlib/Mathlib/FieldTheory/Perfect.lean:63:instance pow (n : ℕ) : PerfectRing M (p ^ n) :=
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:79:protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:83:protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:144:protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:175:protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] := by
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:192:protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
.lake/packages/mathlib/Mathlib/Data/Int/ModEq.lean:227:protected theorem mul_left_cancel' (hc : c ≠ 0) :
.lake/packages/mathlib/Mathlib/FieldTheory/SeparableDegree.lean:835:theorem Algebra.IsSeparable.trans [Algebra E K] [IsScalarTower F E K]
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:54:def mul : (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) :=
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:103:protected lemma mul_one (x : ⨂[R] i, A i) : mul x (tprod R 1) = x := by
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:128:protected lemma mul_assoc (x y z : ⨂[R] i, A i) : mul (mul x y) z = mul x (mul y z) := by
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:245:protected lemma mul_comm (x y : ⨂[R] i, A i) : mul x y = mul y x := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Conj.lean:40:theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
.lake/packages/mathlib/Mathlib/Algebra/Group/Conj.lean:48:theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
.lake/packages/mathlib/Mathlib/Algebra/Group/Conj.lean:52:theorem IsConj.pow {a b : α} (n : ℕ) : IsConj a b → IsConj (a ^ n) (b ^ n)
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:108:protected def pi (m : ∀ i, OuterMeasure (α i)) : OuterMeasure (∀ i, α i) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:183:def pi' : Measure (∀ i, α i) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:186:theorem pi'_pi [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:237:def FiniteSpanningSetsIn.pi {C : ∀ i, Set (Set (α i))}
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:289:theorem pi'_eq_pi [Encodable ι] [∀ i, SigmaFinite (μ i)] : pi' μ = Measure.pi μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:305:instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:313:instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:336:instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:532:instance pi.isLocallyFiniteMeasure
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:568:instance pi.isMulLeftInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:582:instance pi.isMulRightInvariant [∀ i, Group (α i)] [∀ i, MeasurableMul (α i)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:597:instance pi.isInvInvariant [∀ i, Group (α i)] [∀ i, MeasurableInv (α i)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:610:instance pi.isOpenPosMeasure [∀ i, TopologicalSpace (α i)] [∀ i, IsOpenPosMeasure (μ i)] :
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:626:instance pi.isFiniteMeasureOnCompacts [∀ i, TopologicalSpace (α i)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean:644:instance pi.isHaarMeasure [∀ i, Group (α i)] [∀ i, TopologicalSpace (α i)]
.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:538:theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O}
.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:653:theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' where
Poincare/Global/CartanCanonicalFamilyProvenanceLocalUniformData.lean:152:theorem TransferredNormalRadiusAdmissible.mono
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:101:theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:679:theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:775:theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
.lake/packages/mathlib/Mathlib/Data/Finsupp/Defs.lean:143:theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
.lake/packages/mathlib/Mathlib/Data/Sigma/Lex.lean:63:theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i}
.lake/packages/mathlib/Mathlib/Data/Sigma/Lex.lean:162:theorem Lex.mono {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
Poincare/Global/BoundedUniformContinuousHeat.lean:135:theorem heatKernel_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:201:theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:234:theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:244:theorem IsHermitian.smul {A : Matrix n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:325:theorem IsHermitian.pow [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : ℕ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Defs.lean:560:protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Basic.lean:304:protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:56:def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:122:instance CompatibleSMul.pi (R S M N ι : Type*) [Semiring S]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:375:def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean:75:theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean:119:theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean:123:theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean:127:theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
.lake/packages/mathlib/Mathlib/RingTheory/SurjectiveOnStalks.lean:107:lemma SurjectiveOnStalks.comp (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f) :
.lake/packages/mathlib/Mathlib/Data/Finmap.lean:580:theorem Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjoint y x := fun p hy hx => h p hx hy
.lake/packages/mathlib/Mathlib/Algebra/Group/ULift.lean:40:instance mul [Mul α] : Mul (ULift α) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/ULift.lean:64:instance pow [Pow α β] : Pow (ULift α) β :=
.lake/packages/mathlib/Mathlib/FieldTheory/PurelyInseparable/Basic.lean:260:theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:150:theorem RingHom.IsIntegralElem.add (f : R →+* S) {x y : S}
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:183:theorem RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:191:theorem RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:200:theorem IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Algebra S B] [Algebra R S]
.lake/packages/mathlib/Mathlib/Data/Finsupp/Pointwise.lean:50:theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/MulAction.lean:78:instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
.lake/packages/mathlib/Mathlib/Data/Finsupp/SMulWithZero.lean:59:theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
.lake/packages/mathlib/Mathlib/FieldTheory/Differential/Liouville.lean:56:lemma IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A]
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Membership.lean:376:def pow (n : M) (m : ℕ) : powers n :=
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:223:theorem IsIntegral.pow {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x ^ n) :=
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:503:protected theorem Algebra.IsIntegral.trans
.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:507:protected theorem RingHom.IsIntegral.trans
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:94:theorem BlockTriangular.add [AddZeroClass R] (hM : BlockTriangular M b) (hN : BlockTriangular N b) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:97:theorem BlockTriangular.sub [SubNegZeroMonoid R]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:117:lemma BlockTriangular.comp [Zero R] {M : Matrix m m (Matrix n n R)} (h : BlockTriangular M b) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean:179:theorem BlockTriangular.mul [Fintype m] [NonUnitalNonAssocSemiring R]
.lake/packages/mathlib/Mathlib/Data/Num/ZNum.lean:136:theorem add_zero (n : ZNum) : n + 0 = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/ZNum.lean:138:theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/ZNum.lean:434:private theorem mul_comm : ∀ (a b : ZNum), a * b = b * a := by transfer
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Defs.lean:436:instance mul : Mul S :=
.lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean:64:theorem symm (h : PythagoreanTriple x y z) : PythagoreanTriple y x z := by
.lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean:69:theorem mul (h : PythagoreanTriple x y z) (k : ℤ) : PythagoreanTriple (k * x) (k * y) (k * z) :=
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:93:protected def add : PosNum → PosNum → PosNum
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:127:protected def mul (a : PosNum) : PosNum → PosNum
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:220:protected def add : Num → Num → Num
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:253:protected def mul : Num → Num → Num
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:359:def sub' : PosNum → PosNum → ZNum
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:379:protected def sub (a b : PosNum) : PosNum :=
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:420:def sub' : Num → Num → ZNum
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:431:protected def sub (a b : Num) : Num :=
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:444:protected def add : ZNum → ZNum → ZNum
.lake/packages/mathlib/Mathlib/Data/Num/Basic.lean:456:protected def mul : ZNum → ZNum → ZNum
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean:247:protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean:253:protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Defs.lean:259:protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Operations.lean:710:def restrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Operations.lean:994:def pi (I : Set ι) (S : ∀ i, Submonoid (M i)) : Submonoid (∀ i, M i) where
.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean:185:theorem add_zero (n : Num) : n + 0 = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean:187:theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean:697:theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum := by cases a <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean:884:instance SNum.le : LE SNum :=
Poincare/Global/HeatKernelHessianMoments.lean:34:theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
Poincare/Global/HeatKernelHessianMoments.lean:142:theorem integrable_hessian {t : ℝ} (ht : 0 < t) :
Poincare/Global/HeatKernelHessianMoments.lean:151:theorem integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
.lake/packages/mathlib/Mathlib/Data/Fin/Fin2.lean:72:def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Locus.lean:53:lemma IsUnramifiedAt.comp
.lake/packages/mathlib/Mathlib/Data/Num/Bitwise.lean:425:protected def add (a b : SNum) : SNum :=
.lake/packages/mathlib/Mathlib/Data/Num/Bitwise.lean:432:protected def sub (a b : SNum) : SNum :=
.lake/packages/mathlib/Mathlib/Data/Num/Bitwise.lean:439:protected def mul (a : SNum) : SNum → SNum :=
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:216:theorem comp [FormallyUnramified R A] [FormallyUnramified A B] :
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:391:theorem comp [Algebra A B] [IsScalarTower R A B] [Unramified R A] [Unramified A B] :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:151:instance add [Add α] : Add (Matrix m n α) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:179:instance sub [Sub α] : Sub (Matrix m n α) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:189:instance unique [Unique α] : Unique (Matrix m n α) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:198:instance smul [SMul R α] : SMul R (Matrix m n α) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:226:theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:229:theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:233:theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:237:theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:279:protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basic.lean:113:theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basic.lean:138:theorem lift.unique {g : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = f' x y) : g = lift f' :=
.lake/packages/mathlib/Mathlib/RingTheory/Flat/Stability.lean:62:theorem trans [Flat R S] [Flat S M] : Flat R M := by
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:412:protected def norm : (mixedSpace K) →*₀ ℝ where
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:421:protected theorem norm_nonneg (x : mixedSpace K) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:466:protected theorem continuous_norm : Continuous (mixedEmbedding.norm : (mixedSpace K) → ℝ) := by
Poincare/Global/SemilinearHeatBUCLocalDataOperations.lean:97:def add {N M : BUC → BUC}
Poincare/Global/SemilinearHeatBUCLocalDataOperations.lean:131:def sub {N M : BUC → BUC}
Poincare/Global/SemilinearHeatBUCLocalDataOperations.lean:148:def comp {N M : BUC → BUC}
Poincare/Global/HeatKernelIntegral.lean:87:def heatSolution (t : ℝ) (f : E → ℝ) : E → ℝ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean:226:lemma IsParabolic.pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
.lake/packages/mathlib/Mathlib/Algebra/Group/Prod.lean:336:def inr : N →* M × N :=
.lake/packages/mathlib/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean:545:theorem trans : FaithfullyFlat R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Prod.lean:137:def inr : M₂ →ₗ[R] M × M₂ :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Units/Basic.lean:124:protected theorem norm [NumberField K] (x : (𝓞 K)ˣ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Equiv/Defs.lean:285:def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Equiv/Defs.lean:405:def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean:333:def restrict (f : M → K) (h : ∀ x, IsIntegral ℤ (f x)) (x : M) : 𝓞 K :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/LinearMap.lean:103:theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/LinearMap.lean:118:theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/LinearMap.lean:126:theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:205:lemma HasUnifEigenvalue.pow {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : ℕ) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:306:lemma HasUnifEigenvalue.le {f : End R M} {μ : R} {k m : ℕ∞}
.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:463:lemma HasEigenvalue.pow {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Data/Rat/Sqrt.lean:29:def sqrt (q : ℚ) : ℚ := mkRat (Int.sqrt q.num) (Nat.sqrt q.den)
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean:537:lemma IsUnramifiedAtInfinitePlaces.trans
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:236:lemma IsReal.comp (f : k →+* K) {φ : K →+* ℂ} (hφ : IsReal φ) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:285:lemma IsConj.symm (hσ : IsConj φ σ) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:295:theorem IsConj.comp (hσ : IsConj φ σ) (ν : Gal(K/k)) :
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:237:theorem mul_apply (n : ℕ) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:297:instance smul : SMul (AdicCompletion I R) (AdicCompletion I M) where
.lake/packages/mathlib/Mathlib/Algebra/Group/Invertible/Defs.lean:237:abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
.lake/packages/mathlib/Mathlib/Algebra/Group/TransferInstance.lean:42:protected abbrev mul [Mul β] : Mul α where mul x y := e.symm (e x * e y)
.lake/packages/mathlib/Mathlib/Algebra/Group/TransferInstance.lean:74:protected abbrev pow [Pow β M] : Pow α M where pow x n := e.symm (e x ^ n)
.lake/packages/mathlib/Mathlib/Data/ENat/Basic.lean:404:protected lemma sub_sub_cancel (h : a ≠ ⊤) (h2 : b ≤ a) : a - (a - b) = b :=
.lake/packages/mathlib/Mathlib/Data/ENat/Basic.lean:509:protected theorem map_zero (f : ℕ → α) : map f 0 = f 0 := rfl
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:103:theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:189:theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:250:theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:424:instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:482:theorem zero_apply (n : ℕ) : (0 : AdicCauchySequence I M) n = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:488:theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:492:theorem sub_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:496:theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean:128:theorem flip_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean:215:theorem map_zero₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (y) : f 0 y = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Functoriality.lean:98:theorem map_zero : map I (0 : M →ₗ[R] N) = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Functoriality.lean:169:theorem map_zero : map I (0 : M →ₗ[R] N) = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Functoriality.lean:216:def pi : AdicCompletion I (∀ j, M j) →ₗ[AdicCompletion I R] ∀ j, AdicCompletion I (M j) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Module.lean:56:lemma smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/CompTypeclasses.lean:87:theorem comp {φ : M →* N} {ψ : N →* P} :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/CompTypeclasses.lean:91:lemma comp_apply
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:101:protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:106:protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:255:protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:271:protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:324:protected lemma pow [StarOrderedRing R] [DecidableEq n]
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:752:def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P where
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:758:def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P where
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:765:def MonoidHom.comp [MulOne M] [MulOne N] [MulOne P] (hnp : N →* P) (hmn : M →* N) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:784:theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:788:theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:792:theorem MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne P]
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:917:theorem Function.Surjective.mul_comm [Mul M] [Mul N] {f : M →ₙ* N} (is_surj : Function.Surjective f)
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:88:theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:99:theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:105:theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:226:theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:272:instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Interval.lean:132:def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) := f.support.dfinsupp f
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Internal.lean:420:theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Basic.lean:93:theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Basic.lean:156:theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Basic.lean:239:instance mul : Mul (M →* N) :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Module.lean:37:theorem smul_apply [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Ring.lean:233:private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Ring.lean:309:private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Instances.lean:149:theorem AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M) m = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Instances.lean:197:theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Module.lean:56:theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Module.lean:127:theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i ↦ ψ.comp <| lof R ι M i) f :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/IsDiag.lean:84:theorem IsDiag.add [AddZeroClass α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/IsDiag.lean:89:theorem IsDiag.sub [SubtractionMonoid α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/IsDiag.lean:94:theorem IsDiag.smul [Zero α] [SMulZeroClass R α] (k : R) {A : Matrix n n α}
.lake/packages/mathlib/Mathlib/Data/Part.lean:550:def restrict (p : Prop) (o : Part α) (H : p → o.Dom) : Part α :=
.lake/packages/mathlib/Mathlib/Algebra/GradedMonoid.lean:296:instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where
.lake/packages/mathlib/Mathlib/Algebra/GradedMonoid.lean:311:theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
.lake/packages/mathlib/Mathlib/Algebra/GradedMonoid.lean:657:theorem SetLike.IsHomogeneousElem.mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Norm.lean:49:noncomputable def norm : 𝓞 L →* 𝓞 K :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:177:theorem map_zero [Nonempty ι] : f 0 = 0 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:197:theorem zero_apply (m : ∀ i, M₁ i) : (0 : MultilinearMap R M₁ M₂) m = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:210:theorem smul_apply (f : MultilinearMap R M₁ M₂) (c : S) (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:255:def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:1303:theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
.lake/packages/mathlib/Mathlib/Data/QPF/Univariate/Basic.lean:196:theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
.lake/packages/mathlib/Mathlib/Data/QPF/Univariate/Basic.lean:459:def comp : QPF (Functor.Comp F₂ F₁) where
.lake/packages/mathlib/Mathlib/Algebra/Group/UniqueProds/Basic.lean:75:theorem mono {A' B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (h : UniqueMul A' B' a0 b0) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/PerfectPairing/Restrict.lean:73:lemma IsPerfPair.restrict : (p.compl₁₂ i j).IsPerfPair where
Poincare/Global/ParabolicHolderSpace.lean:418:def restrict {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F) : Y (E := E) α T' F := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Opposite.lean:266:instance pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)
.lake/packages/mathlib/Mathlib/Algebra/Group/Idempotent.lean:64:lemma mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Idempotent.lean:83:lemma pow (n : ℕ) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n) :=
.lake/packages/mathlib/Mathlib/Data/QPF/Multivariate/Constructions/Fix.lean:112:theorem wEquiv.symm {α : TypeVec n} (x y : q.P.W α) : WEquiv x y → WEquiv y x := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:57:theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:89:theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:104:theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:119:theorem mul {I : Ideal A} {x₁ x₂ y₁ y₂ : A} (hxy₁ : x₁ ≡ y₁ [SMOD I])
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:135:lemma pow {I : Ideal A} {x y : A} (n : ℕ) (hxy : x ≡ y [SMOD I]) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Basic.lean:145:lemma sub (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ - x₂ ≡ y₁ - y₂ [SMOD U] := by
.lake/packages/mathlib/Mathlib/Algebra/Group/ModEq.lean:73:protected theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
.lake/packages/mathlib/Mathlib/Algebra/Group/ModEq.lean:83:protected theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
.lake/packages/mathlib/Mathlib/Algebra/Group/ModEq.lean:108:protected theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/SModEq/Pointwise.lean:33:theorem smul' (hxy : x ≡ y [SMOD U])
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:218:protected lemma IsSymm.add {C : M →ₛₗ[I] M →ₗ[R] R} (hB : B.IsSymm) (hC : C.IsSymm) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:247:protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₛₗ[I₂] R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:251:protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} {c : R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:268:protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₗ[R] R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:477:theorem IsAdjointPair.add {f f' : M → M₁} {g g' : M₁ → M} (h : IsAdjointPair B B' f g)
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:482:theorem IsAdjointPair.comp {f : M → M₁} {g : M₁ → M} {f' : M₁ → M₂} {g' : M₂ → M₁}
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:487:theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:502:theorem IsAdjointPair.sub (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
.lake/packages/mathlib/Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:506:theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B' f g) :
.lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Basic.lean:190:def norm : QuadraticAlgebra R a b →* R where
.lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Basic.lean:226:theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
.lake/packages/mathlib/Mathlib/RingTheory/FinitePresentation.lean:182:theorem trans [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
.lake/packages/mathlib/Mathlib/RingTheory/FinitePresentation.lean:438:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
.lake/packages/mathlib/Mathlib/RingTheory/FinitePresentation.lean:536:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Semisimple.lean:173:lemma IsSemisimple.restrict {p : Submodule R M} (hp : p ∈ f.invtSubmodule) (hf : f.IsSemisimple) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Semisimple.lean:202:lemma IsFinitelySemisimple.restrict {p : Submodule R M} (hp : p ∈ f.invtSubmodule)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Semisimple.lean:274:protected theorem IsSemisimple.pow (n : ℕ) : (f ^ n).IsSemisimple :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Finsupp/VectorSpace.lean:173:lemma Module.Free.trans {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
.lake/packages/mathlib/Mathlib/Algebra/Category/Semigrp/Basic.lean:155:lemma comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Semigrp/Basic.lean:318:lemma comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:89:theorem map_zero (f : E →ₛₗ.[σ] F) : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:211:instance le : LE (E →ₛₗ.[σ] F) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:368:theorem zero_apply (x : (⊤ : Submodule R E)) : (0 : E →ₛₗ.[σ] F) x = 0 := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:386:theorem smul_apply (a : M) (f : E →ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:431:theorem add_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:501:theorem sub_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:687:def comp {ρ : R →+* T} [RingHomCompTriple σ τ ρ] (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F)
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:223:protected theorem map_zero {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:254:def mul (χ χ' : MulChar R R') : MulChar R R' :=
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:262:theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:273:protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:372:noncomputable def restrict {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:465:theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' →+* R'') :
.lake/packages/mathlib/Mathlib/Data/Sym/Sym2.lean:70:theorem Rel.symm {x y : α × α} : Rel α x y → Rel α y x := by aesop (rule_sets := [Sym2])
.lake/packages/mathlib/Mathlib/Data/Sym/Sym2.lean:73:theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
.lake/packages/mathlib/Mathlib/Data/Sym/Sym2.lean:949:def mul {M} [CommMagma M] : Sym2 M → M := lift ⟨(· * ·), mul_comm⟩
.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:223:theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:158:theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:273:theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:689:lemma sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/NormalForms.lean:144:theorem mono {n} (hmn : m ≤ n) (hL : IsAdmissible m L) : IsAdmissible n L :=
.lake/packages/mathlib/Mathlib/NumberTheory/FunctionField.lean:146:alias InftyValuation.map_zero' := RatFunc.InftyValuation.map_zero'
.lake/packages/mathlib/Mathlib/LinearAlgebra/PiTensorProduct.lean:416:theorem liftAux.smul {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/PiTensorProduct.lean:449:theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E}
.lake/packages/mathlib/Mathlib/LinearAlgebra/PiTensorProduct.lean:453:theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (PiTensorProduct.tprod R f) = φ f) :
.lake/packages/mathlib/Mathlib/Data/Sym/Basic.lean:362:theorem map_zero (f : α → β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
Poincare/Global/HeatCauchyNext2.lean:32:theorem norm_real_smul_continuousLinearMap_two_le
Poincare/Global/HeatCauchyNext2.lean:66:theorem iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Monoidal.lean:162:def inr (x y : AugmentedSimplexCategory) : y ⟶ x ⊗ y :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Monoidal.lean:171:abbrev inr' (x y : SimplexCategory) : y ⟶ tensorObjOf x y := WithInitial.down <| inr (.of x) (.of y)
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Monoidal.lean:182:lemma inr'_eval (x y : SimplexCategory) (i : Fin (y.len + 1)) :
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Smooth.lean:44:lemma FormallySmooth.comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Smooth.lean:103:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.comp f).Smooth := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Ray.lean:96:theorem symm (h : SameRay R x y) : SameRay R y x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Ray.lean:110:theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 → x = 0 ∨ z = 0) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Ray.lean:183:theorem smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
Poincare/Global/ClosedRiemannianBallVolumeLower.lean:254:theorem UniformClosedRiemannianBallVolumeLower.comp
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean:109:def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Basic.lean:82:protected lemma Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/EssFiniteType.lean:23:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Hom.lean:116:def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M := B.compl₁₂ l r
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Hom.lean:142:theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Field/Basic.lean:177:theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
.lake/packages/mathlib/Mathlib/Algebra/Order/Field/Basic.lean:180:theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f) {c : α}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:68:protected theorem smul {α : Type*} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:102:protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:105:protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:111:protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:116:theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:198:protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:202:protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:225:protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:229:protected lemma IsPosSemidef.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:249:protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:252:protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Properties.lean:258:protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
.lake/packages/mathlib/Mathlib/Algebra/Category/MonCat/Basic.lean:151:lemma comp_apply {M N T : MonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Category/MonCat/Basic.lean:332:lemma comp_apply {M N T : CommMonCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:203:theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:207:lemma LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t ⊆ s) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/IsometryEquiv.lean:85:def symm (f : B₁.IsometryEquiv B₂) : B₂.IsometryEquiv B₁ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/IsometryEquiv.lean:93:def trans (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) : B₁.IsometryEquiv B₃ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/IsometryEquiv.lean:115:theorem symm (h : B₁.Equivalent B₂) : B₂.Equivalent B₁ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/IsometryEquiv.lean:119:theorem trans (h : B₁.Equivalent B₂) (h' : B₂.Equivalent B₃) : B₁.Equivalent B₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Archimedean.lean:90:private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:94:lemma IsStandardSmooth.comp {g : S →+* T} {f : R →+* S}
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/StandardSmooth.lean:101:lemma IsStandardSmoothOfRelativeDimension.comp {g : S →+* T} {f : R →+* S}
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:105:theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:111:theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:119:theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:135:theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:152:def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearDisjoint.lean:311:theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/OpenImmersion.lean:91:lemma comp (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:100:lemma HomotopicL.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:108:lemma HomotopicL.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
.lake/packages/mathlib/Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:122:lemma HomotopicR.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:130:lemma HomotopicR.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
.lake/packages/mathlib/Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:183:noncomputable def Edge.comp (f : Edge x y) (g : Edge y z) : Edge x z :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Isometry.lean:101:def comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) : B₁ →bᵢ B₃ where
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/QuasiFinite.lean:37:lemma QuasiFinite.comp {f : S →+* T} {g : R →+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite) :
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Flat.lean:45:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
.lake/packages/mathlib/Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean:88:theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Unramified.lean:48:lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyUnramified)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean:98:instance QuotientTop.unique : Unique (M ⧸ (⊤ : Submodule R M)) where
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:226:theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:230:theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/StandardPart.lean:185:private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:65:theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:68:alias mul_nonneg := Left.mul_nonneg
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:74:theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:346:lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:350:lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:478:lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:481:lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:484:lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:487:lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:520:lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:597:lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:600:lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:603:lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:606:lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:617:lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:872:lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:206:theorem unique {ζ : M} (hk : IsPrimitiveRoot ζ k) (hl : IsPrimitiveRoot ζ l) : k = l :=
.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:248:theorem pow {n : ℕ} {a b : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (hprod : n = a * b) :
.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Complex.lean:132:theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:26:theorem third_apply {t : ℝ} (ht : t ≠ 0) (x u v w : E) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:57:theorem norm_third_one_le (x : E) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:93:theorem integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:138:theorem third_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:148:theorem weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:157:theorem weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:173:theorem integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:183:theorem weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:199:theorem third_moment_bound :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:213:theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:232:theorem near_hessian_difference_le {α K a t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:267:theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:285:theorem far_time_power_integral_le {α ρ t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:321:theorem hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:344:theorem hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:363:theorem norm_hessian_translation_le (t : ℝ) (y w : E) :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:389:theorem weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:427:theorem integrable_segment_weighted_third {α t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:459:theorem weighted_hessian_translation {α t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:510:theorem weighted_hessian_translation_far {α t : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:541:theorem norm_heat_hessian_difference_far_le {α t M K : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:574:theorem far_hessian_difference_le {α T t M K : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:638:theorem duhamel_hessian_spatial_holder :
.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Basic.lean:77:lemma FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith R m) :
.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Basic.lean:84:lemma FermatLastTheoremFor.mono (hmn : m ∣ n) (hm : FermatLastTheoremFor m) :
.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Four.lean:38:theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean:133:def comp (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Finset.lean:56:lemma mul₀_sup' [PosMulReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
.lake/packages/mathlib/Mathlib/Combinatorics/Hall/Basic.lean:63:def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Basic.lean:118:lemma comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Basic.lean:284:lemma comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Basic.lean:459:lemma comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Ring/Basic.lean:632:lemma comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106:lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:110:lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:113:lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:189:private lemma le : m₁ ≤ m₂ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:188:theorem map_zero [Nonempty ι] : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:215:theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:250:def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:282:theorem add_apply : (f + f') v = f v + f' v :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:294:theorem zero_apply : (0 : M [⋀^ι]→ₗ[R] N) v = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:332:theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
.lake/packages/mathlib/Mathlib/Algebra/Order/AbsoluteValue/Basic.lean:128:protected theorem map_zero : abv 0 = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/FinitePresentationLocal.lean:135:instance pi {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:420:def norm (n : ℤ√d) : ℤ :=
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:440:theorem norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m := by
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:454:theorem norm_neg (x : ℤ√d) : (-x).norm = x.norm :=
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:461:theorem norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:573:theorem Nonneg.add {a b : ℤ√d} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a + b) := by
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:723:protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Star/Basic.lean:174:lemma IsSelfAdjoint.mono {x y : R} (h : x ≤ y) (hx : IsSelfAdjoint x) : IsSelfAdjoint y := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Star/Basic.lean:188:alias LE.le.isSelfAdjoint := IsSelfAdjoint.of_nonneg
.lake/packages/mathlib/Mathlib/Algebra/Order/Star/Basic.lean:191:lemma LE.le.star_eq {x : R} (hx : 0 ≤ x) : star x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Star/Basic.lean:364:protected theorem IsSelfAdjoint.sq_nonneg {a : R} (ha : IsSelfAdjoint a) : 0 ≤ a ^ 2 := by
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:138:theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
.lake/packages/mathlib/Mathlib/Algebra/Category/CommAlgCat/Basic.lean:104:lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
.lake/packages/mathlib/Mathlib/Combinatorics/SetFamily/Intersecting.lean:50:theorem Intersecting.mono (h : t ⊆ s) (hs : s.Intersecting) : t.Intersecting := fun _a ha _b hb =>
.lake/packages/mathlib/Mathlib/Combinatorics/SetFamily/Intersecting.lean:224:theorem mono (h : L ⊆ L') (hL : IsIntersectingOf L 𝒜) : IsIntersectingOf L' 𝒜 := by tauto
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Ideal.lean:96:theorem FG.mul {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG) : (I * J).FG :=
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Ideal.lean:99:theorem FG.pow {I : Ideal R} [I.IsTwoSided] {n : ℕ} (hI : I.FG) : (I ^ n).FG :=
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:279:instance pi {ι : Type*} {M : ι → Type*} [_root_.Finite ι] [∀ i, AddCommMonoid (M i)]
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:367:theorem trans {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:468:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:495:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:461:theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:528:theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:132:theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun _ ε0 =>
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:139:lemma mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:206:theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:245:theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:260:theorem const_add (x y : β) : const (x + y) = const x + const y :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:270:theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:273:theorem const_mul (x y : β) : const (x * y) = const x * const y :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:297:theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:315:theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:556:theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
.lake/packages/mathlib/Mathlib/Algebra/Order/Sub/WithTop.lean:37:protected def sub : ∀ _ _ : WithTop α, WithTop α
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Completion.lean:226:protected theorem mul_inv_cancel {x : (Cauchy abv)} : x ≠ 0 → x * x⁻¹ = 1 :=
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/FreimanHom.lean:270:lemma IsMulFreimanHom.mono (hmn : m ≤ n) (hf : IsMulFreimanHom n A B f) :
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/FreimanHom.lean:302:lemma IsMulFreimanIso.mono {hmn : m ≤ n} (hf : IsMulFreimanIso n A B f) :
.lake/packages/mathlib/Mathlib/Algebra/Order/ZeroLEOne.lean:36:lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Order/ZeroLEOne.lean:59:lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one
Poincare/Global/DifferentialSuccessorEqualityStabilityReduction.lean:225:theorem ActualSuccessorEqualityRadiusAdmissible.mono
.lake/packages/mathlib/Mathlib/Algebra/Order/UpperLower.lean:45:theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) := hs.image <| OrderIso.mulLeft _
.lake/packages/mathlib/Mathlib/Algebra/Order/UpperLower.lean:48:theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) := hs.image <| OrderIso.mulLeft _
.lake/packages/mathlib/Mathlib/Algebra/Order/UpperLower.lean:51:theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected := by
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Subalgebra.lean:54:theorem FG.mul (hm : M.FG) (hn : N.FG) : (M * N).FG := by
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Subalgebra.lean:57:theorem FG.pow (h : M.FG) (n : ℕ) : (M ^ n).FG :=
.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:94:theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:251:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:297:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/CovBySMul.lean:49:lemma CovBySMul.mono (hKL : K ≤ L) : CovBySMul M K A B → CovBySMul M L A B := by
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/ApproximateSubgroup.lean:80:lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean:83:def symm (f : Q₁.IsometryEquiv Q₂) : Q₂.IsometryEquiv Q₁ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean:89:def trans (f : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₃) : Q₁.IsometryEquiv Q₃ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean:119:theorem symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean:123:theorem trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Stalk.lean:42:def colimit.smul (r : (R ⋙ forget _).ColimitType) (m : (M ⋙ forget _).ColimitType) :
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/NonZeroDivisors.lean:74:protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:123:lemma zero_apply (x : E₁) : (0 : E₁ →ₚ[R] E₂) x = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:138:lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:82:private def add'' (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:85:private theorem add''_char (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:107:private def add' (r₂ : X) (s₂ : S) : X[S⁻¹] → X[S⁻¹] :=
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:131:private def add : X[S⁻¹] → X[S⁻¹] → X[S⁻¹] := fun x =>
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:198:protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:202:protected theorem add_zero (x : X[S⁻¹]) : x + 0 = x := by
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:218:protected theorem smul_zero (x : R[S⁻¹]) : x • (0 : X[S⁻¹]) = 0 := by
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/Corner/Defs.lean:57:lemma IsCorner.mono (hAB : A ⊆ B) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner B x₁ y₁ x₂ y₂ where
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/Corner/Defs.lean:63:lemma IsCornerFree.mono (hAB : A ⊆ B) (hB : IsCornerFree B) : IsCornerFree A :=
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Ring.lean:34:protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean:129:lemma ne (x : P.I) (y : P.II) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean:137:lemma le [P.IsProper] (x : P.II) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:240:protected theorem map_zero : Q 0 = 0 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:415:theorem smul_apply (a : S) (Q : QuadraticMap R M N) (x : M) : (a • Q) x = a • Q x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:436:theorem zero_apply (x : M) : (0 : QuadraticMap R M N) x = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:457:theorem add_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q + Q') x = Q x + Q' x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:541:theorem sub_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q - Q') x = Q x - Q' x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:576:def comp (Q : QuadraticMap R N P) (f : M →ₗ[R] N) : QuadraticMap R M P where
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:584:theorem comp_apply (Q : QuadraticMap R N P) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:1142:theorem PosDef.smul {R} [CommSemiring R] [PartialOrder R]
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:1172:theorem PosDef.add [AddLeftStrictMono N]
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/AP/Three/Defs.lean:83:theorem ThreeGPFree.mono (h : t ⊆ s) (hs : ThreeGPFree s) : ThreeGPFree t :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean:131:lemma strongAnodyneExtensions.mono {X Y : SSet.{u}} {f : X ⟶ Y}
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/IsUniquelyCodimOneFace.lean:90:lemma le : x ≤ y := by
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/IsUniquelyCodimOneFace.lean:98:lemma unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
.lake/packages/mathlib/Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:138:theorem map_zero (d : ℕ) (a : Fin 0 → ℕ) : map d a = 0 := by simp [map]
Poincare/Global/HeatSemigroupBUCGeneratorEvolution.lean:31:theorem IsInBUCHeatGeneratorDomain.unique
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:99:protected theorem symm {x y} : c x y → c y x :=
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:102:protected theorem trans {x y z} : c x y → c y z → c x z :=
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:105:protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:108:protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:111:protected theorem sub {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:388:protected theorem symm {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Prod.lean:77:def Isometry.inr (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : Q₂ →qᵢ (Q₁.prod Q₂) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Prod.lean:244:def pi [Fintype ι] (Q : ∀ i, QuadraticMap R (Mᵢ i) P) : QuadraticMap R (∀ i, Mᵢ i) P :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Prod.lean:261:def IsometryEquiv.pi [Fintype ι]
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Prod.lean:300:theorem Equivalent.pi [Fintype ι] {Q : ∀ i, QuadraticMap R (Mᵢ i) P}
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean:94:def comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) : Q₁ →qᵢ Q₃ where
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Semi.lean:137:lemma comp_apply {M N O : SemimoduleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:65:def symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:73:noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:111:abbrev symm {f g : X ⟶ Y} (h : P.LeftHomotopy f g) : P.symm.LeftHomotopy g f :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:137:noncomputable abbrev trans [IsCofibrant X] {f₀ f₁ f₂ : X ⟶ Y}
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:232:lemma symm [CategoryWithWeakEquivalences C]
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean:237:lemma trans [ModelCategory C]
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Symmetric.lean:69:lemma smul (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Symmetric.lean:90:def smul' (r : R) : Sym[R] ι M →+ Sym[R] ι M :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean:62:lemma IsCusp.smul {c : OnePoint ℝ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (hc : IsCusp c 𝒢)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean:93:lemma IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ} (hGH : 𝒢 ≤ ℋ)
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:71:def symm : Precylinder A where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:80:noncomputable def trans (P' : Precylinder A) [HasPushout P.i₁ P'.i₀] :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:126:def symm : Cylinder A where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:246:noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] :
.lake/packages/mathlib/Mathlib/NumberTheory/DirichletCharacter/Basic.lean:148:theorem FactorsThrough.mono {d m : ℕ} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
.lake/packages/mathlib/Mathlib/NumberTheory/DirichletCharacter/Basic.lean:204:lemma map_zero' (hn : n ≠ 1) : χ 0 = 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/DirichletCharacter/Basic.lean:366:noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Basic.lean:159:theorem mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Basic.lean:169:theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
.lake/packages/mathlib/Mathlib/RingTheory/Norm/Defs.lean:61:noncomputable def norm : S →* R :=
.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:169:lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:228:lemma unique (g : L ≃+* L) {c : ZMod n} (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Hom.lean:109:def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Hom.lean:320:def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Hom.lean:412:def symm {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:68:def symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:76:noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y}
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:114:abbrev symm {f g : X ⟶ Y} (h : P.RightHomotopy f g) : P.symm.RightHomotopy g f :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:140:noncomputable abbrev trans [IsFibrant Y] {f₀ f₁ f₂ : X ⟶ Y}
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:235:lemma symm [CategoryWithWeakEquivalences C]
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/RightHomotopy.lean:240:lemma trans [ModelCategory C]
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Clique.lean:98:theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := Set.Pairwise.mono' h
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Clique.lean:228:theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Clique.lean:397:theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n := by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Clique.lean:547:theorem CliqueFreeOn.mono (hmn : m ≤ n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n := by
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean:66:lemma IsBoundedAt.add {f' : ℍ → ℂ} (hf : IsBoundedAt c f k) (hf' : IsBoundedAt c f' k) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean:70:lemma IsZeroAt.add {f' : ℍ → ℂ} (hf : IsZeroAt c f k) (hf' : IsZeroAt c f' k) :
.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/Basic.lean:136:theorem trans (C : Type w) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
.lake/packages/mathlib/Mathlib/Algebra/Category/AlgCat/Basic.lean:115:lemma comp_apply {A B C : AlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/Basic.lean:154:protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean:75:def symm : PrepathObject A where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean:84:noncomputable def trans (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀] :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean:131:def symm : PathObject A where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean:251:noncomputable def trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] :
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:89:theorem IsPoly.add {f g : (α → ℕ) → ℤ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:152:theorem zero_apply (x) : (0 : Poly α) x = 0 := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:161:theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:164:theorem sub_apply (f g : Poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:167:theorem mul_apply (f g : Poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/IsValuedIn.lean:126:lemma IsValuedIn.trans (T : Type*) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Defs.lean:583:lemma IsOrthogonal.symm (h : IsOrthogonal P i j) : IsOrthogonal P j i := ⟨h.2, h.1⟩
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean:63:protected def norm [ℋ.HasDetPlusMinusOne] : SlashInvariantForm ℋ (k * Nat.card 𝒬) where
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/NormTrace.lean:107:protected def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:120:def pow (k : ℕ) : ArithmeticFunction ℕ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Base.lean:484:lemma IsPos.add {i j k : ι}
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Base.lean:491:lemma IsPos.sub {i j k : ι}
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Bipartite.lean:88:theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialNerve.lean:73:lemma Path.le {J : Type*} [LinearOrder J] {i j : J} (f : Path i j) : i ≤ j :=
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:76:theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:87:theorem zero_apply {x : ℕ} : (0 : ArithmeticFunction R) x = 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:175:instance add : Add (ArithmeticFunction R) where
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:179:theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:222:theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:234:theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:263:theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:503:theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:198:instance add : Add (ModularForm Γ k) where add f g :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:208:theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:223:theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:261:theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:284:theorem IsGLPos.smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:311:theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:336:def mul {k_1 k_2 : ℤ} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:417:theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:430:theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:454:theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:478:theorem IsGLPos.smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:505:theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.lean:162:def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.lean:273:def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:553:theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:559:theorem ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:565:theorem ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Hom.lean:258:theorem mul_apply (φ ψ : A →ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean:46:def smul : FamilyOfElements (M.presheaf ⋙ forget _) P := fun Y f hf =>
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean:219:noncomputable def smul : A.obj.obj X := (smulCandidate α φ r m).x
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean:226:protected lemma one_smul : smul α φ 1 m = m := by
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean:232:protected lemma zero_smul : smul α φ 0 m = 0 := by
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean:239:protected lemma smul_zero : smul α φ r 0 = 0 := by
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:34:lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:39:lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:88:lemma LSeriesHasSum.sub {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:93:lemma LSeriesSummable.sub {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:115:lemma LSeriesHasSum.smul {f : ℕ → ℂ} (c : ℂ) {s a : ℂ} (hf : LSeriesHasSum f s a) :
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Linearity.lean:119:lemma LSeriesSummable.smul {f : ℕ → ℂ} (c : ℂ) {s : ℂ} (hf : LSeriesSummable f s) :
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Equiv.lean:167:def symm (e : A ≃ₗc[R] B) : B ≃ₗc[R] A :=
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Equiv.lean:249:def trans (e₁₂ : A ≃ₗc[R] B) (e₂₃ : B ≃ₗc[R] C) : A ≃ₗc[R] C :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Coloring/VertexColoring.lean:268:theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean:296:def restrict {n : ℕ} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Subgraph.lean:112:protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Subgraph.lean:124:protected theorem Adj.ne {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ≠ v :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Subgraph.lean:1034:protected abbrev restrict {G' : G.Subgraph} : G.Subgraph → G'.coe.Subgraph :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:125:theorem add_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:153:theorem smul_apply (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:202:theorem sub_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:254:def mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : SlashInvariantForm Γ k₁)
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:136:def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:142:theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:251:theorem IsContained.trans : A ⊑ B → B ⊑ C → A ⊑ C := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:254:theorem IsContained.trans' : B ⊑ C → A ⊑ B → A ⊑ C := flip IsContained.trans
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:260:alias IsContained.trans_le := IsContained.mono_right
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:266:alias IsContained.trans_le' := IsContained.mono_left
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Locus.lean:46:lemma IsEtaleAt.comp
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:118:theorem comp [FormallyEtale R A] [FormallyEtale A B] :
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:239:theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:296:lemma FormallyEtale.comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyEtale)
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:116:def WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:132:def StrongFEPair.symm (P : StrongFEPair E) : StrongFEPair E where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean:828:theorem Parallel.symm {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) : s₂ ∥ s₁ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean:842:theorem Parallel.trans {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:148:lemma comp_apply {X Y T : GrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:369:lemma comp_apply {X Y T : CommGrpCat} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean:144:lemma comp_apply {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ O) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean:488:def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGrpCat).obj M) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:40:def AffineMap.restrict (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:51:theorem AffineMap.restrict.coe_apply (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:56:theorem AffineMap.restrict.linear_aux {φ : P₁ →ᵃ[k] P₂} {E : AffineSubspace k P₁}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:61:theorem AffineMap.restrict.linear (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:66:theorem AffineMap.restrict.injective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Injective φ)
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:73:theorem AffineMap.restrict.surjective (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Restrict.lean:81:theorem AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ →ᵃ[k] P₂}
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Pointwise/Bounds.lean:49:lemma BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Pointwise/Bounds.lean:53:lemma BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Pointwise/Bounds.lean:125:lemma IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Pointwise/Bounds.lean:131:lemma IsGLB.mul (hs : IsGLB s a) (ht : IsGLB t b) :
.lake/packages/mathlib/Mathlib/RingTheory/Morita/Basic.lean:85:def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
.lake/packages/mathlib/Mathlib/RingTheory/Morita/Basic.lean:101:def trans {A B C : Type u₁}
.lake/packages/mathlib/Mathlib/RingTheory/Morita/Basic.lean:134:lemma symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
.lake/packages/mathlib/Mathlib/RingTheory/Morita/Basic.lean:138:lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Basic.lean:51:lemma IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:109:protected theorem map_zero : D 0 = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:181:theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:199:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:226:theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:542:theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:370:def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:384:theorem comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:744:def pi (f : (i : ι) → (P1 →ᵃ[k] φp i)) : P1 →ᵃ[k] ((i : ι) → φp i) where
.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean:104:lemma IsOfFinOrder.pow {n : ℕ} : IsOfFinOrder a → IsOfFinOrder (a ^ n) := by
.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean:244:theorem IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x) :
.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean:884:theorem IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y) :=
.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean:1406:protected theorem IsOfFinOrder.pi [Finite ι] : (∀ i, IsOfFinOrder (x i)) → IsOfFinOrder x := by
.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:128:lemma isNilpotent.restrict
.lake/packages/mathlib/Mathlib/GroupTheory/SemidirectProduct.lean:120:def inr : G →* N ⋊[φ] G where
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Independent.lean:363:protected theorem AffineIndependent.mono {s t : Set P}
.lake/packages/mathlib/Mathlib/GroupTheory/EckmannHilton.lean:64:theorem mul : m₁ = m₂ := by
.lake/packages/mathlib/Mathlib/GroupTheory/EckmannHilton.lean:75:theorem mul_comm : Std.Commutative m₂ :=
.lake/packages/mathlib/Mathlib/GroupTheory/EckmannHilton.lean:82:theorem mul_assoc : Std.Associative m₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean:500:theorem Monic.mul {f g : MvPolynomial σ R} (hf : m.Monic f) (hg : m.Monic g) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean:560:protected theorem Monic.pow {f : MvPolynomial σ R} {n : ℕ} (hf : m.Monic f) :
.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Exp.lean:55:noncomputable def exp (a : A) : A :=
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/EpiMono.lean:121:theorem one_smul (x : X') : (1 : B) • x = x :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:244:theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:256:theorem mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:265:theorem pow {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (n : ℕ) :
.lake/packages/mathlib/Mathlib/GroupTheory/Finiteness.lean:137:theorem Submonoid.FG.pi (hP : ∀ i, (P i).FG) : (pi Set.univ P).FG := by
.lake/packages/mathlib/Mathlib/GroupTheory/Finiteness.lean:383:theorem Subgroup.FG.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean:68:theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean:73:theorem IsUniform.symm : Symmetric (IsUniform G ε) := fun s t h t' ht' s' hs' ht hs => by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Regularity/Uniform.lean:248:theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:230:theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:237:theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:260:lemma pow (hφ : φ.IsHomogeneous m) (n : ℕ) : (φ ^ n).IsHomogeneous (m * n) := by
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:308:theorem sub (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ - ψ) n :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean:238:lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G ≤ H) (hG : G.IsHamiltonian) :
.lake/packages/mathlib/Mathlib/Algebra/Category/CommBialgCat.lean:104:lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:137:theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:140:theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:143:theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:169:theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean:369:theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
.lake/packages/mathlib/Mathlib/GroupTheory/PushoutI.lean:70:protected instance mul : Mul (PushoutI φ) := by
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/IsBaseChangePi.lean:48:lemma pi {ι : Type*} [Finite ι]
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/IsBaseChangePi.lean:93:instance pi {ι : Type*} [Finite ι]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:47:theorem HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:54:theorem HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:60:theorem CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:80:theorem HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:85:theorem HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:90:theorem CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:94:theorem CPolynomialOn.add {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:98:theorem CPolynomialOn.sub {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/AbsoluteValue/Equivalence.lean:41:theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm
.lake/packages/mathlib/Mathlib/Analysis/AbsoluteValue/Equivalence.lean:43:theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:268:protected lemma smul (r : R) : IsAlgebraic R (r • a) :=
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:294:protected lemma mul : IsAlgebraic R (a * b) := by
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:301:protected lemma add : IsAlgebraic R (a + b) := by
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:308:protected lemma sub : IsAlgebraic R (a - b) :=
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:312:protected lemma pow (n : ℕ) : IsAlgebraic R (a ^ n) :=
.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:173:theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
.lake/packages/mathlib/Mathlib/RingTheory/Frobenius.lean:83:def restrict : S ⧸ Q →ₐ[R ⧸ Q.under R] S ⧸ Q where
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:140:def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:145:theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:217:protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:234:protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:723:theorem TensorProduct.Algebra.mul'_comp_tensorTensorTensorComm :
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:729:lemma LinearMap.mul'_tensor :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Basic.lean:173:theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Basic.lean:180:protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Basic.lean:183:protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
.lake/packages/mathlib/Mathlib/GroupTheory/Coprod/Basic.lean:184:def inr : N →* M ∗ N where
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomialDef.lean:152:theorem HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomialDef.lean:171:theorem CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Tutte.lean:60:lemma IsTutteViolator.mono {u : Set V} (h : G ≤ G') (ht : G'.IsTutteViolator u) :
.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean:288:theorem unique' {p q : Multiset (Associates α)} :
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Maps.lean:818:lemma mul'_bijective_of_surjective (h : Function.Surjective (algebraMap R A)) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:75:theorem HasFPowerSeriesWithinOnBall.add (hf : HasFPowerSeriesWithinOnBall f pf s x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:82:theorem HasFPowerSeriesOnBall.add (hf : HasFPowerSeriesOnBall f pf x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:88:theorem HasFPowerSeriesWithinAt.add
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:94:theorem HasFPowerSeriesAt.add (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:99:theorem AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:106:theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:112:theorem AnalyticOn.add (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:116:theorem AnalyticOnNhd.add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:164:theorem HasFPowerSeriesWithinOnBall.sub (hf : HasFPowerSeriesWithinOnBall f pf s x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:169:theorem HasFPowerSeriesOnBall.sub (hf : HasFPowerSeriesOnBall f pf x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:173:theorem HasFPowerSeriesWithinAt.sub
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:178:theorem HasFPowerSeriesAt.sub (hf : HasFPowerSeriesAt f pf x) (hg : HasFPowerSeriesAt g pg x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:182:theorem AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:187:theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:191:theorem AnalyticOn.sub (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:195:theorem AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:239:lemma AnalyticWithinAt.div_const {f : E → 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝} :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:244:lemma AnalyticAt.div_const {f : E → 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝} :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:248:lemma AnalyticOn.div_const {f : E → 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝} :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:252:lemma AnalyticOnNhd.div_const {f : E → 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝} :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:358:theorem AnalyticAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {x : E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:365:theorem AnalyticWithinAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:373:theorem AnalyticAt.comp₂_analyticWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:381:theorem AnalyticOnNhd.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)} {t : Set E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:387:theorem AnalyticOn.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:494:lemma HasFPowerSeriesWithinOnBall.pi
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:511:lemma HasFPowerSeriesOnBall.pi
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:523:lemma HasFPowerSeriesWithinAt.pi
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:538:lemma HasFPowerSeriesAt.pi
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:550:lemma AnalyticWithinAt.pi (hf : ∀ i, AnalyticWithinAt 𝕜 (f i) s e) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:560:lemma AnalyticAt.pi (hf : ∀ i, AnalyticAt 𝕜 (f i) e) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:570:lemma AnalyticOn.pi (hf : ∀ i, AnalyticOn 𝕜 (f i) s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:578:lemma AnalyticOnNhd.pi (hf : ∀ i, AnalyticOnNhd 𝕜 (f i) s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:605:lemma AnalyticWithinAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:613:lemma AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E → A}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:619:lemma AnalyticOn.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:626:lemma AnalyticOnNhd.smul [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:632:lemma AnalyticWithinAt.mul {f g : E → A} {s : Set E} {z : E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:639:lemma AnalyticAt.mul {f g : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:644:lemma AnalyticOn.mul {f g : E → A} {s : Set E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:650:lemma AnalyticOnNhd.mul {f g : E → A} {s : Set E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:657:lemma AnalyticWithinAt.pow {f : E → A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:670:lemma AnalyticAt.pow {f : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:677:lemma AnalyticOn.pow {f : E → A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:683:lemma AnalyticOnNhd.pow {f : E → A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean:241:theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Reduce.lean:363:def norm (x : FreeGroup α) : ℕ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:37:lemma mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:57:lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:79:lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Matching.lean:327:lemma IsMatchingFree.mono {G G' : SimpleGraph V} (h : G ≤ G') (hmf : G'.IsMatchingFree) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Matching.lean:547:lemma IsAlternating.mono {G'' : SimpleGraph V} (halt : G.IsAlternating G') (h : G'' ≤ G) :
.lake/packages/mathlib/Mathlib/Algebra/Order/AddTorsor.lean:86:theorem Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:236:theorem HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:294:theorem HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:299:theorem HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:353:lemma HasFPowerSeriesWithinOnBall.mono (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:364:lemma HasFPowerSeriesWithinAt.mono (hf : HasFPowerSeriesWithinAt f p s x) (h : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:454:lemma AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f s x) (h : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:498:theorem AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:527:lemma AnalyticOn.mono {f : E → F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:420:abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:530:abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:610:abbrev symm : G' ≃g G :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:709:abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:253:def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:263:theorem comp_apply
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:714:protected theorem map_zero (f : A →ₑ*[φ] B) : f 1 = 1 :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:780:def comp [κ : MonoidHom.CompTriple φ ψ χ]
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:786:theorem comp_apply (g : B →ₑ*[ψ] C) (f : A →ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:922:protected theorem map_zero (f : R →ₑ+*[φ] S) : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:974:def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R →ₑ+*[χ] T :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:979:theorem comp_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:225:protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:241:protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:375:protected theorem mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:391:protected theorem pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a := by
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:677:theorem padicValInt.mul [hp : Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean:85:protected lemma Connected.mono {H H' : G.Subgraph} (hle : H ≤ H') (hv : H.verts = H'.verts)
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean:92:protected lemma Connected.mono' {H H' : G.Subgraph}
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Basic.lean:96:theorem Red.trans : Red L₁ L₂ → Red L₂ L₃ → Red L₁ L₃ :=
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Basic.lean:764:theorem map.comp {γ : Type w} (f : α → β) (g : β → γ) (x) :
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Basic.lean:773:theorem map.unique (g : FreeGroup α →* FreeGroup β)
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Basic.lean:868:theorem prod.unique (g : FreeGroup α →* α) (hg : ∀ x, g (FreeGroup.of x) = x) {x} : g x = prod x :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:209:def norm (f : PadicSeq p) : ℚ :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:256:theorem norm_nonneg (f : PadicSeq p) : 0 ≤ f.norm := by
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:360:theorem norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm := by
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:490:theorem norm_neg (a : PadicSeq p) : (-a).norm = a.norm :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:833:protected theorem padicNormE.mul (q r : ℚ_[p]) : ‖q * r‖ = ‖q‖ * ‖r‖ := by simp [Norm.norm, map_mul]
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:1142:theorem AddValuation.map_zero : addValuationDef (0 : ℚ_[p]) = ⊤ := by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:90:protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:97:protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:133:protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:137:theorem Reachable.mono' {G G' : SimpleGraph V} (h : G ≤ G') : G.Reachable ≤ G'.Reachable :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:234:protected lemma Preconnected.mono {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:333:protected lemma Connected.mono {G G' : SimpleGraph V} (h : G ≤ G')
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/DomAct/Basic.lean:167:theorem smul_apply [SMul M α] (c : Mᵈᵐᵃ) (f : α → β) (a : α) : (c • f) a = f (mk.symm c • a) := rfl
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:231:protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:696:theorem HasFPowerSeriesWithinAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:818:theorem HasFPowerSeriesAt.comp {g : F → G} {f : E → F} {q : FormalMultilinearSeries 𝕜 F G}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:827:theorem AnalyticWithinAt.comp {g : F → G} {f : E → F} {x : E} {t : Set F} {s : Set E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:842:lemma AnalyticOn.comp {f : F → G} {g : E → F} {s : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:850:theorem AnalyticAt.comp {g : F → G} {f : E → F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:858:theorem AnalyticAt.comp' {g : F → G} {f : E → F} {x : E} (hg : AnalyticAt 𝕜 g (f x))
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:887:theorem AnalyticOnNhd.comp' {s : Set E} {g : F → G} {f : E → F} (hg : AnalyticOnNhd 𝕜 g (s.image f))
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:891:theorem AnalyticOnNhd.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:903:theorem HasFiniteFPowerSeriesAt.comp {m n : ℕ} {g : F → G} {f : E → F}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:936:theorem CPolynomialAt.comp {g : F → G} {f : E → F} {x : E}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:965:theorem CPolynomialOn.comp' {s : Set E} {g : F → G} {f : E → F} (hg : CPolynomialOn 𝕜 g (s.image f))
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:969:theorem CPolynomialOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F}
.lake/packages/mathlib/Mathlib/Probability/Process/LocalProperty.lean:120:lemma mono [Zero E] (hpq : ∀ X, p X → q X) (hpX : Locally p 𝓕 X P) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean:46:lemma IsEdgeReachable.symm (h : G.IsEdgeReachable k u v) : G.IsEdgeReachable k v u :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean:53:lemma IsEdgeReachable.trans (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean:57:lemma IsEdgeReachable.mono (hGH : G ≤ H) (h : G.IsEdgeReachable k u v) : H.IsEdgeReachable k u v :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:240:theorem AnalyticAt.rexp {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (exp ∘ f) x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:245:theorem AnalyticAt.rexp' {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun z ↦ exp (f z)) x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:248:theorem AnalyticWithinAt.rexp {x : E} (fa : AnalyticWithinAt ℝ f s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:253:theorem AnalyticOnNhd.rexp {s : Set E} (fs : AnalyticOnNhd ℝ f s) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:257:theorem AnalyticOn.rexp (fs : AnalyticOn ℝ f s) : AnalyticOn ℝ (fun z ↦ exp (f z)) s :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:300:theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:304:theorem HasDerivAt.exp (hf : HasDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:308:theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:333:theorem ContDiff.exp {n} (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.exp (f x) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:337:theorem ContDiffAt.exp {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.exp (f x)) x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:341:theorem ContDiffOn.exp {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.exp (f x)) s :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:345:theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt ℝ n f s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:349:theorem HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:353:theorem HasFDerivAt.exp (hf : HasFDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:357:theorem HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:361:theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt ℝ f s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:366:theorem DifferentiableAt.exp (hc : DifferentiableAt ℝ f x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:371:theorem DifferentiableOn.exp (hc : DifferentiableOn ℝ f s) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:375:theorem Differentiable.exp (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.exp (f x) :=
.lake/packages/mathlib/Mathlib/Probability/Process/Stopping.lean:421:theorem add [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNorm.lean:134:protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNorm.lean:194:protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
.lake/packages/mathlib/Mathlib/Probability/Process/Filtration.lean:67:protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
.lake/packages/mathlib/Mathlib/Probability/Process/Filtration.lean:70:protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Dart.lean:73:def Dart.symm (d : G.Dart) : G.Dart :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:167:def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:175:theorem comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:224:theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:64:protected theorem mul [∀ i, Mul (β i)] [∀ i, MeasurableMul₂ (β i)]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:77:protected theorem smul {𝕂 : Type*} [MeasurableSpace 𝕂]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:109:protected theorem mul [∀ i, Mul (β i)] [∀ i, ContinuousMul (β i)]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:122:protected theorem smul [∀ i, SMul ℝ (β i)] [∀ i, ContinuousConstSMul ℝ (β i)]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:127:protected lemma norm {β : ι → Type*} {u : (i : ι) → Ω → β i} [∀ i, SeminormedAddCommGroup (β i)]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:207:protected theorem comp {t : ι → Ω → ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:220:protected theorem mul [Mul β] [ContinuousMul β] (hu : IsStronglyProgressive f u)
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:259:protected lemma norm {β : Type*} {u : ι → Ω → β} [SeminormedAddCommGroup β]
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:311:alias ProgMeasurable.mul := IsStronglyProgressive.mul
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:243:protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:251:theorem comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:378:protected def symm (e : α ≃+*o β) : β ≃+*o α :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:403:protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Walk/Subwalks.lean:65:lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Blocks.lean:146:theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:363:def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:371:theorem comp_apply (f : β →*o γ) (g : α →*o β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:448:theorem mul_apply [IsOrderedMonoid β] (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:576:def trans (f : α ≃*o β) (g : β ≃*o γ) : α ≃*o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:630:def symm (f : α ≃*o β) : β ≃*o α :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupExtension/Defs.lean:199:def symm : S'.Equiv S where
.lake/packages/mathlib/Mathlib/GroupTheory/GroupExtension/Defs.lean:222:def trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'') :
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/RingHom.lean:151:protected theorem map_zero (f : 𝒜 →+*ᵍ ℬ) : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/RingHom.lean:202:def comp (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) : 𝒜 →+*ᵍ 𝒞 where
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/RingHom.lean:215:theorem comp_apply (hnp : ℬ →+*ᵍ 𝒞) (hmn : 𝒜 →+*ᵍ ℬ) (x : A) :
.lake/packages/mathlib/Mathlib/RingTheory/Multiplicity.lean:652:theorem FiniteMultiplicity.pow {p a : α} (hp : Prime p)
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Embedding.lean:32:instance smul [Group G] [MulAction G β] : SMul G (α ↪ β) :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Embedding.lean:41:theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupExtension/Basic.lean:192:theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
.lake/packages/mathlib/Mathlib/GroupTheory/GroupExtension/Basic.lean:198:theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/VertexCover.lean:55:theorem IsVertexCover.mono {c : Set V} (hG : G ≤ G') (hc : IsVertexCover G' c) :
.lake/packages/mathlib/Mathlib/GroupTheory/Commensurable.lean:68:theorem symm {H K : Subgroup G} : Commensurable H K → Commensurable K H := And.symm
.lake/packages/mathlib/Mathlib/GroupTheory/Commensurable.lean:71:theorem trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Invariance.lean:50:theorem Invariant.comp (hκ : Invariant κ μ) (hη : Invariant η μ) :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Finsubgraph.lean:141:def FinsubgraphHom.restrict {G' G'' : G.Finsubgraph} (h : G'' ≤ G') (f : G' →fg F) : G'' →fg F := by
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean:402:theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Defs.lean:201:instance IsFiniteKernel.add (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Defs.lean:384:instance IsSFiniteKernel.add (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
.lake/packages/mathlib/Mathlib/Combinatorics/Hindman.lean:54:def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V
.lake/packages/mathlib/Mathlib/Combinatorics/Hindman.lean:126:theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:40:def exp (x : EReal) : ℝ≥0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:109:lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Restrict.lean:122:def restrict (M : Matroid α) (R : Set α) : Matroid α := (M.restrictIndepMatroid R).matroid
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Restrict.lean:280:theorem IsRestriction.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤r M₂) (h' : M₂ ≤r M₃) : M₁ ≤r M₃ :=
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Restrict.lean:306:theorem IsStrictRestriction.ne (h : N <r M) : N ≠ M := by
.lake/packages/mathlib/Mathlib/RingTheory/ZariskisMainTheorem.lean:109:lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Order.lean:78:lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Order.lean:101:lemma IsMinor.le (h : N ≤m M) : N ≤ M := h
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Order.lean:114:lemma IsStrictMinor.ne (h : N <m M) : N ≠ M :=
.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Minor/Order.lean:138:lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
.lake/packages/mathlib/Mathlib/GroupTheory/MonoidLocalization/MonoidWithZero.lean:45:protected theorem LocalizationMap.map_zero (f : LocalizationMap S N) : f 0 = 0 := by
.lake/packages/mathlib/Mathlib/GroupTheory/MonoidLocalization/MonoidWithZero.lean:49:protected theorem IsLocalizationMap.map_zero {F} [FunLike F M N] [MulHomClass F M N] {f : F}
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/MeasureComp.lean:176:lemma AbsolutelyContinuous.comp (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
.lake/packages/mathlib/Mathlib/GroupTheory/MonoidLocalization/Order.lean:30:instance le : LE (Localization s) :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Support.lean:47:theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun _ hg =>
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Support.lean:57:theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:280:alias mul_left_cancel'' := mul_left_cancel
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1140:theorem Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone fun x ↦ a * f x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1144:theorem MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1148:theorem Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ a * f x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1152:theorem AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1156:theorem Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1160:theorem MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1164:theorem Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ f x * a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1168:theorem AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1173:theorem Monotone.mul' [MulLeftMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1179:theorem MonotoneOn.mul' [MulLeftMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1186:theorem Antitone.mul' [MulLeftMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1192:theorem AntitoneOn.mul' [MulLeftMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1202:theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1206:theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1211:theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1215:theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1226:theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1230:theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1235:theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1239:theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1247:theorem StrictMono.mul' [MulLeftStrictMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1254:theorem StrictMonoOn.mul' [MulLeftStrictMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1261:theorem StrictAnti.mul' [MulLeftStrictMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:1268:theorem StrictAntiOn.mul' [MulLeftStrictMono α]
.lake/packages/mathlib/Mathlib/GroupTheory/FreeAbelianGroup.lean:232:protected theorem map_zero (f : α → β) : f <$> (0 : FreeAbelianGroup α) = 0 :=
.lake/packages/mathlib/Mathlib/GroupTheory/FreeAbelianGroup.lean:391:instance mul : Mul (FreeAbelianGroup α) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean:97:instance add : Add (WithTop α) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean:455:instance add : Add (WithBot α) :=
.lake/packages/mathlib/Mathlib/GroupTheory/IsSubnormal.lean:216:lemma trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) :
.lake/packages/mathlib/Mathlib/GroupTheory/IsSubnormal.lean:234:lemma trans (HK : H ≤ K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
.lake/packages/mathlib/Mathlib/GroupTheory/IsSubnormal.lean:288:protected lemma smul {Γ : Type*} [Group Γ] [MulDistribMulAction Γ G] (hS : H.IsSubnormal)
.lake/packages/mathlib/Mathlib/RingTheory/IdealFilter/Basic.lean:135:lemma IsTorsionQuot.mono {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strict.lean:217:theorem StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strict.lean:249:theorem StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s) := by
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strict.lean:342:theorem StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s - t) :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:141:theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:168:theorem smul_apply [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E)
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:182:theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:277:def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:287:theorem comp_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) x = p (f x) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Lex.lean:74:def inr : β →*o α × β where
.lake/packages/mathlib/Mathlib/CategoryTheory/FintypeCat.lean:73:theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Over.lean:154:instance LiesOver.smul [h : P.LiesOver p] : (g • P).LiesOver p :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Over.lean:179:theorem LiesOver.trans [𝔓.LiesOver P] [P.LiesOver p] : 𝔓.LiesOver p where
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/MapComap.lean:86:lemma map_zero : Kernel.map (0 : Kernel α β) f = 0 := by
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pointwise.lean:144:instance IsPrime.smul {I : Ideal R} [H : I.IsPrime] (g : M) : (g • I).IsPrime := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:236:noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:412:lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:434:lemma rpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:447:lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:459:lemma rpow_add {a : A} {x y : ℝ} (ha : IsUnit a) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:637:lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:648:lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Resolution.lean:107:def Hom.comp {R R' R'' : Φ.RightResolution X₂}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Resolution.lean:151:def Hom.comp {L L' L'' : Φ.LeftResolution X₂}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/SmallShiftedHom.lean:150:noncomputable def comp {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean:146:lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:219:private abbrev smul' (r₁ : R) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:223:private theorem smul'_char (r₁ : R) (r₂ : X) (s₁ s₂ : S) (u : S) (v : R) (huv : u * r₁ = v * s₂) :
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:248:private abbrev smul'' (r : R) (s : S) : X[S⁻¹] → X[S⁻¹] :=
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:273:protected abbrev smul (y : R[S⁻¹]) (x : X[S⁻¹]) : X[S⁻¹] :=
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:370:protected theorem one_smul (x : X[S⁻¹]) : (1 : R[S⁻¹]) • x = x := by
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:379:protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:399:protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Nonneg/Basic.lean:63:instance add [AddZeroClass α] [Preorder α] [AddLeftMono α] : Add { x : α // 0 ≤ x } :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Nonneg/Basic.lean:123:instance mul : Mul { x : α // 0 ≤ x } where
.lake/packages/mathlib/Mathlib/Algebra/Order/Nonneg/Basic.lean:205:instance pow : Pow { x : α // 0 ≤ x } ℕ where
.lake/packages/mathlib/Mathlib/Algebra/Order/Nonneg/Basic.lean:279:instance sub [Sub α] : Sub { x : α // 0 ≤ x } :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/SmallHom.lean:155:noncomputable def comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:50:noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:57:theorem comp_apply (η : Kernel β γ) (κ : Kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:60:theorem comp_apply' (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:177:lemma comp_add_right (μ κ : Kernel α β) (η : Kernel β γ) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:200:instance IsMarkovKernel.comp (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:208:instance IsZeroOrMarkovKernel.comp (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:213:instance IsFiniteKernel.comp (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:220:instance IsSFiniteKernel.comp (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/SubMulAction.lean:378:instance smul' : SMul S p where smul c x := ⟨c • x.1, smul_of_tower_mem _ c x.2⟩
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:145:theorem add {f' q' r'} (H : f.IsWeierstrassDivisionAt g q r I)
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:151:theorem smul (H : f.IsWeierstrassDivisionAt g q r I) (a : A) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:593:theorem IsWeierstrassDivision.unique [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:699:theorem mul {g' : A⟦X⟧} {f' : A[X]} {h' : A⟦X⟧} (H' : g'.IsWeierstrassFactorizationAt f' h' I) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:704:theorem smul {a : A} (ha : IsUnit a) : (a • g).IsWeierstrassFactorizationAt f (a • h) I := by
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean:851:theorem IsWeierstrassFactorization.unique
.lake/packages/mathlib/Mathlib/Algebra/LieRinehartAlgebra/Defs.lean:118:protected def comp (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (g : L₂ →ₗ⁅σ₂₃⁆ L₃) : L₁ →ₗ⁅σ₂₃.comp σ₁₂⁆ L₃ where
.lake/packages/mathlib/Mathlib/Probability/Kernel/Basic.lean:191:lemma const_add (β : Type*) [MeasurableSpace β] (μ ν : Measure α) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Basic.lean:247:protected noncomputable def restrict (κ : Kernel α β) (hs : MeasurableSet s) : Kernel α β where
.lake/packages/mathlib/Mathlib/Probability/Kernel/Basic.lean:284:instance IsFiniteKernel.restrict (κ : Kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Basic.lean:290:instance IsSFiniteKernel.restrict (κ : Kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/GoingDown.lean:125:lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:309:protected theorem mul_assoc : I * J * K = I * (J * K) :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:384:protected theorem mul_one : I * 1 = I :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:566:protected theorem mul_comm : I * J = J * I :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:663:theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Basic.lean:50:def pi : Ideal (Π i, R i) where
.lake/packages/mathlib/Mathlib/Analysis/Convex/Side.lean:447:theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Side.lean:479:theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Side.lean:499:theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Side.lean:526:theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Restricted.lean:65:lemma add {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Restricted.lean:80:lemma smul {f : PowerSeries R} (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Restricted.lean:118:lemma mul {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/LocalizerMorphism.lean:71:def comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/LocalizerMorphism.lean:229:instance IsLocalizedEquivalence.comp [Φ.IsLocalizedEquivalence]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:97:theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean:111:theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp A).IsSymm :=
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Substitution.lean:106:theorem HasSubst.add (hf : HasSubst f) (hg : HasSubst g) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Substitution.lean:121:theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Substitution.lean:133:theorem HasSubst.smul' (a : A) (hf : HasSubst f) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Substitution.lean:358:theorem HasSubst.comp
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Evaluation.lean:72:theorem HasEval.mono {S : Type*} [CommRing S] {a : S}
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Evaluation.lean:81:theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Prefunctor.lean:75:def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
.lake/packages/mathlib/Mathlib/GroupTheory/SpecificGroups/Quaternion.lean:64:private def mul : QuaternionGroup n → QuaternionGroup n → QuaternionGroup n
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Fractions.lean:116:abbrev symm : W.LeftFraction₂ X Y where
.lake/packages/mathlib/Mathlib/Analysis/Normed/MulAction.lean:34:theorem norm_smul_le (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ := by
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Exp.lean:48:def exp : PowerSeries A :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:131:theorem HasTemperateGrowth.comp' [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:172:theorem HasTemperateGrowth.comp [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:192:theorem HasTemperateGrowth.add (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:206:theorem HasTemperateGrowth.sub (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:268:theorem HasTemperateGrowth.smul {f : E → 𝕜} {g : E → F} (hf : f.HasTemperateGrowth)
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:276:theorem HasTemperateGrowth.mul {f g : E → R} (hf : f.HasTemperateGrowth)
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:281:theorem HasTemperateGrowth.pow {f : E → R} (hf : f.HasTemperateGrowth) (k : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:146:theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:60:abbrev add : W.LeftFraction X Y where
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:122:noncomputable def add' (f₁ f₂ : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:125:lemma add'_eq (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:144:lemma add'_comm (f₁ f₂ : L.obj X ⟶ L.obj Y) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:149:lemma add'_zero (f : L.obj X ⟶ L.obj Y) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:159:lemma zero_add' (f : L.obj X ⟶ L.obj Y) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:171:lemma add'_assoc (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:181:lemma add'_comp (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:215:lemma add'_map (f₁ f₂ : X ⟶ Y) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean:255:noncomputable def add (f₁ f₂ : X' ⟶ Y') : X' ⟶ Y' :=
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Path.lean:88:def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:116:protected theorem differentiable (f : 𝓢(E, F)) : Differentiable ℝ f :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:246:theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:295:theorem zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:328:theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:353:theorem sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/GroupTheory/SpecificGroups/Dihedral.lean:45:private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:178:protected theorem map_zero : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:332:def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:649:def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:715:def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:853:theorem map_zero : e 0 = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:125:theorem smul {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:137:theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:146:theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:149:theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:199:lemma symm (h : IsBoundedBilinearMap 𝕜 f) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:468:theorem Continuous.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:473:theorem ContinuousOn.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:479:theorem ContinuousAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E} {x : X}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:484:theorem ContinuousWithinAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:884:protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Pi.lean:31:instance pi {J : Type w} [Finite J] {C : J → Type u₁} {D : J → Type u₂}
.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Operations.lean:100:protected theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Inverse.lean:167:protected theorem mul_inv_cancel (φ : k⟦X⟧) (h : constantCoeff φ ≠ 0) : φ * φ⁻¹ = 1 :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:37:theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:44:theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Composition.lean:39:def StrictUniversalPropertyFixedTarget.comp
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Composition.lean:62:lemma comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
.lake/packages/mathlib/Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean:78:lemma IsRatCondKernelCDF.mono (hf : IsRatCondKernelCDF f κ ν) (a : α) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean:249:lemma IsRatCondKernelCDFAux.mono (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:649:protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean:157:theorem MemSobolev.add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean:165:theorem MemSobolev.sub {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean:180:theorem MemSobolev.smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean:298:theorem MemSobolev.mono {s s' : ℝ} (h : s' ≤ s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean:373:protected def LinearIsometry.inr [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:137:theorem ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:145:theorem ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:161:theorem StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:169:theorem StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:193:theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:201:theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:492:theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:508:theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:827:theorem ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (f - g) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:830:theorem ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s (f - g) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:833:theorem StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:837:theorem StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:907:theorem ConvexOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s fun x => c • f x :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean:914:theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) :
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Support.lean:60:theorem IsVanishingOn.mono ⦃s₁ s₂ : Set α⦄ (hs : s₂ ⊆ s₁) (hf : IsVanishingOn f s₁) :
.lake/packages/mathlib/Mathlib/Probability/Kernel/IonescuTulcea/Maps.lean:61:lemma restrict₂_comp_IicProdIoc (a b : ι) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Conformal.lean:61:theorem IsConformalMap.smul (hf : IsConformalMap f) {c : R} (hc : c ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Conformal.lean:79:theorem comp (hg : IsConformalMap g) (hf : IsConformalMap f) : IsConformalMap (g.comp f) := by
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/ReflQuiver.lean:101:def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:146:protected theorem symm {x y} : c x y → c y x := c.toSetoid.symm'
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:150:protected theorem trans {x y z} : c x y → c y z → c x z := c.toSetoid.trans'
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:154:protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) := c.mul'
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:557:protected theorem pow {M : Type*} [Monoid M] (c : Con M) :
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Basic.lean:66:theorem SameCycle.symm : SameCycle f x y → SameCycle f y x := fun ⟨i, hi⟩ =>
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Basic.lean:73:theorem SameCycle.trans : SameCycle f x y → SameCycle f y z → SameCycle f x z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exponential.lean:411:lemma HasSum.exp {ι : Type*} {f : ι → 𝔸} {a : 𝔸} (h : HasSum f a) :
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Covering.lean:112:theorem Prefunctor.IsCovering.comp (hφ : φ.IsCovering) (hψ : ψ.IsCovering) : (φ ⋙q ψ).IsCovering :=
.lake/packages/mathlib/Mathlib/Probability/Kernel/Integral.lean:41:lemma integral_congr_ae₂ {f g : α → β → E} {μ : Measure α} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Basic.lean:62:def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Basic.lean:283:theorem smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean:408:theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean:567:theorem comp [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B] : Smooth R B where
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:129:lemma zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0 := rfl
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:140:lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:176:lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:255:lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:494:theorem IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:626:theorem IsSt.add {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:636:theorem IsSt.sub {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:641:theorem IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x ≤ y) : r ≤ s :=
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:884:theorem IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
.lake/packages/mathlib/Mathlib/Analysis/Real/Hyperreal.lean:1175:theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:241:lemma symm {X Y : C} {z₁ z₂ : W.LeftFraction X Y} (h : LeftFractionRel z₁ z₂) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:246:lemma trans {X Y : C} {z₁ z₂ z₃ : W.LeftFraction X Y}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:285:def comp₀ [W.HasLeftCalculusOfFractions] {X Y Z : C}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:292:lemma comp₀_rel [W.HasLeftCalculusOfFractions]
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:329:noncomputable def comp
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:344:noncomputable def Hom.comp {X Y Z : C} (z₁ : Hom W X Y) (z₂ : Hom W Y Z) : Hom W X Z := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:923:lemma symm {X Y : C} {z₁ z₂ : W.RightFraction X Y} (h : RightFractionRel z₁ z₂) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:927:lemma trans {X Y : C} {z₁ z₂ z₃ : W.RightFraction X Y}
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:68:lemma IsSubgraph.trans (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁) : H.IsSubgraph G₁ :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:86:lemma IsLink.mono (hHG : H ≤ G) (h : H.IsLink e x y) : G.IsLink e x y := hHG.2 h
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:129:lemma Inc.mono (hHG : H ≤ G) (h : H.Inc e x) : G.Inc e x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:140:lemma IsLoopAt.mono (hHG : H ≤ G) (h : H.IsLoopAt e x) : G.IsLoopAt e x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:153:lemma IsNonloopAt.mono (hHG : H ≤ G) (h : H.IsNonloopAt e x) : G.IsNonloopAt e x := by
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:167:lemma Adj.mono (hHG : H ≤ G) (h : H.Adj x y) : G.Adj x y :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:210:protected lemma trans (h₁ : G ≤s G₁) (h₂ : G₁ ≤s G₂) : G ≤s G₂ :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:254:protected lemma trans (h₁ : G ≤i G₁) (h₂ : G₁ ≤i G₂) : G ≤i G₂ :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Subgraph.lean:316:protected lemma trans (h₁ : G ≤c G₁) (h₂ : G₁ ≤c G₂) : G ≤c G₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:201:theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:206:theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:239:theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
.lake/packages/mathlib/Mathlib/Analysis/Convex/Visible.lean:57:lemma IsVisible.mono (hst : s ⊆ t) (ht : IsVisible 𝕜 t x y) : IsVisible 𝕜 s x y :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Delete.lean:38:def restrict (G : Graph α β) (E₀ : Set β) : Graph α β where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:41:def mul : R →L[𝕜] R →L[𝕜] R :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:45:theorem mul_apply' (x y : R) : mul 𝕜 R x y = x * y :=
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Support.lean:52:theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Support.lean:522:theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support)
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:82:def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:270:def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Basic.lean:129:protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Basic.lean:316:protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Basic.lean:443:lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
.lake/packages/mathlib/Mathlib/CategoryTheory/DifferentialObject.lean:72:def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Basic.lean:49:theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Basic.lean:157:theorem IsCoprime.mono (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w) : IsCoprime x z :=
.lake/packages/mathlib/Mathlib/GroupTheory/PresentedGroup.lean:129:theorem toGroup.unique (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/StandardSmooth.lean:138:lemma IsStandardSmooth.trans [IsStandardSmooth R S] [IsStandardSmooth S T] :
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/StandardSmooth.lean:145:lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension n R S]
.lake/packages/mathlib/Mathlib/Analysis/Convex/Exposed.lean:95:protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C := by
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Lemmas.lean:203:theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
.lake/packages/mathlib/Mathlib/RingTheory/Coprime/Lemmas.lean:291:theorem pow (H : IsRelPrime x y) : IsRelPrime (x ^ m) (y ^ n) :=
.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Fin.lean:449:theorem cycleIcc.trans [NeZero n] (hij : i ≤ j) (hjk : j ≤ k) :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/IsGaussianProcess/Basic.lean:161:lemma smul (c : T → ℝ) (hX : IsGaussianProcess X P) :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/IsGaussianProcess/Basic.lean:174:lemma restrict (h : IsGaussianProcess X P) (s : Set T) :
.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean:318:theorem fourierCoeff.add {f g : AddCircle T → E} (hf : Integrable f haarAddCircle)
.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean:341:theorem fourierCoeff.const_mul (f : AddCircle T → ℂ) (c : ℂ) (n : ℤ) :
.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean:371:theorem fourierCoeffOn.const_mul {a b : ℝ} (f : ℝ → ℂ) (c : ℂ) (n : ℤ) (hab : a < b) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:190:theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:409:theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:464:theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean:159:lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean:189:lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P :=
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean:196:lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P :=
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean:216:lemma prodMk [Finite ι] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:65:theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:156:theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:38:lemma ConvexOn.smul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:57:lemma ConcaveOn.smul' [IsOrderedModule 𝕜 E] (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:77:lemma ConvexOn.smul'' [IsOrderedModule 𝕜 E] (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:84:lemma ConcaveOn.smul'' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:116:lemma ConvexOn.mul (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:120:lemma ConcaveOn.mul (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:124:lemma ConvexOn.mul' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:128:lemma ConcaveOn.mul' (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Mul.lean:148:lemma ConvexOn.pow (hf : ConvexOn 𝕜 s f) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:212:theorem IsCompactOperator.smul {S : Type*} [Monoid S] [DistribMulAction S M₂]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:240:theorem IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ → M₂} (hf : IsCompactOperator f)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:252:theorem IsCompactOperator.sub [IsTopologicalAddGroup M₄] {f g : M₁ → M₄} (hf : IsCompactOperator f)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:334:theorem IsCompactOperator.restrict {f : M₁ →ₗ[R₁] M₁} (hf : IsCompactOperator f)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:347:theorem IsCompactOperator.restrict' [T0Space M₂] {f : M₂ →ₗ[R₂] M₂}
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:228:theorem IsThetaTVS.symm (h : f =Θ[𝕜; l] g) : g =Θ[𝕜; l] f := And.symm h
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:241:theorem IsBigOTVS.trans (hfg : f =O[𝕜; l] g) (hgk : g =O[𝕜; l] k) : f =O[𝕜; l] k := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:269:theorem IsThetaTVS.trans (hfg : f =Θ[𝕜; l] g) (hgk : g =Θ[𝕜; l] k) : f =Θ[𝕜; l] k :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:317:theorem IsLittleOTVS.trans (hfg : f =o[𝕜; l] g) (hgk : g =o[𝕜; l] k) : f =o[𝕜; l] k :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:400:lemma IsLittleOTVS.mono (hf : f =o[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =o[𝕜; l₂] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:403:lemma IsBigOTVS.mono (hf : f =O[𝕜; l₁] g) (h : l₂ ≤ l₁) : f =O[𝕜; l₂] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:466:theorem IsLittleOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:490:theorem IsBigOTVS.prodMk [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] {k : α → G}
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:514:theorem IsLittleOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:521:theorem IsBigOTVS.add [ContinuousAdd E] [ContinuousSMul 𝕜 E]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:564:protected theorem IsLittleOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =o[𝕜; l] g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:577:protected theorem IsBigOTVS.symm {f₁ f₂ : α → E} (h : (f₁ - f₂) =O[𝕜; l] g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:619:protected theorem IsLittleOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/TVS.lean:642:protected theorem IsBigOTVS.pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]
.lake/packages/mathlib/Mathlib/Probability/Martingale/Basic.lean:110:theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
.lake/packages/mathlib/Mathlib/Probability/Martingale/Basic.lean:118:theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
.lake/packages/mathlib/Mathlib/Probability/Martingale/Basic.lean:121:theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
.lake/packages/mathlib/Mathlib/Probability/Martingale/Basic.lean:174:theorem add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
.lake/packages/mathlib/Mathlib/Probability/Martingale/Basic.lean:217:theorem add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/SuperpolynomialDecay.lean:80:theorem SuperpolynomialDecay.add [ContinuousAdd β] (hf : SuperpolynomialDecay l k f)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/SuperpolynomialDecay.lean:84:theorem SuperpolynomialDecay.mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/SuperpolynomialDecay.lean:88:theorem SuperpolynomialDecay.mul_const [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/SuperpolynomialDecay.lean:92:theorem SuperpolynomialDecay.const_mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:67:lemma le_rfl : a ≤ a := le_refl a
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:92:lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:197:theorem zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0 := rfl
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:304:theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:307:theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:462:theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:465:theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:468:theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:471:theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:481:theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:526:theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:573:theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:577:theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:580:theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:982:theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:990:theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:995:theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1036:theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1044:theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1047:theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1085:theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1093:theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1099:theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1307:theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1316:theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1336:theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1340:theorem IsBigOWith.pow' [NormOneClass S] {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1349:theorem IsBigOWith.pow [NormOneClass R] [NormOneClass S]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1366:theorem IsBigO.pow [NormOneClass S] {f : α → R} {g : α → S} (h : f =O[l] g) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1371:theorem IsLittleO.pow {f : α → R} {g : α → S} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/FiniteExtension.lean:59:def norm (x : L) : ℝ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/FiniteExtension.lean:71:protected theorem norm_neg (x : L) : B.norm (-x) = B.norm x := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/FiniteExtension.lean:75:protected theorem norm_nonneg (x : L) : 0 ≤ B.norm x := by
.lake/packages/mathlib/Mathlib/Order/Defs/Unbundled.lean:121:lemma trans [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
.lake/packages/mathlib/Mathlib/Order/Defs/Unbundled.lean:122:lemma symm [Std.Symm r] : a ≺ b → b ≺ a := Std.Symm.symm _ _
.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean:69:theorem IsChain.mono : s ⊆ t → IsChain r t → IsChain r s :=
.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean:77:theorem IsChain.symm (h : IsChain r s) : IsChain (flip r) s :=
.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean:233:lemma IsChain.lt_of_not_ge [Preorder α] (hs : IsChain (· ≤ ·) s)
.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean:270:theorem IsMaxChain.symm (h : IsMaxChain r s) : IsMaxChain (flip r) s :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Independent.lean:101:protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t → E))
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:62:lemma UniformConvexOn.mono (hψφ : ψ ≤ φ) (hf : UniformConvexOn s φ f) : UniformConvexOn s ψ f :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:65:lemma UniformConcaveOn.mono (hψφ : ψ ≤ φ) (hf : UniformConcaveOn s φ f) : UniformConcaveOn s ψ f :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:88:lemma UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:94:lemma UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:108:lemma UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strong.lean:111:lemma UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:94:theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:98:theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:225:theorem IsEquivalent.smul {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:264:protected theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:296:protected theorem IsEquivalent.pow (h : t ~[l] u) (n : ℕ) : t ^ n ~[l] u ^ n := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean:476:theorem IsEquivalent.mono {f g : α → β} {l' : Filter α} (h : f ~[l'] g) (hl : l ≤ l') :
.lake/packages/mathlib/Mathlib/Order/Sublattice.lean:369:def pi (s : Set κ) (L : ∀ i, Sublattice (π i)) : Sublattice (∀ i, π i) where
.lake/packages/mathlib/Mathlib/Probability/IdentDistribIndep.lean:39:lemma IdentDistrib.prodMk [IsFiniteMeasure μ]
.lake/packages/mathlib/Mathlib/Probability/IdentDistribIndep.lean:57:lemma IdentDistrib.pi [Countable ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
.lake/packages/mathlib/Mathlib/Analysis/Convex/Extreme.lean:85:protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Extreme.lean:107:protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:369:protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:375:protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:398:protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:404:protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:429:lemma MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:436:lemma AntitoneOn.comp (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:443:lemma StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:450:lemma StrictAntiOn.comp (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean:513:theorem Monotone.prodMk {f : γ → α} {g : γ → β} (hf : Monotone f) (hg : Monotone g) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean:277:theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean:285:theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean:305:theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Theta.lean:58:theorem IsTheta.trans {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Theta.lean:153:theorem IsTheta.mono (h : f =Θ[l] g) (hl : l' ≤ l) : f =Θ[l'] g :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Theta.lean:179:theorem IsTheta.smul [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'} {g₁ : α → E'}
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Theta.lean:184:theorem IsTheta.mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Theta.lean:215:theorem IsTheta.pow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:126:protected noncomputable def pi : ℝ :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:195:noncomputable def pi : ℝ≥0 :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:217:theorem StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:257:theorem StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) :
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:273:theorem StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c • s) :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:276:theorem StarConvex.zero_smul (hs : StarConvex 𝕜 0 s) (c : 𝕜) : StarConvex 𝕜 0 (c • s) := by
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:356:theorem StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:123:protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:128:theorem mono' (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), r' a b → r a b) :
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:211:theorem IsWF.mono (h : IsWF t) (st : s ⊆ t) : IsWF s := h.subset st
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:270:theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:388:protected theorem PartiallyWellOrderedOn.pi {α : ι → Type*} [Finite ι] {r : ∀ i, α i → α i → Prop}
.lake/packages/mathlib/Mathlib/Order/WellFoundedSet.lean:453:theorem IsPWO.pi {α : ι → Type*} [Finite ι] [∀ i, Preorder (α i)] {s : ∀ i, Set (α i)}
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:91:theorem CompRel.symm : CompRel r a b → CompRel r b a :=
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:135:alias LE.le.compRel := CompRel.of_le
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:136:alias LE.le.compRel_symm := CompRel.of_ge
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:262:theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:303:theorem IncompRel.ne [Std.Refl r] {a b : α} (h : IncompRel r a b) : a ≠ b := by
.lake/packages/mathlib/Mathlib/Order/Comparable.lean:315:theorem LE.le.not_incompRel (h : a ≤ b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_le h
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:89:protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:94:protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν)
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:109:protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:237:protected theorem norm [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:246:protected theorem pow [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) {n : ℕ} :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:259:theorem mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:264:theorem const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:269:theorem div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
.lake/packages/mathlib/Mathlib/Order/Monotone/Monovary.lean:336:protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun _ _ hf =>
.lake/packages/mathlib/Mathlib/Order/Monotone/Monovary.lean:340:protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun _ _ hf =>
.lake/packages/mathlib/Mathlib/Order/Monotone/Monovary.lean:344:protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun _ hi _ hj hf =>
.lake/packages/mathlib/Mathlib/Order/Monotone/Monovary.lean:348:protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun _ hi _ hj hf =>
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean:48:def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Basic.lean:576:def comp : F ⋙ H ⊣ I ⋙ G :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:79:theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:84:theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:88:theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:109:theorem HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:113:theorem HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:117:theorem HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:122:theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:127:theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:132:theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:136:theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:150:theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:155:theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:160:theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:164:theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => √(f y) :=
.lake/packages/mathlib/Mathlib/Tactic/Algebra/Basic.lean:167:def add (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
.lake/packages/mathlib/Mathlib/Tactic/Algebra/Basic.lean:180:def mul (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
.lake/packages/mathlib/Mathlib/Tactic/Algebra/Basic.lean:215:def pow (cR : Common.Cache sR) {a : Q($A)} {b : Q(ℕ)} (za : BaseType sAlg a)
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:117:protected lemma IsCofinalFor.trans (hst : IsCofinalFor s t) (htu : IsCofinalFor t u) :
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:218:theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:230:theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:234:theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s ⊆ t) : a ≤ b :=
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:781:theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:789:theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:128:theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:148:theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:163:theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:207:theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:210:theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:262:theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:265:theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:412:theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:450:theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:456:lemma rpow_add_one' (hx : 0 ≤ x) (h : y + 1 ≠ 0) : x ^ (y + 1) = x ^ y * x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:476:theorem mul_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:513:lemma rpow_natCast_mul (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:516:lemma rpow_mul_natCast (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:546:theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988:theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:64:theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:71:theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:90:theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:93:theorem rpow_add' (h : y + z ≠ 0) (x : ℝ≥0) : x ^ (y + z) = x ^ y * x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:120:lemma rpow_add_one (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:126:lemma rpow_add_one' (h : y + 1 ≠ 0) (x : ℝ≥0) : x ^ (y + 1) = x ^ y * x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:140:theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:143:lemma rpow_natCast_mul (x : ℝ≥0) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:146:lemma rpow_mul_natCast (x : ℝ≥0) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:157:theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:160:theorem rpow_sub' (h : y - z ≠ 0) (x : ℝ≥0) : x ^ (y - z) = x ^ y / x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:185:theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:197:theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:560:theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:626:theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:664:theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:669:theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:994:lemma rpow_natCast_mul (x : ℝ≥0∞) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:997:lemma rpow_mul_natCast (x : ℝ≥0∞) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:217:lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Complex/Circle.lean:115:def exp : C(ℝ, Circle) where
.lake/packages/mathlib/Mathlib/Analysis/Complex/Circle.lean:128:theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:228:theorem continuous_rpow_const {q : ℝ} (h : 0 ≤ q) : Continuous (fun x : ℝ => x ^ q) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:422:theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:468:theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := by
.lake/packages/mathlib/Mathlib/Order/SuccPred/Archimedean.lean:60:theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Presheaf.lean:109:def restrict {F : X.Presheaf C}
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Presheaf.lean:191:def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Reflective.lean:107:instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G] :
.lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Reflective.lean:234:instance Coreflective.comp (F : C ⥤ D) (G : D ⥤ E) [Coreflective F] [Coreflective G] :
.lake/packages/mathlib/Mathlib/Order/Max.lean:207:theorem IsBot.mono (ha : IsBot a) (h : b ≤ a) : IsBot b := fun _ => h.trans <| ha _
.lake/packages/mathlib/Mathlib/Order/Max.lean:210:theorem IsMin.mono (ha : IsMin a) (h : b ≤ a) : IsMin b := fun _ hc => h.trans <| ha <| hc.trans h
.lake/packages/mathlib/Mathlib/Order/Max.lean:285:theorem IsBot.prodMk (ha : IsBot a) (hb : IsBot b) : IsBot (a, b) := fun _ => ⟨ha _, hb _⟩
.lake/packages/mathlib/Mathlib/Order/Max.lean:288:theorem IsMin.prodMk (ha : IsMin a) (hb : IsMin b) : IsMin (a, b) := fun _ hc => ⟨ha hc.1, hb hc.2⟩
.lake/packages/mathlib/Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean:122:protected lemma HasIndepIncrements.smul {R : Type*} [AddGroup E] [DistribSMul R E]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:255:protected lemma IsBigO.sqrt (hfg : f =O[l] g) (hg : 0 ≤ᶠ[l] g) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:259:protected lemma IsLittleO.sqrt (hfg : f =o[l] g) (hg : 0 ≤ᶠ[l] g) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:263:protected lemma IsTheta.sqrt (hfg : f =Θ[l] g) (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:176:theorem Filter.Tendsto.rexp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : Tendsto f l (𝓝 z)) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:183:theorem ContinuousWithinAt.rexp (h : ContinuousWithinAt f s x) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:189:theorem ContinuousAt.rexp (h : ContinuousAt f x) : ContinuousAt (fun y ↦ exp (f y)) x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:192:theorem ContinuousOn.rexp (h : ContinuousOn f s) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:196:theorem Continuous.rexp (h : Continuous f) : Continuous fun y ↦ exp (f y) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:445:lemma HasSum.rexp {ι} {f : ι → ℝ} {a : ℝ} (h : HasSum f a) : HasProd (rexp ∘ f) (rexp a) :=
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/Indep.lean:265:theorem IndepSets.symm {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω} {μ : Measure α}
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/Indep.lean:273:theorem Indep.symm {m₁ m₂ : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:589:lemma pow_nonneg {a : A} (ha : 0 ≤ a := by cfc_tac) (n : ℕ) : 0 ≤ a ^ n := by
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Stalks.lean:210:theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/IndepFun.lean:197:lemma iIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/IndepFun.lean:208:lemma iIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/IndepFun.lean:241:theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
.lake/packages/mathlib/Mathlib/Probability/Independence/Kernel/IndepFun.lean:250:theorem IndepFun.comp₀ {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Measure.lean:60:theorem measurableSet_Icc : MeasurableSet (Box.Icc I) :=
.lake/packages/mathlib/Mathlib/Tactic/TermCongr.lean:308:def CongrResult.trans (res1 res2 : CongrResult) : CongrResult where
.lake/packages/mathlib/Mathlib/CategoryTheory/Equivalence.lean:367:def symm (e : C ≌ D) : D ≌ C :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Equivalence.lean:384:def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
.lake/packages/mathlib/Mathlib/CategoryTheory/Equivalence.lean:522:def pow (e : C ≌ C) : ℤ → (C ≌ C)
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Filter.lean:330:theorem MemBaseSet.mono' (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Filter.lean:339:theorem MemBaseSet.mono (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Filter.lean:405:theorem RCond.mono {ι : Type*} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.RCond r) :
.lake/packages/mathlib/Mathlib/Order/Category/Frm.lean:117:lemma comp_apply {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean:289:lemma Commute.mul_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Commute a b) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Basic.lean:421:def restrict (π : Prepartition I) (J : Box ι) : Prepartition J :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Basic.lean:678:protected theorem restrict (h : IsPartition π) (hJ : J ≤ I) : IsPartition (π.restrict J) :=
.lake/packages/mathlib/Mathlib/Probability/Independence/Conditional.lean:374:theorem CondIndepSets.symm {s₁ s₂ : Set (Set Ω)}
.lake/packages/mathlib/Mathlib/Probability/Independence/Conditional.lean:444:theorem CondIndep.symm {m' m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
.lake/packages/mathlib/Mathlib/Probability/Independence/Conditional.lean:707:theorem CondIndepFun.comp {γ γ' : Type*} {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
.lake/packages/mathlib/Mathlib/Order/Category/BoolAlg.lean:115:lemma comp_apply {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Additive.lean:112:def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Bounded.lean:127:protected theorem IsVonNBounded.add (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Bounded.lean:149:protected theorem IsVonNBounded.sub (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Tagged.lean:238:theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Tagged.lean:242:theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean:344:theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} (h : IndepSets s₁ s₂ μ) : IndepSets s₂ s₁ μ :=
.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean:348:theorem Indep.symm (h : Indep m₁ m₂ μ) : Indep m₂ m₁ μ := IndepSets.symm h
.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean:799:theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean:805:theorem IndepFun.comp₀ {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
.lake/packages/mathlib/Mathlib/Order/Category/BddOrd.lean:115:lemma comp_apply {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/MulticoequalizerDiagram.lean:67:lemma le₁₂ : x₁ ≤ x₂ := by grind
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/MulticoequalizerDiagram.lean:68:lemma le₁₃ : x₁ ≤ x₃ := by grind
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/MulticoequalizerDiagram.lean:69:lemma le₂₄ : x₂ ≤ x₄ := by grind
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/MulticoequalizerDiagram.lean:70:lemma le₃₄ : x₃ ≤ x₄ := by grind
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:221:theorem HasIntegral.mono {l₁ l₂ : IntegrationParams} (h : HasIntegral I l₁ f vol y) (hl : l₂ ≤ l₁) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:230:theorem Integrable.mono {l'} (h : Integrable I l f vol) (hle : l' ≤ l) : Integrable I l' f vol :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:233:theorem HasIntegral.unique (h : HasIntegral I l f vol y) (h' : HasIntegral I l f vol y') : y = y' :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:246:theorem Integrable.add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:250:theorem integral_add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:273:theorem HasIntegral.sub (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:276:theorem Integrable.sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:280:theorem integral_sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:292:theorem integrable_const (c : E) : Integrable I l (fun _ => c) vol :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:314:theorem HasIntegral.smul (hf : HasIntegral I l f vol y) (c : ℝ) :
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:319:theorem Integrable.smul (hf : Integrable I l f vol) (c : ℝ) : Integrable I l (c • f) vol :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:327:theorem integral_smul (c : ℝ) : integral I l (fun x => c • f x) vol = c • integral I l f vol := by
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:338:theorem integral_nonneg {g : ℝⁿ → ℝ} (hg : ∀ x ∈ Box.Icc I, 0 ≤ g x) (μ : Measure ℝⁿ)
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Basic.lean:347:theorem norm_integral_le_of_norm_le {g : ℝⁿ → ℝ} (hle : ∀ x ∈ Box.Icc I, ‖f x‖ ≤ g x)
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean:964:def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean:967:theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:222:def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:494:def symm : P₂ ≃ᵃⁱ[𝕜] P :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:544:def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Iso.lean:87:def symm (I : X ≅ Y) : Y ≅ X where
.lake/packages/mathlib/Mathlib/CategoryTheory/Iso.lean:132:def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:305:def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:318:theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:410:def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:423:theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:513:def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:526:theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Category/NonemptyFinLinOrd.lean:82:lemma comp_apply {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Category/HeytAlg.lean:114:lemma comp_apply {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Heyting/Basic.lean:672:theorem LE.le.disjoint_compl_left (h : b ≤ a) : Disjoint aᶜ b :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Basic.lean:675:theorem LE.le.disjoint_compl_right (h : a ≤ b) : Disjoint a bᶜ :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Basic.lean:836:theorem LE.le.codisjoint_hnot_left (h : a ≤ b) : Codisjoint (￢a) b :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Basic.lean:839:theorem LE.le.codisjoint_hnot_right (h : b ≤ a) : Codisjoint a (￢b) :=
.lake/packages/mathlib/Mathlib/Order/Category/Lat.lean:120:lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:172:noncomputable def norm (A : Type*) {E : Type*} [Norm A] [Inner A E] : Norm E where
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:182:protected lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
.lake/packages/mathlib/Mathlib/Order/Category/FinPartOrd.lean:87:lemma comp_apply {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Category/PartOrd.lean:110:lemma comp_apply {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:55:theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:69:theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:74:theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := by
.lake/packages/mathlib/Mathlib/Order/Category/LinOrd.lean:94:lemma comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Basic.lean:119:theorem Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s) := fun _b hb =>
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Basic.lean:142:theorem Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t) := fun _a ha =>
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Basic.lean:145:theorem Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t) := by
.lake/packages/mathlib/Mathlib/Order/Category/FinBddDistLat.lean:121:lemma comp_apply {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Category/BddDistLat.lean:119:lemma comp_apply {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Category/PartOrdEmb.lean:114:lemma comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:324:theorem zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:328:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:332:theorem sub_apply : (x - y) i = x i - y i :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:342:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Probability/HasLaw.lean:85:lemma HasLaw.comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:177:theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:209:lemma rpow_add_le_add_rpow {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:311:theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
.lake/packages/mathlib/Mathlib/Order/Category/Preord.lean:113:lemma comp_apply {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra/Equiv.lean:221:def symm (e : A ≃A[R] B) : B ≃A[R] A where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra/Equiv.lean:257:def trans (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : A ≃A[R] C where
.lake/packages/mathlib/Mathlib/Order/Category/BddLat.lean:103:lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Order/Category/DistLat.lean:117:lemma comp_apply {X Y Z : DistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:471:def comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) : E →SWOT[σ₁₃] G :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:475:lemma comp_apply (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) (x : E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Field/Basic.lean:66:theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
.lake/packages/mathlib/Mathlib/Order/DirSupClosed.lean:76:lemma DirSupClosedOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupClosedOn D₂ s) : DirSupClosedOn D₁ s :=
.lake/packages/mathlib/Mathlib/Order/DirSupClosed.lean:80:lemma DirSupInaccOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) : DirSupInaccOn D₁ s :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Subobject/Classifier/Defs.lean:234:lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C)) : χ' = χ m :=
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:497:alias HasSubset.subset.trans_eq := subset_of_subset_of_eq
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:505:alias HasSubset.Subset.trans := subset_trans
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:543:alias HasSSubset.SSubset.trans_eq := ssubset_of_ssubset_of_eq
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:547:alias HasSSubset.SSubset.ne := ne_of_ssubset
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:549:alias HasSSubset.SSubset.ne' := ne_of_ssuperset
.lake/packages/mathlib/Mathlib/Order/RelClasses.lean:551:alias HasSSubset.SSubset.trans := ssubset_trans
.lake/packages/mathlib/Mathlib/Order/IsNormal.lean:104:theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:121:def norm : L → ℝ := fun x : L => hv.hom _ (v.restrict x)
.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:125:theorem norm_nonneg (x : L) : 0 ≤ v.norm x := by simp only [norm, NNReal.zero_le_coe]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:127:theorem norm_add_le (x y : L) : v.norm (x + y) ≤ max (v.norm x) (v.norm y) := by
.lake/packages/mathlib/Mathlib/Order/WellFounded.lean:73:theorem mono (hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r' :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Subobject/MonoOver.lean:110:instance mono (f : MonoOver X) : Mono f.arrow :=
.lake/packages/mathlib/Mathlib/Analysis/ODE/Basic.lean:98:lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:108:theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:114:theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:121:theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:126:theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:131:theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:135:theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:153:protected theorem Specializes.smul {a b : M} {x y : X} (h₁ : a ⤳ b) (h₂ : x ⤳ y) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/MulAction.lean:158:protected theorem Inseparable.smul {a b : M} {x y : X} (h₁ : Inseparable a b)
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:227:def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:236:theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:420:def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:428:theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/FilterBasis.lean:97:theorem mul {U : Set G} : U ∈ B → ∃ V ∈ B, V * V ⊆ U :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/FilterBasis.lean:247:theorem mul {U : Set R} (hU : U ∈ B) : ∃ V ∈ B, V * V ⊆ U :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/FilterBasis.lean:308:theorem smul {U : Set M} (hU : U ∈ B) : ∃ V ∈ 𝓝 (0 : R), ∃ W ∈ B, V • W ⊆ U :=
.lake/packages/mathlib/Mathlib/Order/Disjoint.lean:60:theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b → Disjoint b a :=
.lake/packages/mathlib/Mathlib/Order/Disjoint.lean:74:theorem Disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Disjoint b d → Disjoint a c :=
.lake/packages/mathlib/Mathlib/Order/Disjoint.lean:107:theorem Disjoint.ne (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b :=
.lake/packages/mathlib/Mathlib/Order/Disjoint.lean:342:protected theorem symm (h : IsCompl x y) : IsCompl y x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:136:def comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : P →ᴬ[R] Q₂ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:142:theorem comp_apply (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) (p : P) : f.comp g p = f (g p) := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:254:theorem zero_apply (x : P) : (0 : P →ᴬ[R] W) x = 0 := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:267:theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:291:theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:299:theorem sub_apply (f g : P →ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:276:def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:285:theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:405:def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:414:theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:510:def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:518:theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
.lake/packages/mathlib/Mathlib/Tactic/FieldSimp.lean:168:def mul : qNF q($M) → qNF q($M) → qNF q($M)
.lake/packages/mathlib/Mathlib/Analysis/Complex/Basic.lean:461:theorem norm_of_nonneg' {x : ℂ} (hx : 0 ≤ x) : ‖x‖ = x := by
.lake/packages/mathlib/Mathlib/Order/BooleanGenerators.lean:70:lemma mono (hS : BooleanGenerators S) {T : Set α} (hTS : T ⊆ S) : BooleanGenerators T where
.lake/packages/mathlib/Mathlib/Order/Partition/Basic.lean:365:lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz
.lake/packages/mathlib/Mathlib/Order/Basic.lean:606:alias StrongLT.trans_le := strongLT_of_strongLT_of_le
.lake/packages/mathlib/Mathlib/Order/Basic.lean:938:protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 ≤ y.2) : x < y := by simp [lt_iff, *]
.lake/packages/mathlib/Mathlib/Order/Basic.lean:1070:protected theorem le : a ≤ b :=
.lake/packages/mathlib/Mathlib/Order/Basic.lean:1085:instance Prop.le : LE Prop :=
.lake/packages/mathlib/Mathlib/Order/Partition/Finpartition.lean:186:protected theorem le {b : α} (hb : b ∈ P.parts) : b ≤ a :=
.lake/packages/mathlib/Mathlib/Order/Partition/Finpartition.lean:418:def restrict (P : Finpartition a) (hb : b ≤ a) : Finpartition b where
.lake/packages/mathlib/Mathlib/Order/Sublocale.lean:138:def restrict (S : Sublocale X) : FrameHom X S where
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:233:def comp (f : TopHom β γ) (g : TopHom α β) :
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:243:theorem comp_apply (f : TopHom β γ) (g : TopHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:417:def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:425:theorem comp_apply (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) (a : α) :
.lake/packages/mathlib/Mathlib/Tactic/Explode/Datatypes.lean:81:def Entries.add (entries : Entries) (expr : Expr) (entry : Entry) : Entry × Entries :=
.lake/packages/mathlib/Mathlib/Order/Cover.lean:42:theorem WCovBy.le (h : a ⩿ b) : a ≤ b :=
.lake/packages/mathlib/Mathlib/Order/Cover.lean:59:alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le
.lake/packages/mathlib/Mathlib/Order/Cover.lean:246:theorem CovBy.le (h : a ⋖ b) : a ≤ b :=
.lake/packages/mathlib/Mathlib/Order/Cover.lean:250:protected theorem CovBy.ne (h : a ⋖ b) : a ≠ b :=
.lake/packages/mathlib/Mathlib/Order/ScottContinuity.lean:64:lemma ScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : ScottContinuousOn D₂ f) :
.lake/packages/mathlib/Mathlib/Order/ScottContinuity.lean:85:theorem ScottContinuousOn.comp {g : β → γ} {D'}
.lake/packages/mathlib/Mathlib/Order/ScottContinuity.lean:107:lemma ScottContinuousOn.prodMk {g : α → γ} (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
.lake/packages/mathlib/Mathlib/Order/ScottContinuity.lean:166:lemma ScottContinuous.comp {g : β → γ}
.lake/packages/mathlib/Mathlib/Order/ScottContinuity.lean:173:lemma ScottContinuous.prodMk {g : α → γ}
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:399:theorem IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:404:theorem IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:409:theorem IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x + g x) s a :=
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:412:theorem IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x + g x) s a :=
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:443:theorem IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) :
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:446:theorem IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) :
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:449:theorem IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) :
.lake/packages/mathlib/Mathlib/Order/Filter/Extr.lean:453:theorem IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) :
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:151:lemma aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:308:protected lemma const_mul (h : HasSubgaussianMGF X c κ ν) (r : ℝ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:407:lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX κ ν)
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:617:lemma aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ := by
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:685:protected lemma const_mul (h : HasSubgaussianMGF X c μ) (r : ℝ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:720:lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:55:def exp' (z : ℂ) : CauSeq ℂ (‖·‖) :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:107:theorem exp_add : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Field.lean:31:theorem Multipliable.norm (hf : Multipliable f) : Multipliable (‖f ·‖) :=
.lake/packages/mathlib/Mathlib/Order/Cofinal.lean:51:theorem IsCofinal.mono {s t : Set α} (h : s ⊆ t) (hs : IsCofinal s) : IsCofinal t := by
.lake/packages/mathlib/Mathlib/Order/Cofinal.lean:76:theorem IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:326:theorem HasProd.unique {a₁ a₂ : α} :
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:168:protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:236:protected theorem mono (f : α →o β) : Monotone f :=
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:328:def comp (g : β →o γ) (f : α →o β) : α →o γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:457:def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:481:instance unique [Subsingleton α] : Unique (α →o α) where
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:773:def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:817:def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:127:lemma HasProdUniformlyOn.mono {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:132:lemma MultipliableUniformlyOn.mono {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:207:lemma HasProdLocallyUniformlyOn.mono {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:212:lemma MultipliableLocallyUniformlyOn.mono {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:268:theorem HasProdLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/UniformOn.lean:275:theorem MultipliableLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
.lake/packages/mathlib/Mathlib/Tactic/Ring/Common.lean:600:theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]
.lake/packages/mathlib/Mathlib/Tactic/Ring/Common.lean:891:theorem one_pow {a : R} (b : ℕ) (ha : IsNat a 1) : a ^ b = a := by
.lake/packages/mathlib/Mathlib/Order/Antichain.lean:54:theorem mono (hs : IsAntichain r₁ s) (h : r₂ ≤ r₁) : IsAntichain r₂ s :=
.lake/packages/mathlib/Mathlib/Order/Antichain.lean:316:theorem mono (hs : IsStrongAntichain r₁ s) (h : r₂ ≤ r₁) : IsStrongAntichain r₂ s :=
.lake/packages/mathlib/Mathlib/Order/Antichain.lean:393:protected theorem symm (h : IsMaxAntichain r s) : IsMaxAntichain (flip r) s :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:159:theorem mono {f : (i : α) → E i} {g : α → ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:177:theorem mono' {F : α → Type*} [∀ i, NormedAddCommGroup (F i)] {f : (i : α) → E i}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:247:theorem add {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f + g) p := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:274:theorem sub {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f - g) p := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:315:theorem const_mul {f : α → 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp (fun x => c * f x) p :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:341:instance PreLp.unique [IsEmpty α] : Unique (PreLp E) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:468:theorem norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:516:theorem norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖ := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean:70:theorem HasProd.prodMk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasProd f a L)
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:264:def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:272:theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:419:def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:428:theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:316:theorem HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:323:theorem Multipliable.mul (hf : Multipliable f L) (hg : Multipliable g L) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:328:lemma HasProd.pow (hf : HasProd f a L) (n : ℕ) : HasProd (f · ^ n) (a ^ n) L := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:334:lemma Multipliable.pow (hf : Multipliable f L) (n : ℕ) : Multipliable (f · ^ n) L :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:318:lemma mono₂ (h : T.mor₁ = 0) : Mono T.mor₂ := (T.mor₁_eq_zero_iff_mono₂ hT).1 h
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:319:lemma mono₃ (h : T.mor₂ = 0) : Mono T.mor₃ := (T.mor₂_eq_zero_iff_mono₃ hT).1 h
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean:320:lemma mono₁ (h : T.mor₃ = 0) : Mono T.mor₁ := (T.mor₃_eq_zero_iff_mono₁ hT).1 h
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:175:instance comp [adj.IsTriangulated] [adj'.IsTriangulated] : (adj.comp adj').IsTriangulated where
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:219:instance symm [E.IsTriangulated] : E.symm.IsTriangulated where
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Adjunction.lean:229:instance trans [E.IsTriangulated] [E'.IsTriangulated] : (E.trans E').IsTriangulated := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:34:protected theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:46:protected theorem norm_add_le' (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:61:protected theorem norm_neg' (z : ℂ) : ‖-z‖ = ‖z‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:73:protected theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:77:protected theorem norm_div (z w : ℂ) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:106:protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:116:lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:352:lemma smul_eq_mul {α : Type*} [Mul α] {a a' : α} (h : a = a') (b : α) : a • b = a' * b := by
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:356:theorem Nat.smul_eq_mul {n n' : ℕ} {r : R} (hr : n = r) (hn : n' = n) (a : R) : n' • a = r * a := by
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:361:theorem Int.smul_eq_mul {n n' : ℤ} {r : R} [CommRing R] (hr : n = r) (hn : n' = n) (a : R) :
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:380:partial def add {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:396:partial def mul {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:441:partial def pow {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
.lake/packages/mathlib/Mathlib/Order/OrdContinuous.lean:75:theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
.lake/packages/mathlib/Mathlib/Order/OrdContinuous.lean:80:theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:90:theorem HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (fun i ↦ f i / b) (a / b) L := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:93:theorem Summable.div_const (h : Summable f L) (b : α) : Summable (fun i ↦ f i / b) L :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:178:theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
.lake/packages/mathlib/Mathlib/Order/SupIndep.lean:93:lemma SupIndep.mono (hf : s.SupIndep f) (h : ∀ i ∈ s, g i ≤ f i) : s.SupIndep g :=
.lake/packages/mathlib/Mathlib/Order/SupIndep.lean:289:theorem sSupIndep.mono {t : Set α} (hst : t ⊆ s) : sSupIndep t := fun _ ha =>
.lake/packages/mathlib/Mathlib/Order/SupIndep.lean:361:theorem iSupIndep.mono {s t : ι → α} (hs : iSupIndep s) (hst : t ≤ s) : iSupIndep t :=
.lake/packages/mathlib/Mathlib/Order/SupIndep.lean:366:theorem iSupIndep.comp {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep t)
.lake/packages/mathlib/Mathlib/Order/SupIndep.lean:372:theorem iSupIndep.comp' {ι ι' : Sort*} {t : ι → α} {f : ι' → ι} (ht : iSupIndep <| t ∘ f)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:111:theorem zero_apply : (0 : PiLp p β) i = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:115:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:119:theorem sub_apply : (x - y) i = x i - y i :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:123:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Order/Filter/Ultrafilter/Defs.lean:60:theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f) (hne : NeBot g := by infer_instance) :
.lake/packages/mathlib/Mathlib/Order/JordanHolder.lean:259:theorem symm {s₁ s₂ : CompositionSeries X} (h : Equivalent s₁ s₂) : Equivalent s₂ s₁ :=
.lake/packages/mathlib/Mathlib/Order/JordanHolder.lean:263:theorem trans {s₁ s₂ s₃ : CompositionSeries X} (h₁ : Equivalent s₁ s₂) (h₂ : Equivalent s₂ s₃) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Module.lean:68:theorem HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Module.lean:72:theorem Summable.smul_const (hf : Summable f L) (a : M) : Summable (fun z ↦ f z • a) L :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Module.lean:99:theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
.lake/packages/mathlib/Mathlib/Order/Interval/Set/ProjIcc.lean:284:protected theorem Set.OrdConnected.restrict (hs : s.OrdConnected) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Triangulated/Basic.lean:137:def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
.lake/packages/mathlib/Mathlib/Order/Interval/Set/Basic.lean:280:theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/MStructure.lean:139:theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
.lake/packages/mathlib/Mathlib/Order/Directed.lean:73:theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
.lake/packages/mathlib/Mathlib/Order/Directed.lean:78:theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : ∀ ⦃a b⦄, r a b → r' a b) :
.lake/packages/mathlib/Mathlib/Order/Directed.lean:85:theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b)
.lake/packages/mathlib/Mathlib/Order/Directed.lean:346:lemma pi {d : (i : ι) → Set (α i)} (hd : ∀ (i : ι), DirectedOn (r i) (d i)) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:87:theorem IsSymmetric.add {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:97:theorem IsSymmetric.sub {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:103:theorem IsSymmetric.smul {c : 𝕜} (hc : conj c = c) {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Symmetric.lean:120:lemma IsSymmetric.pow {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean:112:theorem Bornology.IsBounded.smul₀ {s : Set E} (hs : IsBounded s) (c : 𝕜) : IsBounded (c • s) :=
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:74:lemma add {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:88:lemma smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:98:lemma mul {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:177:lemma sub {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:283:lemma pow {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:503:lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:647:lemma add (hf : Meromorphic f) (hg : Meromorphic g) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:659:lemma sub (hf : Meromorphic f) (hg : Meromorphic g) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:663:lemma smul {f : 𝕜 → 𝕜} (hf : Meromorphic f) (hg : Meromorphic g) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:667:lemma mul {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Basic.lean:686:lemma pow {f : 𝕜 → 𝕜'} {n : ℕ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).pow n
.lake/packages/mathlib/Mathlib/CategoryTheory/GradedObject.lean:221:theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:80:protected theorem IsFormalAdjoint.symm (h : T.IsFormalAdjoint S) :
.lake/packages/mathlib/Mathlib/Order/Filter/Defs.lean:352:def pi {ι : Type*} {α : ι → Type*} (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:212:theorem le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.1.le_opNorm m
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:241:theorem opNorm_le_bound (f : E [⋀^ι]→L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
.lake/packages/mathlib/Mathlib/Order/Filter/TendstoCofinite.lean:72:lemma comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineEquiv.lean:176:def symm (e : P₁ ≃ᴬ[k] P₂) : P₂ ≃ᴬ[k] P₁ where
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineEquiv.lean:271:def trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : P₁ ≃ᴬ[k] P₃ where
.lake/packages/mathlib/Mathlib/Order/Interval/Set/UnorderedInterval.lean:76:lemma uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:217:protected theorem map_zero (f : A →A[R] B) : f (0 : A) = 0 := map_zero f
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:345:def comp (g : B →A[R] C) (f : A →A[R] B) : A →A[R] C :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:355:theorem comp_apply (g : B →A[R] C) (f : A →A[R] B) (x : A) : (g.comp f) x = g (f x) := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:376:theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Order/Filter/IsBounded.lean:57:theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
.lake/packages/mathlib/Mathlib/Order/Filter/IsBounded.lean:60:theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) :
.lake/packages/mathlib/Mathlib/Order/Filter/IsBounded.lean:79:theorem IsBoundedUnder.comp {l : Filter γ} {q : β → β → Prop} {u : γ → α} {v : α → β}
.lake/packages/mathlib/Mathlib/Order/Filter/IsBounded.lean:266:theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
.lake/packages/mathlib/Mathlib/Order/Interval/Basic.lean:75:instance le : LE (NonemptyInterval α) :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:255:theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ := hf.ne'
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:260:theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:420:instance unique [IsEmpty α] : Unique (Filter α) where
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:645:theorem Eventually.of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:669:theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x)
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:754:theorem Frequently.of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) :
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:771:theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x)
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:961:theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:967:theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:983:theorem EventuallyEq.prodMk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:997:theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1002:theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g)
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1029:theorem EventuallyEq.smul {𝕜} [SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β}
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1129:theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1140:theorem EventuallyLE.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1147:theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:1154:theorem EventuallyLE.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean:249:theorem IsOrtho.symm {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean:281:theorem IsOrtho.mono {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (hV : V₂ ≤ V₁) (h : U₁ ⟂ V₁) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean:298:theorem IsOrtho.le {U V : Submodule 𝕜 E} (h : U ⟂ V) : U ≤ Vᗮ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/UniformMulAction.lean:130:theorem UniformContinuous.const_mul' [UniformContinuousConstSMul R R] {f : β → R}
.lake/packages/mathlib/Mathlib/Topology/Algebra/UniformMulAction.lean:134:theorem UniformContinuous.mul_const' [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β → R}
.lake/packages/mathlib/Mathlib/Topology/Algebra/UniformMulAction.lean:146:theorem UniformContinuous.div_const' {R β : Type*} [DivisionRing R] [UniformSpace R]
.lake/packages/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean:125:lemma IsConservativeOn.mono {U V : Set ℂ} (h : U ⊆ V) (hf : IsConservativeOn f V) :
.lake/packages/mathlib/Mathlib/Order/Bounded.lean:37:theorem Bounded.mono (hst : s ⊆ t) (hs : Bounded r t) : Bounded r s :=
.lake/packages/mathlib/Mathlib/Order/Bounded.lean:40:theorem Unbounded.mono (hst : s ⊆ t) (hs : Unbounded r s) : Unbounded r t := fun a =>
.lake/packages/mathlib/Mathlib/Order/Filter/Bases/Basic.lean:352:theorem HasBasis.restrict (h : l.HasBasis p s) {q : ι → Prop}
.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Basic.lean:158:theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := by
.lake/packages/mathlib/Mathlib/Order/Interval/Finset/Basic.lean:926:theorem uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean:172:theorem innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/ContinuousInverse.lean:141:lemma comp {g : F →L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/ContinuousInverse.lean:171:protected lemma inr : (ContinuousLinearMap.inr R F G).HasLeftInverse := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/ContinuousInverse.lean:306:lemma comp {g : F →L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:56:theorem comp {g : G → E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:79:protected theorem mono (h : DiffContOnCl 𝕜 f s) (ht : t ⊆ s) : DiffContOnCl 𝕜 f t :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:82:theorem add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f + g) s :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:88:theorem const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c + f x) s :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:94:theorem sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f - g) s :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:97:theorem sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x - c) s :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:107:theorem smul {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:112:theorem smul_const {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:95:protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:380:theorem le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:416:theorem opNorm_le_bound {f : ContinuousMultilinearMap 𝕜 E G}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean:45:theorem norm_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Ring/Basic.lean:588:def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:69:theorem zero_apply (n : ℕ) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0 := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:72:theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (p + q) n = p n + q n := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:75:theorem smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:178:theorem sub_apply (f g : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (f - g) n = f n - g n := rfl
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:282:theorem HasBasis.mul {ιf ιg : Type*} {pf : ιf → Prop} {sf : ιf → Set α}
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:316:protected theorem NeBot.mul : NeBot f → NeBot g → NeBot (f * g) :=
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:328:protected lemma mul.instNeBot [NeBot f] [NeBot g] : NeBot (f * g) := .mul ‹_› ‹_›
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:802:theorem HasBasis.smul {ιf ιg : Type*} {pf : ιf → Prop} {sf : ιf → Set α}
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:836:protected theorem NeBot.smul : NeBot f → NeBot g → NeBot (f • g) :=
.lake/packages/mathlib/Mathlib/Order/Filter/Pointwise.lean:848:lemma smul.instNeBot [NeBot f] [NeBot g] : NeBot (f • g) := .smul ‹_› ‹_›
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Positive.lean:124:theorem IsPositive.add {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Positive.lean:344:theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:366:theorem HasDerivAtFilter.mono (h : HasDerivAtFilter f f' L₂) (hst : L₁ ≤ L₂) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:370:theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:396:theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:670:theorem hasDerivAt_id : HasDerivAt id 1 x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:673:theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Datatypes.lean:59:partial def add : Linexp → Linexp → Linexp
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Datatypes.lean:156:def Comp.add (c1 c2 : Comp) : Comp :=
.lake/packages/mathlib/Mathlib/Order/Filter/Prod.lean:139:theorem Tendsto.prodMk {h : Filter γ} {m₁ : α → β} {m₂ : α → γ}
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:204:theorem finrank_euclideanSpace_fin {n : ℕ} :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:224:def restrict₂ (hIJ : I ⊆ J) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:232:lemma restrict₂_apply (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Pointed.lean:73:def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:106:theorem HasDerivWithinAt.smul (hc : HasDerivWithinAt c c' s x) (hf : HasDerivWithinAt f f' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:111:theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:117:theorem HasStrictDerivAt.smul (hc : HasStrictDerivAt c c' x) (hf : HasStrictDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:141:theorem HasStrictDerivAt.smul_const (hc : HasStrictDerivAt c c' x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:146:theorem HasDerivWithinAt.smul_const (hc : HasDerivWithinAt c c' s x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:151:theorem HasDerivAt.smul_const (hc : HasDerivAt c c' x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:263:theorem HasDerivWithinAt.mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:268:theorem HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:274:theorem HasStrictDerivAt.mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:300:theorem HasDerivWithinAt.mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:305:theorem HasDerivAt.mul_const (hc : HasDerivAt c c' x) (d : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:313:theorem HasStrictDerivAt.mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:352:theorem HasDerivWithinAt.const_mul (c : 𝔸) (hd : HasDerivWithinAt d d' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:357:theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:365:theorem HasStrictDerivAt.const_mul (c : 𝔸) (hd : HasStrictDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:561:theorem HasDerivAt.div_const (hc : HasDerivAt c c' x) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:565:theorem HasDerivWithinAt.div_const (hc : HasDerivWithinAt c c' s x) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:569:theorem HasStrictDerivAt.div_const (hc : HasStrictDerivAt c c' x) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:574:theorem DifferentiableWithinAt.div_const (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:579:theorem DifferentiableAt.div_const (hc : DifferentiableAt 𝕜 c x) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:584:theorem DifferentiableOn.div_const (hc : DifferentiableOn 𝕜 c s) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:588:theorem Differentiable.div_const (hc : Differentiable 𝕜 c) (d : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:637:theorem HasStrictDerivAt.clm_apply (hc : HasStrictDerivAt c c' x) (hu : HasStrictDerivAt u u' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:641:theorem HasDerivWithinAt.clm_apply (hc : HasDerivWithinAt c c' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:646:theorem HasDerivAt.clm_apply (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:109:lemma comp (h : EventuallyConst f l) (g : β → γ) : EventuallyConst (g ∘ f) l := h.map g
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:122:lemma comp₂ {g : α → γ} (hf : EventuallyConst f l) (op : β → γ → δ) (hg : EventuallyConst g l) :
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:127:lemma prodMk {g : α → γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:132:lemma mul [Mul β] {g : α → β} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:52:instance norm : Norm ℝ where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:56:theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:62:theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:142:protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:357:protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean:248:theorem inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean:387:theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:159:theorem SurjectiveOnWith.mono {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:207:theorem le_opNorm (x : V₁) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:243:theorem opNorm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:285:instance add : Add (NormedAddGroupHom V₁ V₂) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:303:theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:344:theorem zero_apply (v : V₁) : (0 : NormedAddGroupHom V₁ V₂) v = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:399:instance sub : Sub (NormedAddGroupHom V₁ V₂) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:411:theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:424:instance smul : SMul R (NormedAddGroupHom V₁ V₂) where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:443:theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:555:protected def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:721:theorem comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:232:theorem zero_apply (x : E) : (0 : GroupSeminorm E) x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:254:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:327:def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:338:theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:458:theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:527:theorem zero_apply (x : E) : (0 : NonarchAddGroupSeminorm E) x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:649:theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:703:theorem smul_apply (r : R) (p : NonarchAddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:777:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/AffineMap.lean:51:protected theorem differentiable : Differentiable 𝕜 f := fun _ ↦ f.differentiableAt
.lake/packages/mathlib/Mathlib/Order/Minimal.lean:111:theorem Minimal.mono (h : Minimal P x) (hle : Q ≤ P) (hQ : Q x) : Minimal Q x :=
.lake/packages/mathlib/Mathlib/Order/Minimal.lean:285:theorem Minimal.le (h : Minimal P x) (hy : P y) : x ≤ y :=
.lake/packages/mathlib/Mathlib/Order/Minimal.lean:289:theorem MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i ≤ f j :=
.lake/packages/mathlib/Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:49:theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero β]
.lake/packages/mathlib/Mathlib/Order/Filter/ZeroAndBoundedAtFilter.lean:96:theorem BoundedAtFilter.smul
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:144:protected def comp (g : s →r t) (f : r →r s) : r →r t :=
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:267:protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:309:protected theorem symm (f : r ↪r s) [Std.Symm s] : Std.Symm r :=
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:603:protected def symm (f : r ≃r s) : s ≃r r :=
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:624:protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:43:theorem HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' L)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:47:theorem HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:51:theorem HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Prod.lean:55:theorem HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x)
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean:180:def PComp.add (c1 c2 : PComp) (elimVar : ℕ) : PComp :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean:106:theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean:119:theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:931:lemma KrullDimLE.mono {n m : ℕ} (e : n ≤ m) (α : Type*) [Preorder α] [KrullDimLE n α] :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Pi.lean:74:theorem UniqueDiffWithinAt.pi (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Pi.lean:83:theorem UniqueDiffOn.pi (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:629:theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:640:theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖ = ofNat(n) :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:866:lemma norm_of_nonneg' {x : K} (hx : 0 ≤ x) : ‖x‖ = x := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:93:lemma comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:147:theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:169:instance Hom.add {M N : SemiNormedGrp} : Add (M ⟶ N) where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:183:instance Hom.sub {M N : SemiNormedGrp} : Sub (M ⟶ N) where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:297:lemma comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:365:theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Lemmas.lean:35:theorem zero_lt_one [IsStrictOrderedRing α] : (0:α) < 1 :=
.lake/packages/mathlib/Mathlib/Order/Filter/CountablyGenerated.lean:230:instance pi.isCountablyGenerated {ι : Type*} {α : ι → Type*} [Countable ι]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:44:theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' L)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:49:theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:54:theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:59:theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:339:theorem HasDerivAtFilter.sub (hf : HasDerivAtFilter f f' L) (hg : HasDerivAtFilter g g' L) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:344:theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:349:theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:354:theorem HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Parsing.lean:96:def Sum.mul (s1 s2 : Sum) : Sum :=
.lake/packages/mathlib/Mathlib/Tactic/Linarith/Parsing.lean:101:partial def Sum.pow (s : Sum) : ℕ → Sum
.lake/packages/mathlib/Mathlib/Tactic/ToFun.lean:29:theorem Differentiable.mul (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Bipointed.lean:70:def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
.lake/packages/mathlib/Mathlib/Tactic/Abel.lean:250:theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:230:theorem HasDerivAtFilter.comp (hh₂ : HasDerivAtFilter h₂ h₂' L')
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:243:theorem HasDerivWithinAt.comp (hh₂ : HasDerivWithinAt h₂ h₂' s' (h x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:258:theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:271:theorem HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:290:theorem HasDerivWithinAt.comp_hasDerivAt {t} (hh₂ : HasDerivWithinAt h₂ h₂' t (h x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:369:theorem HasFDerivWithinAt.comp_hasDerivAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:389:theorem HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean:221:theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean:242:theorem UniformContinuous.mul_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean:247:theorem UniformContinuous.const_mul [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Defs.lean:260:theorem UniformContinuous.div_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f)
.lake/packages/mathlib/Mathlib/Order/Filter/Ring.lean:35:theorem EventuallyLE.mul_nonneg [Semiring β] [PartialOrder β] [IsOrderedRing β]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean:154:theorem OrthogonalFamily.comp {γ : Type*} {f : γ → ι} (hf : Function.Injective f) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Pairwise.lean:84:def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Sqrt.lean:26:noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Sqrt.lean:44:noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 := map ℂ 𝕜 (map 𝕜 ℂ a).sqrt
.lake/packages/mathlib/Mathlib/Order/WellQuasiOrder.lean:88:theorem WellQuasiOrdered.pi {ι : Type*} {α : ι → Type*} [Finite ι] {r : ∀ i, (α i → α i → Prop)}
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:59:theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:105:theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:455:theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:39:theorem HasStrictDerivAt.pow' (h : HasStrictDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:49:theorem HasDerivWithinAt.pow' (h : HasDerivWithinAt f f' s x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:58:theorem HasDerivAt.pow' (h : HasDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:98:theorem HasStrictDerivAt.pow (h : HasStrictDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:105:theorem HasDerivWithinAt.pow (h : HasDerivWithinAt f f' s x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean:112:theorem HasDerivAt.pow (h : HasDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Monad/Algebra.lean:77:def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
.lake/packages/mathlib/Mathlib/CategoryTheory/Monad/Algebra.lean:288:def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:114:theorem CauchySeq.mul {ι : Type*} [Preorder ι] {u v : ι → α} (hu : CauchySeq u)
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:119:theorem CauchySeq.mul_const {ι : Type*} [Preorder ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:124:theorem CauchySeq.const_mul {ι : Type*} [Preorder ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:149:theorem TendstoUniformlyOnFilter.mul (hf : TendstoUniformlyOnFilter f g l l')
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:166:theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s)
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:181:theorem TendstoUniformly.mul (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:196:theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:218:theorem TendstoLocallyUniformlyOn.mul
.lake/packages/mathlib/Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:235:theorem TendstoLocallyUniformly.mul
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:117:theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:179:theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:194:theorem Continuous.norm' : Continuous f → Continuous fun x => ‖f x‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:224:theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:232:theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean:242:theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:43:instance norm : Norm (ULift E) where norm x := ‖x.down‖
.lake/packages/mathlib/Mathlib/Tactic/Sat/FromLRAT.lean:144:theorem Valuation.by_cases {v : Valuation} {l}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean:95:theorem mono_set (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Cat/CartesianClosed.lean:42:def exp : Cat ⥤ Cat where
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:129:protected theorem sub (x : E) : f (c - x) = f (c + x) := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp/Completion.lean:84:theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:158:theorem ContDiffAt.norm (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:167:theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:178:theorem ContDiffOn.norm (hf : ContDiffOn ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:185:theorem ContDiff.norm (hf : ContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => ‖f y‖ :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:237:theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:248:theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:259:theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean:272:theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:66:theorem mul_le_mul_of_nonneg_left [Mul α] [Zero α] [Preorder α] [PosMulMono α]
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:70:theorem mul_le_mul_of_nonneg_right [Mul α] [Zero α] [Preorder α] [MulPosMono α]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:108:lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:112:lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:124:theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
.lake/packages/mathlib/Mathlib/Order/Filter/CountableSeparatingOn.lean:113:theorem HasCountableSeparatingOn.mono {α} {p₁ p₂ : Set α → Prop} {t₁ t₂ : Set α}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:135:theorem prodMk {g : E → G} (hf : ContDiffPointwiseHolderAt k α f a)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:194:theorem comp {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:200:theorem comp₂_of_differentiableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:265:theorem clm_apply {f : E → F →L[ℝ] G} {g : E → F} (hf : ContDiffPointwiseHolderAt k α f a)
.lake/packages/mathlib/Mathlib/Order/Antisymmetrization.lean:65:theorem AntisymmRel.symm : AntisymmRel r a b → AntisymmRel r b a :=
.lake/packages/mathlib/Mathlib/Order/Antisymmetrization.lean:75:theorem AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c) :
.lake/packages/mathlib/Mathlib/Order/Antisymmetrization.lean:114:theorem AntisymmRel.le (h : AntisymmRel (· ≤ ·) a b) : a ≤ b := h.1
.lake/packages/mathlib/Mathlib/Order/Antisymmetrization.lean:182:alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
.lake/packages/mathlib/Mathlib/Order/Antisymmetrization.lean:183:alias AntisymmRel.trans_le := le_of_antisymmRel_of_le
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Pointwise.lean:32:theorem Bornology.IsBounded.mul (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s * t) := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:191:theorem Orthonormal.comp {ι' : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (f : ι' → ι)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean:73:theorem mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:114:lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:156:theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:177:theorem LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:497:theorem HasLineDerivWithinAt.smul (h : HasLineDerivWithinAt 𝕜 f f' s x v) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:514:theorem HasLineDerivAt.smul (h : HasLineDerivAt 𝕜 f f' x v) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:523:theorem LineDifferentiableWithinAt.smul (h : LineDifferentiableWithinAt 𝕜 f s x v) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:531:theorem LineDifferentiableAt.smul (h : LineDifferentiableAt 𝕜 f x v) (c : 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:97:lemma HarmonicOnNhd.mono (h : HarmonicOnNhd f s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:114:theorem HarmonicAt.add (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:124:theorem HarmonicAt.sub (h₁ : HarmonicAt f₁ x) (h₂ : HarmonicAt f₂ x) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:134:theorem HarmonicOnNhd.add (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:140:theorem HarmonicOnNhd.sub (h₁ : HarmonicOnNhd f₁ s) (h₂ : HarmonicOnNhd f₂ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:70:protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
.lake/packages/mathlib/Mathlib/Order/SemiconjSup.lean:59:protected theorem unique [PartialOrder α] [Preorder β] {f : α → β} {g₁ g₂ : β → α}
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:152:def comp (g : B →ₜ* C) (f : A →ₜ* B) : A →ₜ* C :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:214:def inr : B →ₜ* (A × B) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:231:def mul : (E × E) →ₜ* E := ⟨mulMonoidHom, continuous_mul⟩
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:244:theorem mul_apply (f g : A →ₜ* E) (a : A) : (f * g) a = f a * g a := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:435:def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:525:def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L where
.lake/packages/mathlib/Mathlib/Tactic/FunProp.lean:83:theorem continuous_id : Continuous (fun x ↦ x) := ...
.lake/packages/mathlib/Mathlib/Tactic/FunProp.lean:86:theorem continuous_const (y : Y) : Continuous (fun x ↦ y) := ...
.lake/packages/mathlib/Mathlib/Tactic/FunProp.lean:166:    theorem continuous_id : Continuous (fun (x : X) ↦ x) := ..
.lake/packages/mathlib/Mathlib/Tactic/FunProp.lean:172:    theorem continuous_const (y : Y) : Continuous (fun (x : X) ↦ y) := ..
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:99:protected theorem add (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x) :
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:114:protected theorem sub (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:122:protected theorem mul_const (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (m * n) x := by
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:125:protected theorem const_mul (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (n * m) x := by
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:136:theorem comp {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:140:theorem Continuous.prodMk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:156:theorem Continuous.comp₂ {g : X × Y → Z} (hg : Continuous g) {e : W → X} (he : Continuous e)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:160:theorem Continuous.comp₃ {g : X × Y × Z → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:165:theorem Continuous.comp₄ {g : X × Y × Z × ζ → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:347:theorem ContinuousAt.prodMk {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:361:theorem ContinuousAt.comp₂ {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X}
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:366:theorem ContinuousAt.comp₂_of_eq {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X} {y : Y × Z}
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:745:protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:749:protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:765:theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y → X ⊕ Y) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean:295:lemma LipschitzOnWith.mul (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean:304:lemma LipschitzWith.mul (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean:309:lemma LocallyLipschitzOn.mul (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean:317:lemma LocallyLipschitz.mul (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:74:protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:267:protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:533:protected theorem UniqueDiffWithinAt.smul (h : UniqueDiffWithinAt 𝕜 s x)
.lake/packages/mathlib/Mathlib/CategoryTheory/Join/Basic.lean:79:def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
.lake/packages/mathlib/Mathlib/Topology/Bornology/Hom.lean:140:def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
.lake/packages/mathlib/Mathlib/Topology/Bornology/Hom.lean:150:theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/Hom/Open.lean:120:def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
.lake/packages/mathlib/Mathlib/Topology/Hom/Open.lean:128:theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Int.lean:30:theorem norm_eq_abs (n : ℤ) : ‖n‖ = |(n : ℝ)| :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:310:def leftAdjointSquare.comp :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Adjunction/Mate.lean:337:def rightAdjointSquare.comp :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:100:theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:106:theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:114:theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:120:theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:125:theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:130:theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:134:theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:82:lemma mono (h : Absorbs M s₁ t₁) (hs : s₁ ⊆ s₂) (ht : t₂ ⊆ t₁) : Absorbs M s₂ t₂ :=
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:126:protected lemma add [AddZeroClass E] [DistribSMul M E]
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:208:lemma Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
.lake/packages/mathlib/Mathlib/Topology/Bornology/Absorbs.lean:220:protected theorem mono (ht : Absorbent M s) (hsub : s ⊆ t) : Absorbent M t := fun x ↦
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:159:def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
.lake/packages/mathlib/Mathlib/Topology/Bornology/Constructions.lean:107:theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:94:theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:124:theorem differentiable {f : X → Y} (h : Conformal f) : Differentiable ℝ f := fun x =>
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:127:theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/OmegaCompletePartialOrder.lean:604:def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Ergodic.lean:188:theorem symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ where
.lake/packages/mathlib/Mathlib/Tactic/ITauto.lean:361:partial def Context.add : IProp → Proof → Context → Except (IProp → Proof) Context
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:114:theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
.lake/packages/mathlib/Mathlib/Topology/CompactOpen.lean:473:theorem continuous_const' : Continuous (const X : Y → C(X, Y)) :=
.lake/packages/mathlib/Mathlib/Topology/Bases.lean:470:theorem IsSeparable.mono {s u : Set α} (hs : IsSeparable s) (hu : u ⊆ s) : IsSeparable u := by
.lake/packages/mathlib/Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean:178:def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean:81:lemma comp₂_iso_hom {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean:85:lemma comp₂_iso_inv {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
.lake/packages/mathlib/Mathlib/Topology/UnitInterval.lean:75:def symm : I → I := fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩
.lake/packages/mathlib/Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean:114:def comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:92:def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:143:theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:156:theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:551:theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:607:theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:174:theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:426:theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:482:theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Types/Basic.lean:78:def Fun.comp {X Y Z : Type*} (f : Fun Y Z) (g : Fun X Y) : Fun X Z := mk (f.toFun ∘ g.toFun)
.lake/packages/mathlib/Mathlib/CategoryTheory/Types/Basic.lean:272:theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
.lake/packages/mathlib/Mathlib/Topology/Maps/OpenQuotient.lean:49:theorem comp {g : Y → Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:59:theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:64:theorem HasFDerivWithinAt.smul
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:72:theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:78:theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:83:theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:88:theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:92:theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:116:theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:121:theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:126:theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:131:theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:136:theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:141:theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:145:theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:170:theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:177:theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:184:theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:191:theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:198:theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:205:theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:212:theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:217:theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:222:theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:226:theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:270:theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:275:theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:282:theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:287:theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:294:theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:299:theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:306:theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:311:theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:316:theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:320:theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:342:theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:347:theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:352:theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:357:theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:362:theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:367:theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:371:theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
.lake/packages/mathlib/Mathlib/CategoryTheory/EpiMono.lean:80:def SplitMono.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (smf : SplitMono f) (smg : SplitMono g) :
.lake/packages/mathlib/Mathlib/CategoryTheory/EpiMono.lean:110:def SplitEpi.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g) :
.lake/packages/mathlib/Mathlib/CategoryTheory/EpiMono.lean:169:theorem SplitMono.mono {X Y : C} {f : X ⟶ Y} (sm : SplitMono f) : Mono f :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:221:theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:306:protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:343:protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:1126:lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:288:theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:561:theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1150:theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : n ≠ 0) : Differentiable 𝕜 f :=
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean:81:protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean:323:theorem EqOnSource.symm' {e e' : OpenPartialHomeomorph X Y} (h : e ≈ e') : e.symm ≈ e'.symm :=
.lake/packages/mathlib/Mathlib/Topology/Inseparable.lean:135:theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
.lake/packages/mathlib/Mathlib/Topology/Inseparable.lean:387:lemma SpecializingMap.comp {f : X → Y} {g : Y → Z}
.lake/packages/mathlib/Mathlib/Topology/Inseparable.lean:430:lemma GeneralizingMap.comp {f : X → Y} {g : Y → Z}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:164:theorem HasFTaylorSeriesUpToOn.add {n : ℕ∞ω} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:177:theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:183:theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:189:theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:195:theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:307:theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:313:theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:318:theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:324:theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:444:theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:456:theorem ContDiffOn.mul {f g : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:461:theorem ContDiff.mul {f g : E → 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:507:theorem ContDiff.pow {f : E → 𝔸} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:512:theorem ContDiffWithinAt.pow {f : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:522:theorem ContDiffOn.pow {f : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:526:theorem ContDiffWithinAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:536:theorem ContDiffOn.div_const {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:540:theorem ContDiff.div_const {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:561:theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜'} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:567:theorem ContDiffAt.smul {f : E → 𝕜'} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:573:theorem ContDiff.smul {f : E → 𝕜'} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:579:theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜'} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:616:theorem ContDiffWithinAt.smul_const {s : Set E} {f : E → A} {x : E}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:630:theorem ContDiffAt.smul_const {f : E → A} {x : E} (hf : ContDiffAt 𝕜 n f x) (v : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:642:theorem ContDiff.smul_const {f : E → A} (hf : ContDiff 𝕜 n f) (v : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:653:theorem ContDiffOn.smul_const {s : Set E} {f : E → A} (hf : ContDiffOn 𝕜 n f s) (v : F) :
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:73:protected lemma IsInducing.comp (hg : IsInducing g) (hf : IsInducing f) :
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:200:protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:282:protected lemma comp (hg : IsCoinducing g) (hf : IsCoinducing f) : IsCoinducing (g.comp f) where
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:317:protected theorem comp (hg : IsQuotientMap g) (hf : IsQuotientMap f) : IsQuotientMap (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:355:protected theorem comp (hg : IsOpenMap g) (hf : IsOpenMap f) :
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:519:protected theorem comp (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:751:protected lemma comp (hg : IsOpenEmbedding g)
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:834:theorem comp (hg : IsClosedEmbedding g) (hf : IsClosedEmbedding f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:69:protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:133:theorem differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean:79:protected def symm : OpenPartialHomeomorph Y X where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:130:theorem map_zero [Nonempty ι] : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:175:theorem smul_apply (f : M [⋀^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:214:theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:259:def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:495:theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:260:theorem ContinuousAlternatingMap.differentiable (f : E [⋀^ι]→L[𝕜] F) : Differentiable 𝕜 f := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictlyUnitary.lean:162:def comp (F : StrictlyUnitaryLaxFunctor B C)
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictlyUnitary.lean:351:def comp (F : StrictlyUnitaryPseudofunctor B C)
.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:73:theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:99:protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:116:protected theorem trans {e : α ≃ᵐ β} {e' : β ≃ᵐ γ}
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Equiv.lean:93:def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Equiv.lean:130:def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:537:theorem HasFTaylorSeriesUpToOn.prodMk {n : ℕ∞ω}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:552:theorem ContDiffWithinAt.prodMk {s : Set E} {f : E → F} {g : E → G}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:573:theorem ContDiffOn.prodMk {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:579:theorem ContDiffAt.prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:585:theorem ContDiff.prodMk {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean:141:def pi : OpenPartialHomeomorph (∀ i, X i) (∀ i, Y i) where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Prelax.lean:92:def comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxFunctorStruct B D where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Prelax.lean:146:def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:105:def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:119:def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:209:def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:251:theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:254:theorem symm₂ {p q : Path x₀ x₁} (h : p.Homotopic q) : p.symm.Homotopic q.symm :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:258:theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:353:def symm (P : Path.Homotopic.Quotient x₀ x₁) : Path.Homotopic.Quotient x₁ x₀ :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Path.lean:383:def trans (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:192:protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:269:theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:314:theorem zero_apply (x : M₁) : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:389:instance add : Add (M₁ →SL[σ₁₂] M₂) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:393:theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:453:def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:474:theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:566:theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:863:theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:891:instance sub : Sub (M →SL[σ₁₂] M₂) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:902:theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean:125:lemma IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMap f) :
.lake/packages/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean:282:lemma IsProperMap.restrict {C : Set X} (hf : IsProperMap f) (hC : IsClosed C) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:52:theorem HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' L)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:57:protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:84:theorem DifferentiableWithinAt.prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:90:theorem DifferentiableAt.prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:95:theorem DifferentiableOn.prodMk (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:99:theorem Differentiable.prodMk (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Lax.lean:168:def comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:1054:theorem HasFTaylorSeriesUpToOn.comp {n : WithTop ℕ∞} {g : F → G} {f : E → F}
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:209:def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:228:def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:281:def comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:312:protected def pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:341:theorem symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:345:theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:348:theorem comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:365:protected theorem pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:458:def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:474:def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:521:theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:529:theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:572:def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:587:def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:646:theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:650:theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Pseudofunctor.lean:154:def comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Composition.lean:41:protected def trans' (h : e.target = e'.source) : OpenPartialHomeomorph X Z where
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Composition.lean:52:protected def trans : OpenPartialHomeomorph X Z :=
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Composition.lean:140:theorem EqOnSource.trans' {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
.lake/packages/mathlib/Mathlib/Tactic/CategoryTheory/Bicategory/Datatypes.lean:425:def comp? (e : Expr) : BicategoryM (Option (Mor₁ × Mor₁)) := do
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean:134:def comp (F : StrictPseudofunctor B C)
.lake/packages/mathlib/Mathlib/Dynamics/Circle/RotationNumber/TranslationNumber.lean:181:theorem mul_apply (x) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:65:def HomotopyRel.pi (homotopies : ∀ i : I, HomotopyRel (f i) (g i) S) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Product.lean:117:def pi (γ : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:82:theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:125:theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:155:theorem ContDiff.comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:425:theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:429:theorem ContDiffAt.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:435:theorem ContDiffAt.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:441:theorem ContDiff.comp₂_contDiffAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:446:theorem ContDiff.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:452:theorem ContDiff.comp₂_contDiffOn {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:457:theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:462:theorem ContDiff.comp₃_contDiffOn {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:495:theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiff 𝕜 n f)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:500:theorem ContDiffOn.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:505:theorem ContDiffAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:510:theorem ContDiffWithinAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:724:theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:750:theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Oplax.lean:172:def comp (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D) : B ⥤ᵒᵖᴸ D where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:63:def inr : M₂ →L[R] M₁ × M₂ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean:165:def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:192:theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:198:theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:203:theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:208:theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:213:theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:218:theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:223:theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:227:theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:612:theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFilter g g' L) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:617:theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:622:theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:627:theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:632:theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:637:theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:663:theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:688:theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:769:theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:779:theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:784:theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:788:theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/ColimitPresentation.lean:57:def Total.Hom.comp {k l m : Total P} (f : k.Hom l) (g : l.Hom m) : k.Hom m where
.lake/packages/mathlib/Mathlib/Topology/Homotopy/TopCat/Basic.lean:64:abbrev symm := ContinuousMap.Homotopy.symm F
.lake/packages/mathlib/Mathlib/Topology/Homotopy/TopCat/Basic.lean:70:noncomputable abbrev trans := ContinuousMap.Homotopy.trans F G
.lake/packages/mathlib/Mathlib/Topology/Homotopy/TopCat/Basic.lean:74:abbrev comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:47:theorem HasFDerivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter (F × F)}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:68:protected theorem HasStrictFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:74:theorem HasFDerivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:105:theorem HasFDerivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFDerivAt g g' (f x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:110:theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:116:theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:127:theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:204:theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:214:theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:92:theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s := by
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:460:theorem DefinableFun.mono {B : Set M} (hAs : A.DefinableFun L f) (hAB : A ⊆ B) :
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:531:theorem DefinableFun.comp [Finite α] {g : (β → M) → α → M}
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:618:theorem TermDefinable.mono {f : (α → M) → M} (h : A.TermDefinable L f) (hAB : A ⊆ B) :
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:627:theorem TermDefinable.trans {f : (β → M) → M} (h₁ : A.TermDefinable L f)
.lake/packages/mathlib/Mathlib/ModelTheory/Definability.lean:686:theorem TermDefinable.comp {f : (α → M) → M} {g : α → (β → M) → M} (hf : A.TermDefinable L f)
.lake/packages/mathlib/Mathlib/Topology/Order/LocalExtr.lean:263:theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
.lake/packages/mathlib/Mathlib/Topology/Order/LocalExtr.lean:267:theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
.lake/packages/mathlib/Mathlib/Topology/Order/LocalExtr.lean:271:theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:100:theorem IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Retract.lean:78:def trans {Z : C} (h' : Retract Y Z) : Retract X Z where
.lake/packages/mathlib/Mathlib/Dynamics/FixedPoints/Basic.lean:37:protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:171:theorem HasFTaylorSeriesUpToOn.mono (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:761:theorem HasFTaylorSeriesUpTo.differentiable (h : HasFTaylorSeriesUpTo n f p) (hn : n ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:940:lemma iteratedFDeriv_two_apply (f : E → F) (z : E) (m : Fin 2 → E) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:171:theorem zero_apply [Zero β] : (0 : C₀(α, β)) x = 0 :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:182:theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:199:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:214:theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:251:theorem sub_apply : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:583:def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:64:theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:545:theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:818:lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/NonPreadditive.lean:336:theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/NonPreadditive.lean:343:theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/NonPreadditive.lean:396:theorem add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a := by rw [add_def, neg_def, sub_self, sub_zero]
.lake/packages/mathlib/Mathlib/Tactic/CategoryTheory/Monoidal/Datatypes.lean:419:def comp? (e : Expr) : MonoidalM (Option (Mor₁ × Mor₁)) := do
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:59:theorem HasStrictFDerivAt.pow' (h : HasStrictFDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:79:theorem HasFDerivWithinAt.pow' (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:98:theorem HasFDerivAt.pow' (h : HasFDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:113:theorem DifferentiableWithinAt.pow (hf : DifferentiableWithinAt 𝕜 f s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:127:theorem DifferentiableAt.pow (hf : DifferentiableAt 𝕜 f x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:138:theorem DifferentiableOn.pow (hf : DifferentiableOn 𝕜 f s) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:150:theorem Differentiable.pow (hf : Differentiable 𝕜 f) (n : ℕ) : Differentiable 𝕜 (f ^ n) :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:204:theorem HasStrictFDerivAt.pow (h : HasStrictFDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:213:theorem HasFDerivWithinAt.pow (h : HasFDerivWithinAt f f' s x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:222:theorem HasFDerivAt.pow (h : HasFDerivAt f f' x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ContinuousMapZero.lean:82:def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ContinuousMapZero.lean:87:lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl
.lake/packages/mathlib/Mathlib/CategoryTheory/Grothendieck.lean:111:def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:173:theorem add_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:184:theorem sub_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:228:theorem smul_apply {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
.lake/packages/mathlib/Mathlib/ModelTheory/Equivalence.lean:55:protected theorem trans {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ) :
.lake/packages/mathlib/Mathlib/ModelTheory/Equivalence.lean:132:protected theorem mpr {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
.lake/packages/mathlib/Mathlib/ModelTheory/Equivalence.lean:143:protected theorem symm {φ ψ : L.BoundedFormula α n}
.lake/packages/mathlib/Mathlib/ModelTheory/Equivalence.lean:152:protected theorem trans {φ ψ θ : L.BoundedFormula α n}
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:359:def restrict (f : α →ᵇ β) (s : Set α) : s →ᵇ β :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:370:def comp (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:381:theorem comp_apply (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:510:theorem mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:657:theorem sub_apply {x : α} : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:717:theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl
.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:130:theorem map_zero : ϕ 0 = id := funext ϕ.map_zero'
.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:143:def restrict {s : Set α} (h : IsInvariant ϕ s) : Flow τ (↥s) where
.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:233:theorem IsSemiconjugacy.comp {π : α → β} {ρ : β → γ}
.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:248:theorem IsFactorOf.trans (h₁ : IsFactorOf ϕ ψ) (h₂ : IsFactorOf ψ χ) : IsFactorOf ϕ χ :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:121:theorem HasGradientAt.unique {gradf gradg : F}
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean:294:theorem map_zero₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (y : F) : f 0 y = 0 := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:120:theorem map_zero [Nonempty ι] : f 0 = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:130:theorem zero_apply (m : ∀ i, M₁ i) : (0 : ContinuousMultilinearMap R M₁ M₂) m = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:147:theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:234:def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:496:theorem sub_apply (m : ∀ i, M₁ i) : (f - f') m = f m - f' m :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:113:def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:121:theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:188:def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:242:def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:281:def restrict (f : C(α, β)) : C(s, β) where
.lake/packages/mathlib/Mathlib/ModelTheory/Arithmetic/Presburger/Semilinear/Defs.lean:98:theorem IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSet (s₁ + s₂) := by
.lake/packages/mathlib/Mathlib/ModelTheory/Arithmetic/Presburger/Semilinear/Defs.lean:189:theorem IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:189:theorem zero_apply [Zero β] : (0 : C_c(α, β)) x = 0 :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:199:theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:234:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:255:theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:303:theorem sub_apply : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:562:def comp (f : C_c(γ, δ)) (g : β →co γ) : C_c(β, δ) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean:139:def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean:147:theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Quotient/Preadditive.lean:32:def add (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
.lake/packages/mathlib/Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:135:theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
.lake/packages/mathlib/Mathlib/CategoryTheory/ObjectProperty/Basic.lean:79:lemma Nonempty.mono {P Q : ObjectProperty C} [P.Nonempty] (hPQ : P ≤ Q) : Q.Nonempty :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Quotient/Linear.lean:37:def smul (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:142:theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:230:def Homeomorph.smul (γ : G) : α ≃ₜ α where
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:246:theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:254:theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:262:theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:367:theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean:416:theorem IsClosed.smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
.lake/packages/mathlib/Mathlib/ModelTheory/Satisfiability.lean:78:theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Quotient.lean:152:def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg ↦
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:334:def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:342:theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:458:def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:467:theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:535:def symm (f : M ≃[L] N) : N ≃[L] M :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:632:def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:641:theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/IsInvertedBy.lean:84:lemma pi {J : Type w} {C : J → Type u} {D : J → Type u'}
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/Induced.lean:49:noncomputable def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
.lake/packages/mathlib/Mathlib/CategoryTheory/WithTerminal/Basic.lean:88:def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
.lake/packages/mathlib/Mathlib/CategoryTheory/WithTerminal/Basic.lean:493:def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
.lake/packages/mathlib/Mathlib/ModelTheory/ElementaryMaps.lean:184:def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/ElementaryMaps.lean:189:theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
.lake/packages/mathlib/Mathlib/ModelTheory/Order.lean:124:def Term.le (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/ShiftedHom.lean:40:noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/ShiftedHom.lean:231:lemma map_zero {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive] :
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Basic.lean:143:def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Basic.lean:151:theorem comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Tactic/FunProp/Theorems.lean:294:  theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:165:def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:180:theorem comp_apply (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:277:def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:295:theorem comp_apply (g : EsakiaHom β γ) (f : EsakiaHom α β) (a : α) : (g.comp f) a = g (f a) := rfl
.lake/packages/mathlib/Mathlib/ModelTheory/LanguageMap.lean:112:def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
.lake/packages/mathlib/Mathlib/ModelTheory/LanguageMap.lean:305:protected def symm : L' ≃ᴸ L :=
.lake/packages/mathlib/Mathlib/ModelTheory/LanguageMap.lean:310:protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/Basic.lean:732:def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/SingleFunctors.lean:131:def comp (α : Hom F G) (β : Hom G H) : Hom F H where
.lake/packages/mathlib/Mathlib/Lean/Expr/Basic.lean:363:def ne?' (e : Expr) : Option (Expr × Expr × Expr) :=
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:74:theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:78:theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:82:theorem Joined.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:212:theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:219:theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:224:theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:262:theorem JoinedIn.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
.lake/packages/mathlib/Mathlib/Topology/Connected/PathConnected.lean:428:theorem IsPathConnected.mul {M : Type*} [Mul M] [TopologicalSpace M] [ContinuousMul M]
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShift.lean:209:instance comp [F.CommShift A] [G.CommShift A] : (F ⋙ G).CommShift A where
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShift.lean:345:lemma add {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShift.lean:430:instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FunctorHom.lean:79:def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean:1007:theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Factorization.lean:94:def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)
.lake/packages/mathlib/Mathlib/ModelTheory/Semantics.lean:720:theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/ReflectsIso/Jointly.lean:76:lemma mono {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Mono ((F i).map f)]
.lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Basic.lean:317:def comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
.lake/packages/mathlib/Mathlib/Topology/ClusterPt.lean:108:theorem ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
.lake/packages/mathlib/Mathlib/Topology/ClusterPt.lean:131:theorem MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F ≤ G) :
.lake/packages/mathlib/Mathlib/Topology/ClusterPt.lean:230:theorem AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Linear/Basic.lean:194:def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
.lake/packages/mathlib/Mathlib/ModelTheory/PartialEquiv.lean:73:def symm (f : M ≃ₚ[L] N) : N ≃ₚ[L] M where
.lake/packages/mathlib/Mathlib/ModelTheory/PartialEquiv.lean:419:def FGEquiv.symm (f : L.FGEquiv M N) : L.FGEquiv N M := ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:673:def pi {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
.lake/packages/mathlib/Mathlib/Topology/Algebra/UniformRing.lean:56:instance mul : Mul (Completion α) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FullyFaithful.lean:222:def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FullyFaithful.lean:280:instance Faithful.comp [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FullyFaithful.lean:353:instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
.lake/packages/mathlib/Mathlib/Topology/ApproximateUnit.lean:51:lemma mono {l l' : Filter α} (hl : l.IsApproximateUnit) (hle : l' ≤ l) [hl' : l'.NeBot] :
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Comma.lean:194:def Hom.comp [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
.lake/packages/mathlib/Mathlib/Topology/Category/TopPair.lean:157:def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
.lake/packages/mathlib/Mathlib/Topology/Category/TopPair.lean:174:noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
.lake/packages/mathlib/Mathlib/Topology/Category/TopPair.lean:192:def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/HomLift.lean:122:instance comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean:81:def comp {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) : 𝒳 ⥤ᵇ 𝒵 where
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean:175:def comp {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) : BasedNatTrans F H where
.lake/packages/mathlib/Mathlib/Topology/Category/Profinite/Basic.lean:262:def pi {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)
.lake/packages/mathlib/Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean:156:lemma comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean:214:def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean:299:instance comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean:290:instance comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ] :
.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean:93:theorem symm (x y : X) : S.toSetoid x y → S.toSetoid y x := S.symm'
.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean:95:theorem trans (x y z : X) : S.toSetoid x y → S.toSetoid y z → S.toSetoid x z := S.trans'
.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean:268:theorem LEComap.comp : LEComap g B C → LEComap f A B → LEComap (g.comp f) A C := by tauto
.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean:271:theorem LEComap.mono (h : LEComap f A B) (hA : A' ≤ A) (hB : B ≤ B') : LEComap f A' B' :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/Pseudoelements.lean:185:theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/Pseudoelements.lean:254:theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean:272:theorem mono' {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulTSupport f) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean:277:theorem mono {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulSupport f) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean:300:theorem comp₂_left (hf : HasCompactMulSupport f)
.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean:389:theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
.lake/packages/mathlib/Mathlib/CategoryTheory/Endomorphism.lean:46:protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩
.lake/packages/mathlib/Mathlib/Lean/Thunk.lean:37:def add [Add α] (a b : Thunk α) : Thunk α := Thunk.mk fun _ => a.get + b.get
.lake/packages/mathlib/Mathlib/CategoryTheory/Square.lean:104:def comp {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃) : Hom sq₁ sq₃ where
.lake/packages/mathlib/Mathlib/Topology/Category/TopCat/Monoidal.lean:134:def symm : I.{u} ⟶ I :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:93:theorem TendstoLocallyUniformlyOn.mono (h : TendstoLocallyUniformlyOn F f p s) (h' : s' ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:156:theorem TendstoLocallyUniformlyOn.comp [TopologicalSpace γ] {t : Set γ}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:165:theorem TendstoLocallyUniformly.comp [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:201:theorem TendstoLocallyUniformlyOn.prodMk [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:214:theorem TendstoLocallyUniformly.prodMk [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:297:theorem TendstoLocallyUniformlyOn.unique [p.NeBot] [T2Space β] {g : α → β}
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:220:lemma mul_apply [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)]
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:230:lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] (g : G)
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Basic.lean:117:def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean:347:protected theorem mono : Monotone (@UniformFun.uniformSpace α γ) := fun _ _ hu =>
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean:835:protected theorem mono ⦃u₁ u₂ : UniformSpace γ⦄ (hu : u₁ ≤ u₂) ⦃𝔖₁ 𝔖₂ : Set (Set α)⦄
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Preserves/Shapes/Zero.lean:53:protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:162:lemma EquicontinuousWithinAt.mono {F : ι → X → α} {x₀ : X} {S T : Set X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:179:lemma EquicontinuousOn.mono {F : ι → X → α} {S T : Set X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:195:lemma UniformEquicontinuousOn.mono {F : ι → β → α} {S T : Set β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:392:theorem EquicontinuousAt.comp {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ → ι) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:396:theorem EquicontinuousWithinAt.comp {F : ι → X → α} {S : Set X} {x₀ : X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:401:protected theorem Set.EquicontinuousAt.mono {H H' : Set <| X → α} {x₀ : X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:405:protected theorem Set.EquicontinuousWithinAt.mono {H H' : Set <| X → α} {S : Set X} {x₀ : X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:410:theorem Equicontinuous.comp {F : ι → X → α} (h : Equicontinuous F) (u : κ → ι) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:414:theorem EquicontinuousOn.comp {F : ι → X → α} {S : Set X} (h : EquicontinuousOn F S) (u : κ → ι) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:417:protected theorem Set.Equicontinuous.mono {H H' : Set <| X → α} (h : H.Equicontinuous)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:421:protected theorem Set.EquicontinuousOn.mono {H H' : Set <| X → α} {S : Set X}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:426:theorem UniformEquicontinuous.comp {F : ι → β → α} (h : UniformEquicontinuous F) (u : κ → ι) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:430:theorem UniformEquicontinuousOn.comp {F : ι → β → α} {S : Set β} (h : UniformEquicontinuousOn F S)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:434:protected theorem Set.UniformEquicontinuous.mono {H H' : Set <| β → α} (h : H.UniformEquicontinuous)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equicontinuity.lean:438:protected theorem Set.UniformEquicontinuousOn.mono {H H' : Set <| β → α} {S : Set β}
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:58:theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:135:instance smul [SMul α Y] : SMul α (LocallyConstant X Y) where
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:143:theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Action/Basic.lean:109:def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:78:theorem Filter.Tendsto.mul {α : Type*} {f g : α → M} {x : Filter α} {a b : M}
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:91:theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:96:theorem ContinuousWithinAt.mul (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:101:theorem ContinuousAt.mul (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:106:theorem ContinuousOn.mul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:132:theorem Filter.Tendsto.const_mul {α : Type*} {f : α → M} {x : Filter α} {a : M}
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:137:theorem Filter.Tendsto.mul_const {α : Type*} {f : α → M} {x : Filter α} {a : M}
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:144:theorem Continuous.mul_const (hf : Continuous f) (b : M) : Continuous (f · * b) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:148:theorem Continuous.const_mul (hf : Continuous f) (b : M) : Continuous (b * f ·) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:152:theorem ContinuousWithinAt.mul_const (hf : ContinuousWithinAt f s x) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:157:theorem ContinuousWithinAt.const_mul (hf : ContinuousWithinAt f s x) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:162:theorem ContinuousAt.mul_const (hf : ContinuousAt f x) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:167:theorem ContinuousAt.const_mul (hf : ContinuousAt f x) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:172:theorem ContinuousOn.mul_const (hf : ContinuousOn f s) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean:177:theorem ContinuousOn.const_mul (hf : ContinuousOn f s) (b : M) :
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:108:protected theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) :
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:113:theorem prodMk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f)
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:118:theorem comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:122:theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g)
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:167:theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
.lake/packages/mathlib/Mathlib/Topology/Path.lean:150:def symm (γ : Path x y) : Path y x where
.lake/packages/mathlib/Mathlib/Topology/Path.lean:277:def trans (γ : Path x y) (γ' : Path y z) : Path x z where
.lake/packages/mathlib/Mathlib/Topology/Path.lean:503:protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
.lake/packages/mathlib/Mathlib/Topology/Path.lean:529:protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:146:theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:152:theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:158:theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:164:theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:173:protected theorem Specializes.mul {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d) : (a * c) ⤳ (b * d) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:177:protected theorem Inseparable.mul {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:182:protected theorem Specializes.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:188:protected theorem Inseparable.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:664:theorem IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:813:theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:825:theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:830:theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:835:theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:840:theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equiv.lean:66:protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equiv.lean:102:protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:33:instance pi : Category.{max w₀ v₁} (∀ i, C i) where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:45:theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:181:def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:188:def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:194:def pi'CompEval {A : Type*} [Category* A] (F : ∀ i, A ⥤ C i) (i : I) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:211:theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:240:def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:246:def pi' {E : Type*} [Category* E] {F G : E ⥤ ∀ i, C i}
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:264:def pi (e : ∀ i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:272:def pi' {E : Type*} [Category* E] {F G : E ⥤ ∀ i, C i}
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:351:def pi (E : ∀ i, C i ≌ D i) : (∀ i, C i) ≌ (∀ i, D i) where
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Flat.lean:93:instance RepresentablyFlat.comp (G : D ⥤ E) [RepresentablyFlat F]
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Flat.lean:146:instance RepresentablyCoflat.comp (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G] :
.lake/packages/mathlib/Mathlib/Topology/Coherent.lean:72:protected theorem mono {T} (hS : IsCoherentWith S) (hT : S ⊆ T) : IsCoherentWith T :=
.lake/packages/mathlib/Mathlib/Topology/IsLocalHomeomorph.lean:118:theorem mono {t : Set X} (hf : IsLocalHomeomorphOn f t) (hst : s ⊆ t) : IsLocalHomeomorphOn f s :=
.lake/packages/mathlib/Mathlib/Topology/IsLocalHomeomorph.lean:153:protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
.lake/packages/mathlib/Mathlib/Topology/IsLocalHomeomorph.lean:242:protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:59:theorem IsUniformInducing.comp {g : β → γ} (hg : IsUniformInducing g) {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:155:theorem IsUniformEmbedding.comp {g : β → γ} (hg : IsUniformEmbedding g) {f : α → β}
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:71:lemma mul_apply (γ₁ γ₂ : ZeroCochain G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i := rfl
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:159:lemma symm {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:165:lemma trans {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
.lake/packages/mathlib/Mathlib/Topology/Order.lean:222:theorem IsOpen.mono (hs : IsOpen[t₂] s) (h : t₁ ≤ t₂) : IsOpen[t₁] s := h s hs
.lake/packages/mathlib/Mathlib/Topology/Order.lean:224:theorem IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ ≤ t₂) : IsClosed[t₁] s :=
.lake/packages/mathlib/Mathlib/Topology/Order.lean:227:theorem closure.mono (h : t₁ ≤ t₂) : closure[t₁] s ⊆ closure[t₂] s :=
.lake/packages/mathlib/Mathlib/Topology/Homeomorph/Defs.lean:79:protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
.lake/packages/mathlib/Mathlib/Topology/Homeomorph/Defs.lean:114:protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
.lake/packages/mathlib/Mathlib/Topology/Homeomorph/Defs.lean:488:lemma comp {g : Y → Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) : IsHomeomorph (g ∘ f) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Grp.lean:161:lemma comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:390:theorem IsOpenMap.restrict {f : X → Y} (hf : IsOpenMap f) {s : Set X} (hs : IsOpen s) :
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:402:theorem IsClosedMap.restrict {f : X → Y} (hf : IsClosedMap f) {s : Set X} (hs : IsClosed s) :
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:518:theorem ContinuousAt.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t) {x : s}
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:540:theorem Continuous.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:558:lemma Topology.IsEmbedding.restrict {f : X → Y}
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:564:lemma Topology.IsOpenEmbedding.restrict {f : X → Y}
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:609:lemma IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : t ⊆ s) : IsDiscrete t :=
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:1359:theorem IsOpen.trans (ht : IsOpen t) (hs : IsOpen s) : IsOpen (t : Set X) := by
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:1364:theorem IsClosed.trans (ht : IsClosed t) (hs : IsClosed s) : IsClosed (t : Set X) := by
.lake/packages/mathlib/Mathlib/Topology/Closure.lean:431:theorem Dense.mono (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:169:theorem TendstoUniformlyOn.mono (h : TendstoUniformlyOn F f p s) (h' : s' ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:224:theorem TendstoUniformlyOnFilter.comp (h : TendstoUniformlyOnFilter F f p p') (g : γ → α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:230:theorem TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ → α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:236:theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ → α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:281:theorem TendstoUniformlyOnFilter.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:288:protected theorem TendstoUniformlyOn.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:295:theorem TendstoUniformly.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:504:theorem UniformCauchySeqOn.mono (hf : UniformCauchySeqOn F p s) (hss' : s' ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:510:theorem UniformCauchySeqOnFilter.comp {γ : Type*} (hf : UniformCauchySeqOnFilter F p p')
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:518:theorem UniformCauchySeqOn.comp {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ → α) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mon.lean:553:def comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mon.lean:1204:lemma mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Basic.lean:529:lemma UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Basic.lean:540:lemma UniformContinuousOn.comp {g : β → γ} {t : Set β} (hg : UniformContinuousOn g t)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Basic.lean:829:theorem UniformContinuous.prodMk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean:223:def add (E : PreZeroHypercover.{w} S) {T : C} (f : T ⟶ S) : PreZeroHypercover.{w} S :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean:283:def Hom.comp (f : E.Hom F) (g : F.Hom G) : E.Hom G where
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean:708:def add (E : ZeroHypercover.{w} J S) {T : C} (f : T ⟶ S)
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean:157:theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : eVariationOn f t ≤ eVariationOn f s := by
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean:955:protected theorem add {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/One.lean:355:def Hom.comp (f : E.Hom F) (g : F.Hom G) : E.Hom G where
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:81:theorem LipschitzOnWith.mono (hf : LipschitzOnWith K f t) (h : s ⊆ t) : LipschitzOnWith K f s :=
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:84:lemma LocallyLipschitzOn.mono (hf : LocallyLipschitzOn t f) (h : s ⊆ t) : LocallyLipschitzOn s f :=
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:224:protected theorem restrict (hf : LipschitzWith K f) (s : Set α) : LipschitzWith K (s.restrict f) :=
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:228:protected theorem comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f)
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:246:protected theorem prodMk {f : α → β} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) {g : α → γ} {Kg : ℝ≥0}
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:328:protected theorem comp {g : β → γ} {t : Set β} {Kg : ℝ≥0} (hg : LipschitzOnWith Kg g t)
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:333:protected theorem prodMk {g : α → γ} {Kf Kg : ℝ≥0} (hf : LipschitzOnWith Kf f s)
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:376:protected lemma comp {f : β → γ} {g : α → β}
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:387:protected lemma prodMk {f : α → β} (hf : LocallyLipschitz f) {g : α → γ} (hg : LocallyLipschitz g) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:109:theorem SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:135:theorem SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:176:lemma SemicontinuousWithinAt.comp (h : SemicontinuousWithinAt r t (g x))
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:181:lemma SemicontinuousOn.comp {r : α → β → Prop} {γ : Type*}
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:188:lemma SemicontinuousAt.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:193:lemma Semicontinuous.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:303:theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:327:theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:369:theorem LowerSemicontinuousWithinAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:375:theorem LowerSemicontinuousAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:380:theorem LowerSemicontinuousOn.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:385:theorem LowerSemicontinuous.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:399:theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:425:theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:464:theorem UpperSemicontinuousWithinAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:470:theorem UpperSemicontinuousAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:475:theorem UpperSemicontinuousOn.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:480:theorem UpperSemicontinuous.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:649:theorem LowerHemicontinuousWithinAt.mono (h : LowerHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:673:theorem LowerHemicontinuousOn.mono (h : LowerHemicontinuousOn f s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:750:theorem LowerHemicontinuousWithinAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:756:theorem LowerHemicontinuousAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:761:theorem LowerHemicontinuousOn.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:766:theorem LowerHemicontinuous.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:778:theorem UpperHemicontinuousWithinAt.mono (h : UpperHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:806:theorem UpperHemicontinuousOn.mono (h : UpperHemicontinuousOn f s) (hst : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:879:theorem UpperHemicontinuousWithinAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:886:theorem UpperHemicontinuousAt.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:891:theorem UpperHemicontinuousOn.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean:896:theorem UpperHemicontinuous.comp
.lake/packages/mathlib/Mathlib/Tactic/NormNum/Basic.lean:247:def Result.add {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
.lake/packages/mathlib/Mathlib/Tactic/NormNum/Basic.lean:388:def Result.sub {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
.lake/packages/mathlib/Mathlib/Tactic/NormNum/Basic.lean:486:def Result.mul {u : Level} {α : Q(Type u)} {a b : Q($α)} (ra : Result q($a)) (rb : Result q($b))
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:418:alias LowerSemicontinuous.comp_continuous := LowerSemicontinuous.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:433:theorem LowerSemicontinuousWithinAt.add' {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:495:theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:505:theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:514:theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:525:theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:533:theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:540:theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:547:theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1044:alias UpperSemicontinuous.comp_continuous := UpperSemicontinuous.comp
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1059:theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1068:theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1078:theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1087:theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1098:theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1106:theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1113:theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1120:theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f)
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Comon_.lean:171:def comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Pi.lean:100:lemma Cauchy.pi [Nonempty ι] {l : ∀ i, Filter (α i)} (hl : ∀ i, Cauchy (l i)) :
.lake/packages/mathlib/Mathlib/Topology/Spectral/Hom.lean:59:theorem IsSpectralMap.comp {f : β → γ} {g : α → β} (hf : IsSpectralMap f) (hg : IsSpectralMap g) :
.lake/packages/mathlib/Mathlib/Topology/Spectral/Hom.lean:159:def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
.lake/packages/mathlib/Mathlib/Topology/Spectral/Hom.lean:167:theorem comp_apply (f : SpectralMap β γ) (g : SpectralMap α β) (a : α) : (f.comp g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Tactic/NormNum/PowMod.lean:48:theorem IsNatPowModT.trans (h1 : IsNatPowModT p a b m c)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:81:theorem restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean:240:abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean:513:noncomputable abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean:71:theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean:74:theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g ≤ f) : Cauchy g :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean:245:theorem CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ → α} {v : γ → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean:547:theorem Filter.TotallyBounded.mono {f g : Filter α} (h : f ≤ g) (hg : g.TotallyBounded) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Images.lean:745:instance HasImageMap.comp {f g h : Arrow C} [HasImage f.hom] [HasImage g.hom] [HasImage h.hom]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/BundledFun.lean:66:protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/WideEqualizers.lean:90:def WalkingParallelFamily.Hom.comp :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:106:theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:131:protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:259:theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:287:lemma mono {C' : ℝ≥0} (hf : HolderWith C r f) (h : C ≤ C') :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:406:lemma add (hf : HolderWith C r f) (hg : HolderWith C' r g) :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:413:lemma smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y] (a : α)
.lake/packages/mathlib/Mathlib/Tactic/NormNum/Pow.lean:46:theorem IsNatPowT.trans {p : Prop} {b' c' : ℕ} (h1 : IsNatPowT p a b c)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:163:theorem TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:185:theorem TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:195:theorem TendstoLocallyUniformly.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:205:theorem TendstoLocallyUniformly.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:215:theorem TendstoLocallyUniformlyOn.smul₀ {X ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:225:theorem TendstoLocallyUniformlyOn.mul₀ {X M ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:234:theorem TendstoLocallyUniformly.smul₀ {X ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Algebra.lean:244:theorem TendstoLocallyUniformly.mul₀ {X M ι : Type*} [TopologicalSpace X]
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Multiequalizer.lean:127:def Hom.comp : ∀ {A B C : WalkingMulticospan J} (_ : Hom A B) (_ : Hom B C), Hom A C
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Multiequalizer.lean:200:def Hom.comp : ∀ {A B C : WalkingMultispan J} (_ : Hom A B) (_ : Hom B C), Hom A C
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Ultra/Constructions.lean:76:instance IsUltraUniformity.pi {ι : Type*} {X : ι → Type*} [U : Π i, UniformSpace (X i)]
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mod.lean:175:def comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/IsSheafFor.lean:110:def FamilyOfElements.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/IsSheafFor.lean:194:theorem FamilyOfElements.Compatible.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂)
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Functor.lean:221:instance comp : (F ⋙ G).LaxMonoidal where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Functor.lean:343:instance comp : (F ⋙ G).OplaxMonoidal where
.lake/packages/mathlib/Mathlib/Topology/LocallyFinsupp.lean:566:noncomputable def restrict [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
.lake/packages/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean:573:protected theorem Tendsto.mul {f : Filter α} {ma : α → EReal} {mb : α → EReal} {a b : EReal}
.lake/packages/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean:579:protected theorem Tendsto.const_mul {f : Filter α} {m : α → EReal} {a b : EReal}
.lake/packages/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean:585:protected theorem Tendsto.mul_const {f : Filter α} {m : α → EReal} {a b : EReal}
.lake/packages/mathlib/Mathlib/Topology/Compactness/CompactSystem.lean:70:theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S ⊆ T) :
.lake/packages/mathlib/Mathlib/Topology/Instances/TrivSqZeroExt.lean:73:theorem IsEmbedding.inr [Zero R] : IsEmbedding (inr : M → tsze R M) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Types/Pushouts.lean:61:def inr : X₂ ⟶ Pushout f g := ↾fun x => Quot.mk _ (Sum.inr x)
.lake/packages/mathlib/Mathlib/Tactic/FieldSimp/Lemmas.lean:410:def Sign.mul (iM : Q(CommGroupWithZero $M)) (y₁ y₂ : Q($M)) (g₁ g₂ : Sign M) :
.lake/packages/mathlib/Mathlib/Tactic/FieldSimp/Lemmas.lean:464:def Sign.pow (iM : Q(CommGroupWithZero $M)) (y : Q($M)) (g : Sign M) (s : ℕ) :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/DilationEquiv.lean:74:def symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/DilationEquiv.lean:108:def trans (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z) : X ≃ᵈ Z where
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean:367:theorem Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul G X] {s : Set X}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:310:protected theorem Tendsto.sub {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:338:protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:355:protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:360:protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:446:protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:481:protected theorem Tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:115:protected lemma inr [AddZeroClass α] [AddZeroClass β] : Isometry (AddMonoidHom.inr α β) := by
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:121:theorem comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:440:protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:449:protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:586:theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean:727:def prod.inr : Y ⟶ X ⨯ Y :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/CoverPreserving.lean:66:theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean:114:theorem comp {Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean:121:theorem restrict (hf : AntilipschitzWith K f) (s : Set α) : AntilipschitzWith K (s.restrict f) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Ring.lean:129:instance IsRingHom.comp {R₁ R₂ R₃ : C}
.lake/packages/mathlib/Mathlib/Topology/Covering/Basic.lean:226:theorem mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : t ⊆ s) : IsCoveringMapOn f t :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/Cospan.lean:90:abbrev Hom.inr : right ⟶ one :=
.lake/packages/mathlib/Mathlib/Topology/DiscreteSubset.lean:227:lemma Filter.codiscreteWithin.mono {U₁ U : Set X} (hU : U₁ ⊆ U) :
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:106:theorem continuous_id : Continuous (id : X → X) :=
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:111:theorem continuous_id' : Continuous (fun (x : X) => x) := continuous_id
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:113:theorem Continuous.comp {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:119:theorem Continuous.comp' {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:131:theorem ContinuousAt.comp' {g : Y → Z} {x : X} (hg : ContinuousAt g (f x))
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:161:theorem continuous_const : Continuous fun _ : X => y :=
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:307:theorem DenseRange.comp {g : Y → Z} {f : α → Y} (hg : DenseRange g) (hf : DenseRange f)
.lake/packages/mathlib/Mathlib/Topology/PartitionOfUnity.lean:366:theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.IsSubordinate U)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean:72:lemma RegularMono.mono {f : X ⟶ Y} (h : RegularMono f) : Mono f :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean:104:theorem symm (h : AreSeparated s t) : AreSeparated t s :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean:126:theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HolderNorm.lean:253:lemma MemHolder.comp {r s : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HolderNorm.lean:268:lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HolderNorm.lean:271:lemma MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
.lake/packages/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean:233:protected noncomputable def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
.lake/packages/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean:677:protected noncomputable def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:382:def comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y ⊗ (ihom y).obj z ⟶ (ihom x).obj z :=
.lake/packages/mathlib/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean:73:lemma ContinuousGeneratedBy.comp {g : Y → Z} (hg : ContinuousGeneratedBy X g)
.lake/packages/mathlib/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean:110:def ContinuousMapGeneratedBy.comp
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/CatCospanTransform.lean:85:def comp
.lake/packages/mathlib/Mathlib/Topology/GDelta/Basic.lean:207:lemma IsNowhereDense.mono {s t : Set X} (ht : t ⊆ s) (hs : IsNowhereDense s) : IsNowhereDense t :=
.lake/packages/mathlib/Mathlib/Topology/GDelta/Basic.lean:267:lemma IsMeagre.mono {s t : Set X} (hts : t ⊆ s) (hs : IsMeagre s) : IsMeagre t :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Reflexive.lean:211:def Hom.comp :
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean:58:instance comp (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ'] :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Dilation.lean:288:def comp (g : β →ᵈ γ) (f : α →ᵈ β) : α →ᵈ γ where
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Dilation.lean:301:theorem comp_apply (g : β →ᵈ γ) (f : α →ᵈ β) (x : α) : (g.comp f : α → γ) x = g (f x) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean:315:abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
.lake/packages/mathlib/Mathlib/Topology/Separation/Basic.lean:277:theorem Specializes.symm (h : x ⤳ y) : y ⤳ x := specializes_symmetric h
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/Equifibered.lean:55:theorem Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/Equifibered.lean:101:theorem Coequifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:122:abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
.lake/packages/mathlib/Mathlib/Topology/Separation/SeparatedNhds.lean:110:theorem HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
.lake/packages/mathlib/Mathlib/Topology/Separation/SeparatedNhds.lean:125:theorem symm : SeparatedNhds s t → SeparatedNhds t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
.lake/packages/mathlib/Mathlib/Topology/Separation/SeparatedNhds.lean:153:theorem mono (h : SeparatedNhds s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : SeparatedNhds s₁ t₁ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:89:lemma mono (h : IsZero X) {Y : C} (f : X ⟶ Y) : Mono f where
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:228:theorem ContinuousWithinAt.mono (h : ContinuousWithinAt f t x)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:310:theorem ContinuousOn.mono (hf : ContinuousOn f s) (h : t ⊆ s) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:444:theorem ContinuousWithinAt.comp {g : β → γ} {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:495:theorem ContinuousOn.comp {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:501:theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:523:theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:532:theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:538:theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ → δ} {g : α → β}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:578:theorem ContinuousWithinAt.prodMk {f : α → β} {g : α → γ} {s : Set α} {x : α}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:584:theorem ContinuousOn.prodMk {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/FunctorToTypes.lean:127:def prodMk {a : C} (x : F.obj a) (y : G.obj a) : (F ⨯ G).obj a :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/FunctorToTypes.lean:184:def coprod.inr : G ⟶ coprod F G where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Bimod.lean:124:def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean:355:lemma kernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean:876:lemma cokernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean:425:abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean:82:def WalkingParallelPairHom.comp :
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean:457:lemma Fork.IsLimit.mono {s : Fork f g} (hs : IsLimit s) : Mono s.ι where
.lake/packages/mathlib/Mathlib/CategoryTheory/Sigma/Basic.lean:46:def comp : ∀ {X Y Z : Σ i, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Majorized.lean:89:theorem smul (h : Majorized f b exp) {c : ℝ} :
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Majorized.lean:95:theorem add {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Majorized.lean:104:theorem mul {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Corecursion.lean:196:theorem FriendlyOperation.comp {op op' : Seq α → Seq α}
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Corecursion.lean:206:theorem FriendlyOperationClass.comp (F : γ → Seq α → Seq α) (g : γ' → γ)
.lake/packages/mathlib/Mathlib/Tactic/Module.lean:314:def sub (iR : Q(Ring $R)) : qNF R M → qNF R M → qNF R M
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Monomial/Basic.lean:88:noncomputable def mul (m1 m2 : UnitMonomial) : UnitMonomial :=
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Monomial/Basic.lean:181:noncomputable def mul (t1 t2 : Monomial) : Monomial :=
.lake/packages/mathlib/Mathlib/Tactic/ComputeAsymptotics/Multiseries/Monomial/Basic.lean:185:noncomputable def smul (t : Monomial) (c : ℝ) : Monomial :=
.lake/packages/mathlib/Mathlib/Tactic/Translate/ToAdditive.lean:40:theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y
.lake/packages/mathlib/Mathlib/Tactic/Translate/ToAdditive.lean:58:theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := CommSemigroup.mul_comm
```

</details>
