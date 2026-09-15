import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

end Poincare.NearFrozenParabolicRightInverse
