import Poincare.Global.ParabolicCutoffCommutator

/-!
# Actual Hessian carrier contraction

Two fixed bounded bilinear composition maps substitute the derivative field
in the two arguments of a bilinear carrier. The resulting operator is linear
in the tensor carrier and has a bound quadratic in the derivative field's
original Hölder norm. This supplies the Hessian term of the nonlinear Graph
pullback toward Hamilton flow input existence.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set

namespace Poincare.ParabolicHessianCarrierPullback

open ParabolicHolder ParabolicCutoffCommutator
local notation "E" => ClosedSmoothModel 3
local notation "End" => E →L[ℝ] E
local notation "Cov" => E →L[ℝ] ℝ
local notation "Hess" => E →L[ℝ] E →L[ℝ] ℝ

local instance covectorNormedGroup : NormedAddCommGroup Cov := inferInstance
local instance covectorNormedSpace : NormedSpace ℝ Cov := inferInstance
local instance hessianNormedGroup : NormedAddCommGroup Hess := inferInstance
local instance hessianNormedSpace : NormedSpace ℝ Hess :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }

/-- Construct genuine Hessian carrier substitution with one constant before
the exponent, time interval and actual derivative carrier are chosen. -/
theorem exists_hessian_carrier_pullback :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α T : ℝ) (dF : Y («E» := E) α T End),
      letI : NormedSpace ℝ (Y («E» := E) α T Hess) :=
        Submodule.normedSpace (holderSubmodule («E» := E) (F := Hess) α T)
      ∃ P : Y («E» := E) α T Hess →L[ℝ] Y («E» := E) α T Hess,
        ‖P‖ ≤ C * ‖dF‖ ^ 2 ∧
          ∀ B p (v w : E), P B p v w = B p (dF p v) (dF p w) := by
  let leftSlot : End →L[ℝ] Hess →L[ℝ] Hess :=
    (ContinuousLinearMap.compL ℝ E E Cov).flip
  let covectorSubstitution : End →L[ℝ] Cov →L[ℝ] Cov :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip
  let rightSlot : End →L[ℝ] Hess →L[ℝ] Hess :=
    (ContinuousLinearMap.compL ℝ E Cov Cov).comp covectorSubstitution
  let C : ℝ := 9 * ‖rightSlot‖ * ‖leftSlot‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro α T dF
  letI : NormedSpace ℝ (Y («E» := E) α T Hess) :=
    Submodule.normedSpace (holderSubmodule («E» := E) (F := Hess) α T)
  let Plinear : Y («E» := E) α T Hess →ₗ[ℝ] Y («E» := E) α T Hess := {
    toFun := fun B ↦ bilinearY rightSlot dF (bilinearY leftSlot dF B)
    map_add' := by
      intro B G
      apply ParabolicHolder.ext
      intro p _
      change rightSlot (dF p) (leftSlot (dF p) ((B + G) p)) =
        rightSlot (dF p) (leftSlot (dF p) (B p)) +
          rightSlot (dF p) (leftSlot (dF p) (G p))
      simp only [ParabolicHolder.add_apply, map_add]
    map_smul' := by
      intro c B
      apply ParabolicHolder.ext
      intro p _
      change rightSlot (dF p) (leftSlot (dF p) ((c • B) p)) =
        c • rightSlot (dF p) (leftSlot (dF p) (B p))
      simp only [ParabolicHolder.smul_apply, map_smul] }
  have hbound : ∀ B, ‖Plinear B‖ ≤ (C * ‖dF‖ ^ 2) * ‖B‖ := by
    intro B
    calc
      ‖Plinear B‖ = ‖bilinearY rightSlot dF (bilinearY leftSlot dF B)‖ := rfl
      _ ≤ 3 * ‖rightSlot‖ * ‖dF‖ * ‖bilinearY leftSlot dF B‖ :=
        norm_bilinearY_le rightSlot dF (bilinearY leftSlot dF B)
      _ ≤ 3 * ‖rightSlot‖ * ‖dF‖ * (3 * ‖leftSlot‖ * ‖dF‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_left (norm_bilinearY_le leftSlot dF B) (by positivity)
      _ = (C * ‖dF‖ ^ 2) * ‖B‖ := by dsimp only [C]; ring
  refine ⟨Plinear.mkContinuous (C * ‖dF‖ ^ 2) hbound,
    Plinear.mkContinuous_norm_le (mul_nonneg hC (sq_nonneg ‖dF‖)) hbound, ?_⟩
  intro B p v w
  rfl

end Poincare.ParabolicHessianCarrierPullback
