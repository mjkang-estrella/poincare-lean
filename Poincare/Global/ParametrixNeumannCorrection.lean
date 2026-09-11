import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Correction of a bounded parametrix

Step L7 of the parabolic route (`harness/reports/parabolic-schauder-decomposition-survey_done.md`,
section 3.2 and Appendix E): a bounded right parametrix `P` with error `R` of norm
less than one corrects to an exact right inverse `S = P ∘ (Id - R)⁻¹` by the
Neumann series.  Only completeness of the forcing space is used.
-/

set_option autoImplicit false
noncomputable section
namespace Poincare.ParametrixNeumannCorrection

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The corrected right inverse of a parametrix with small error. -/
def correctedInverse (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y) (hR : ‖R‖ < 1) : Y →L[ℝ] X :=
  P.comp ((↑((Units.oneSub R hR)⁻¹)) : Y →L[ℝ] Y)

/-- A bounded parametrix `P` with `L ∘ P = Id - R` and `‖R‖ < 1` corrects to an
exact right inverse of `L`. -/
theorem comp_correctedInverse (L : X →L[ℝ] Y) (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y)
    (hLP : L.comp P = ContinuousLinearMap.id ℝ Y - R) (hR : ‖R‖ < 1) :
    L.comp (correctedInverse P R hR) = ContinuousLinearMap.id ℝ Y := by
  unfold correctedInverse
  rw [← ContinuousLinearMap.comp_assoc, hLP]
  change (Units.oneSub R hR).val * ↑(Units.oneSub R hR)⁻¹ = 1
  exact (Units.oneSub R hR).val_inv

/-- Existence form of the corrected right inverse. -/
theorem exists_right_inverse (L : X →L[ℝ] Y) (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y)
    (hLP : L.comp P = ContinuousLinearMap.id ℝ Y - R) (hR : ‖R‖ < 1) :
    ∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y :=
  ⟨correctedInverse P R hR, comp_correctedInverse L P R hLP hR⟩

end Poincare.ParametrixNeumannCorrection
