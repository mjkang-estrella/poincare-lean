import Poincare.Global.FixedChartUniformEndpointReanchoring

/-!
# Operator-valued second variation for a retained fixed-chart patch

The augmented state retains the whole initial-state derivative, including
position and velocity directions. All time and state restrictions below
are explicit; a shorter interval does not replace the patch endpoint time.
-/

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Filter Function Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare.FixedChartPatchSecondVariation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The state equation together with its operator-valued first variation. -/
def operatorAugmentedField (F : X → X) (y : X × (X →L[ℝ] X)) :
    X × (X →L[ℝ] X) :=
  (F y.1, (fderiv ℝ F y.1).comp y.2)

/-- C2 regularity of the base field gives C1 regularity of the operator system. -/
theorem operatorAugmentedField_contDiff_one {F : X → X}
    (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (operatorAugmentedField F) := by
  exact ((hF.of_le (by norm_num)).comp contDiff_fst).prodMk
    (((hF.fderiv_right (m := 1) (by norm_num)).comp contDiff_fst).clm_comp contDiff_snd)

end Poincare.FixedChartPatchSecondVariation
