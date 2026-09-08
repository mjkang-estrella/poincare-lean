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

/-- Right composition propagates any initial operator through the same
fundamental solution, giving a full augmented-state flow. -/
theorem operatorAugmentedFlow_hasDerivWithinAt
    {F : X → X} {α : ℝ → X} {Φ : ℝ → X →L[ℝ] X}
    {J : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (F (α t)) J t)
    (hΦ : HasDerivWithinAt Φ ((fderiv ℝ F (α t)).comp (Φ t)) J t)
    (Y : X →L[ℝ] X) :
    HasDerivWithinAt (fun s => (α s, (Φ s).comp Y))
      (operatorAugmentedField F (α t, (Φ t).comp Y)) J t := by
  simpa [operatorAugmentedField, ContinuousLinearMap.comp_assoc] using
    hα.prodMk (hΦ.clm_comp (hasDerivWithinAt_const t J Y))

universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

/-- The fixed-chart operator system is C2. The vector-valued augmented
regularity theorem supplies regularity of each evaluation of the operator. -/
theorem chart_operatorAugmentedField_contDiff_two
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ContDiff ℝ 2 (operatorAugmentedField
      (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀))) := by
  let Γ := GeodesicTransport.chartChristoffelField g x₀
  have haug := (GeodesicTransport.exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
      g x₀ (0 : (E × E) × (E × E)) 0).1
  have hlin : ContDiff ℝ 2 (linearizedGeodesicFlowOperator Γ) := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    simpa only [augmentedGeodesicFlowField, Function.comp_def] using
      (haug.comp (contDiff_id.prodMk (contDiff_const (c := v)))).snd
  exact ((GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two
    g x₀).comp contDiff_fst).prodMk
      ((hlin.comp contDiff_fst).clm_comp contDiff_snd)

end Poincare.FixedChartPatchSecondVariation
