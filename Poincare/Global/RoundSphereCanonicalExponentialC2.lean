import Poincare.Global.RoundSphereCanonicalExponential
import Poincare.Global.UniformAnchoredSecondVariation

/-!
# Anchor-uniform C2 regularity for the normalized round-sphere exponential

The normalized exponential chart is the same reference chart map at every
round-sphere anchor.  The reference map's derivative and second-variation
estimates therefore give genuinely anchor-independent regularity radii.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace RoundSphereCanonicalExponential

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- One positive ball supplies the canonical Fréchet derivative of the
charted normalized exponential at every point and every target anchor. -/
theorem exists_uniform_chart_expAt_hasFDerivAt_on_smallBall :
    ∃ rho > (0 : ℝ), ∀ (p : RoundSphere3) (v : E),
      v ∈ ball (0 : E) rho →
        HasFDerivAt
          (fun w : E ↦ extChartAt I p (expAt p w))
          (fderiv ℝ (coordinateLocalHomeomorph : E → E) v) v := by
  rcases
      UniformAnchoredSecondVariation.exists_expAtChart_hasFDerivAt_on_smallBall
        roundSphereMetric3 referenceAnchor with
    ⟨rho, hrho, hderiv⟩
  refine ⟨rho, hrho, ?_⟩
  intro p v hv
  have h := hderiv v hv
  have hfun :
      (fun w : E ↦ extChartAt I p (expAt p w)) =
        (coordinateLocalHomeomorph : E → E) := by
    funext w
    exact extChartAt_expAt p w
  rw [hfun]
  simpa [coordinateLocalHomeomorph] using h

/-- The canonical derivative field is `C¹` on one ball uniformly over all
round-sphere target anchors. -/
theorem exists_uniform_chart_expAt_fderiv_contDiffAt_one_on_smallBall :
    ∃ rho > (0 : ℝ), ∀ (p : RoundSphere3) (v : E),
      v ∈ ball (0 : E) rho →
        ContDiffAt ℝ 1
          (fun w : E ↦
            fderiv ℝ (fun q : E ↦ extChartAt I p (expAt p q)) w) v := by
  rcases
      UniformAnchoredSecondVariation.exists_expAtChart_fderiv_contDiffAt_one_on_smallBall
        roundSphereMetric3 referenceAnchor with
    ⟨rho, hrho, hcont⟩
  refine ⟨rho, hrho, ?_⟩
  intro p v hv
  have h := hcont v hv
  have hfield :
      (fun w : E ↦
        fderiv ℝ (fun q : E ↦ extChartAt I p (expAt p q)) w) =
      (fun w : E ↦
        fderiv ℝ (coordinateLocalHomeomorph : E → E) w) := by
    funext w
    rw [fderiv_chart_expAt_eq_coordinateLocalHomeomorph p]
  rw [hfield]
  simpa [coordinateLocalHomeomorph] using h

/-- The normalized exponential chart is `C²` on one common ball for every
round-sphere target anchor. -/
theorem exists_uniform_chart_expAt_contDiffAt_two_on_smallBall :
    ∃ rho > (0 : ℝ), ∀ (p : RoundSphere3) (v : E),
      v ∈ ball (0 : E) rho →
        ContDiffAt ℝ 2 (fun w : E ↦ extChartAt I p (expAt p w)) v := by
  rcases
      UniformAnchoredSecondVariation.exists_expAtChart_contDiffAt_two_on_smallBall
        roundSphereMetric3 referenceAnchor with
    ⟨rho, hrho, hcont⟩
  refine ⟨rho, hrho, ?_⟩
  intro p v hv
  have h := hcont v hv
  have hfun :
      (fun w : E ↦ extChartAt I p (expAt p w)) =
        (coordinateLocalHomeomorph : E → E) := by
    funext w
    exact extChartAt_expAt p w
  rw [hfun]
  simpa [coordinateLocalHomeomorph] using h

end RoundSphereCanonicalExponential
end Poincare
