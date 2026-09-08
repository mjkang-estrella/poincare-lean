import Poincare.Global.DeTurckBUCCoefficientIdentification
import Poincare.Global.DeTurckGaugedFlowClosure
import Poincare.Global.DeTurckCoordinateJointRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace Poincare.DeTurckPrincipalSecondJet

abbrev E := ClosedSmoothModel 3
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
abbrev Jet1 := E →L[ℝ] Bilin

abbrev basis3 (i : Fin 3) : E := EuclideanSpace.basisFun (Fin 3) ℝ i

def inverseEntries (G : Bilin) : Matrix (Fin 3) (Fin 3) ℝ :=
  (fun i j => G (basis3 i) (basis3 j))⁻¹

def spatialPrincipal (G : E → Bilin) (z v w : E) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    inverseEntries (G z) i j *
      fderiv ℝ (fderiv ℝ G) z (basis3 i) (basis3 j) v w

section Manifold
universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

open DeTurckCoordinateJointRegularity

/-- The ordinary spatial derivative of the actual field is the derivative
of the explicit inverse-metric Christoffel contraction throughout this zone. -/
theorem fieldDerivative_eq_contractionDerivative
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) :
    deTurckChartFieldDerivativeAt (fun _ => g) bg anchor 0 z =
      fderiv ℝ (anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0) z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(isOpen_extChartAt_target anchor).mem_nhds hz,
    eventually_eventually_nhds.mpr hcut] with y hy hcy
  exact (anchorChartDeTurckContractionFlow_eq_chartCoordinateTangentField_zone
    (fun _ => g) bg anchor 0 hy hcy).symm

end Manifold
end Poincare.DeTurckPrincipalSecondJet
