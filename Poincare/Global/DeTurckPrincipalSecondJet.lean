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

/-- Constant-family coordinate evolution expanded through the actual
Christoffel field and its inverse-metric contraction. -/
theorem evolution_eq_coordinate_expression
    (g bg : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1)
    (v w : E) :
    let G := CovariantDerivative.chartMetric g.inner anchor
    let Γ := GeodesicTransport.chartChristoffelField g anchor
    let W := anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0
    let b := Module.finBasis ℝ E
    deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z v w =
      -2 * (∑ i, b.coord i
        ((fderiv ℝ Γ z (b i)) v w - (fderiv ℝ Γ z v) (b i) w +
          Γ z (b i) (Γ z v w) - Γ z v (Γ z (b i) w))) +
      fderiv ℝ G z (W z) v w +
      G z (fderiv ℝ W z v) w + G z v (fderiv ℝ W z w) := by
  dsimp only
  have hz' := (extChartAt (closedSmoothModelWithCorners 3) anchor).right_inv hz
  have hLie := deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
    (fun _ => g) bg anchor 0
    ((extChartAt (closedSmoothModelWithCorners 3) anchor).map_target hz)
    (by simpa only [hz'] using hcut)
    (deTurckVectorFieldRegularAt_holds (fun _ => g) bg 0) v w
  simp only [hz'] at hLie
  simp only [deTurckChartMetricEvolutionBilin, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hLie, ← anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
    (fun _ => g) anchor 0 hz hcut,
    fieldDerivative_eq_contractionDerivative g bg anchor z hz hcut]
  simp only [deTurckChartMetricAdvectionAt,
    ← anchorChartDeTurckContractionFlow_eq_chartCoordinateTangentField_zone
      (fun _ => g) bg anchor 0 hz hcut]
  simp only [anchorChartRicciEntryFlow, anchorChartCurvatureFlow,
    anchorChartChristoffelFieldFlow, chartCurvatureOf]
  simp only [LinearMap.coe_toContinuousLinearMap', add_assoc]

end Manifold
end Poincare.DeTurckPrincipalSecondJet
