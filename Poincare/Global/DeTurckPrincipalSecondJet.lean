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
/-- Formal second-derivative terms of the coordinate Ricci trace, before
simplification by the symmetries of the metric second derivative. -/
def ricciSecondJet (A : Matrix (Fin 3) (Fin 3) ℝ)
    (H : E → E → E → E → ℝ) (v w : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
    A i j * (H (basis3 i) v w (basis3 j) +
      H (basis3 i) w v (basis3 j) - H (basis3 i) (basis3 j) v w -
      H v (basis3 i) w (basis3 j) - H v w (basis3 i) (basis3 j) +
      H v (basis3 j) (basis3 i) w)

/-- Formal second-derivative terms in the two Lie derivative slots of the
contracted Christoffel field. -/
def lieSecondJet (A : Matrix (Fin 3) (Fin 3) ℝ)
    (H : E → E → E → E → ℝ) (v w : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3,
    A i j * (H v (basis3 i) (basis3 j) w +
      H v (basis3 j) (basis3 i) w - H v w (basis3 i) (basis3 j) +
      H w (basis3 i) (basis3 j) v + H w (basis3 j) (basis3 i) v -
      H w v (basis3 i) (basis3 j))

/-- Cancellation of the formal second-order terms. Their identification
with the geometric derivatives in `evolution_eq_coordinate_expression`
is a separate obligation. -/
theorem secondJet_cancellation (A : Matrix (Fin 3) (Fin 3) ℝ)
    (H : E → E → E → E → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (hD : ∀ a b v w, H a b v w = H b a v w)
    (hS : ∀ a b v w, H a b v w = H a b w v) (v w : E) :
    -2 * ricciSecondJet A H v w + lieSecondJet A H v w =
      ∑ i : Fin 3, ∑ j : Fin 3, A i j * H (basis3 i) (basis3 j) v w := by
  have hswap (p q : E) :
      (∑ i : Fin 3, ∑ j : Fin 3, A i j * H p (basis3 i) (basis3 j) q) =
      ∑ i : Fin 3, ∑ j : Fin 3, A i j * H p (basis3 j) (basis3 i) q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, A i j *
        (H (basis3 i) (basis3 j) v w + (1 / 2 : ℝ) *
          (H v (basis3 i) (basis3 j) w - H v (basis3 j) (basis3 i) w -
           H w (basis3 i) (basis3 j) v + H w (basis3 j) (basis3 i) v)) := by
      simp only [ricciSecondJet, lieSecondJet, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hD (basis3 i) v, hD (basis3 i) w, hD w v,
        hS v (basis3 i) w, hS w (basis3 i) v]
      ring
    _ = _ := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [show ∀ i j (r : ℝ), A i j * ((1 / 2 : ℝ) * r) =
        (1 / 2 : ℝ) * (A i j * r) by intros; ring]
      simp only [← Finset.mul_sum]
      rw [hswap v w, hswap w v]
      ring

end Poincare.DeTurckPrincipalSecondJet
