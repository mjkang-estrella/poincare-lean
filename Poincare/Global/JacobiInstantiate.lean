import Poincare.Global.JacobiConstantCurvature
import Poincare.Global.ChartCurvatureBridge6
import Poincare.Global.GaussLemmaIntegrated

/-!
# Constant-curvature Jacobi instantiation, anchor slice

This file instantiates the chart curvature contraction for a general
constant-curvature-one closed metric at the anchor chart point.

The full oscillator statement along an interval still needs an additional
coordinate/covariant second-derivative bookkeeping theorem away from the
anchor.  The proved statements below isolate the non-vacuous curvature input
needed by that step.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

omit [T2Space M] in
/-- At the anchor, the chart metric evaluated on transported constant fields
is the original manifold metric. -/
theorem chartMetric_anchor_eq_inner
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p q : TM3 x₀) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q =
      g.inner x₀ p q := by
  let z₀ : E3 := extChartAt I3 x₀ x₀
  have htarget : z₀ ∈ (extChartAt I3 x₀).target := by
    simp [z₀]
  have hp :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend E3 p) z₀ = p := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := 3) (M := M) (x := x₀) (y := x₀)
        (mem_extChartAt_source (I := I3) x₀) p)
  have hq :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend E3 q) z₀ = q := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := 3) (M := M) (x := x₀) (y := x₀)
        (mem_extChartAt_source (I := I3) x₀) q)
  have hmetric :=
    CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
      (g := g.inner) (x₀ := x₀)
      (Y := extend E3 p) (Z := extend E3 q) (hz := htarget)
  have hsymm : (extChartAt I3 x₀).symm z₀ = x₀ := by
    simp [z₀]
  rw [hsymm] at hmetric
  calc
    CovariantDerivative.chartMetric g.inner x₀ z₀ p q =
        CovariantDerivative.chartMetric g.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend E3 p) z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend E3 q) z₀) := by rw [hp, hq]
    _ = g.inner x₀ p q := by
          simpa [z₀] using hmetric

/-- At the anchor, lowering the bridged chart curvature by the chart metric
recovers the manifold curvature lowered by `g`. -/
theorem chartMetric_chartCurvatureOf_chartChristoffelField_eq_inner_curvature
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (u w a b : TM3 x₀) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀)
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          (extChartAt I3 x₀ x₀) u w a) b =
      g.inner x₀
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E3 u) (extend E3 w) (extend E3 a) x₀) b := by
  let z₀ : E3 := extChartAt I3 x₀ x₀
  let R : Π y : M, TM3 y :=
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E3 u) (extend E3 w) (extend E3 a)
  have htarget : z₀ ∈ (extChartAt I3 x₀).target := by
    simp [z₀]
  have hb :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend E3 b) z₀ = b := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := 3) (M := M) (x := x₀) (y := x₀)
        (mem_extChartAt_source (I := I3) x₀) b)
  have hcurv :
      chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          z₀ u w a =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀ := by
    simpa [z₀, R] using
      (ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp
        (g := g) (x₀ := x₀) u w a)
  have hlower :
      CovariantDerivative.chartMetric g.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend E3 b) z₀) =
        g.inner x₀ (R x₀) b := by
    have h :=
      CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
        (g := g.inner) (x₀ := x₀) (Y := R)
        (Z := extend E3 b) (hz := htarget)
    have hsymm : (extChartAt I3 x₀).symm z₀ = x₀ := by
      simp [z₀]
    rw [hsymm] at h
    simpa [z₀, R] using h
  calc
    CovariantDerivative.chartMetric g.inner x₀ z₀
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          z₀ u w a) b =
        CovariantDerivative.chartMetric g.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend E3 b) z₀) := by rw [hcurv, hb]
    _ = g.inner x₀ (R x₀) b := hlower

omit [T2Space M] in
/-- At the anchor, the manifold Kulkarni-Nomizu tensor is the chart
Kulkarni-Nomizu tensor of the transported chart metric. -/
theorem tensorKulkarniNomizuAt_eq_chartMetric_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (u w a b : TM3 x₀) :
    ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
        (n := 3) (M := M) x₀
        (fun p q ↦ g.inner x₀ p q)
        (fun p q ↦ g.inner x₀ p q) u w a b =
      chartTensorKulkarniNomizu
        (fun p q : TM3 x₀ =>
          CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
        (fun p q : TM3 x₀ =>
          CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
        u w a b := by
  unfold ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
    chartTensorKulkarniNomizu
  simp only [← chartMetric_anchor_eq_inner (g := g) (x₀ := x₀)]

/-- Chart-level constant-curvature-one identity for `chartChristoffelField` at
the anchor.  This is the forward transport of `HasConstantSectionalCurvature3`
through `ChartCurvatureBridge6`. -/
theorem chartCurvatureOf_chartChristoffelField_constantCurvature_one_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) (u w a b : TM3 x₀) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀)
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          (extChartAt I3 x₀ x₀) u w a) b =
      -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : TM3 x₀ =>
            CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
          (fun p q : TM3 x₀ =>
            CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
          u w a b := by
  calc
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀)
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          (extChartAt I3 x₀ x₀) u w a) b =
        g.inner x₀
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 u) (extend E3 w) (extend E3 a) x₀) b := by
          exact chartMetric_chartCurvatureOf_chartChristoffelField_eq_inner_curvature
            (g := g) (x₀ := x₀) u w a b
    _ = -(1 / 2 : ℝ) *
        ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
          (n := 3) (M := M) x₀
          (fun p q ↦ g.inner x₀ p q)
          (fun p q ↦ g.inner x₀ p q) u w a b := by
          simpa using hcurv x₀ u w a b
    _ = -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : TM3 x₀ =>
            CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
          (fun p q : TM3 x₀ =>
            CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) p q)
          u w a b := by
          rw [tensorKulkarniNomizuAt_eq_chartMetric_anchor]

/-- Lowered contraction form of the anchor constant-curvature identity:
for unit transverse data, lowering `R(v,J)v` gives the same covector as
lowering `-J`.  Raising this to a model-vector equality is the remaining
generic tangent/chart-coordinate bookkeeping step. -/
theorem chartCurvatureOf_chartChristoffelField_unit_orthogonal_lowered_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) (v J : TM3 x₀)
    (hunit :
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) v v = 1)
    (horth :
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) J v = 0)
    (b : TM3 x₀) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀)
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀)
          (extChartAt I3 x₀ x₀) v J v) b =
      -CovariantDerivative.chartMetric g.inner x₀ (extChartAt I3 x₀ x₀) J b := by
  let z₀ : E3 := extChartAt I3 x₀ x₀
  have hlow :=
    chartCurvatureOf_chartChristoffelField_constantCurvature_one_anchor
      (g := g) hcurv x₀ v J v b
  have hcontraction :=
    chartTensorKulkarniNomizu_unit_orthogonal_contraction
      (G := fun p q : TM3 x₀ =>
        CovariantDerivative.chartMetric g.inner x₀ z₀ p q)
      (v := v) (J := J) (a := b) hunit horth
  simpa [z₀] using hlow.trans hcontraction

end Poincare
