import Poincare.Global.UnscaledFeed

/-!
# Source endpoint package and scalar normalizations

This module mirrors `TargetPackage` on the source metric: the round-sphere
curvature witness is replaced by an explicit
`HasConstantSectionalCurvature3 g 1` hypothesis.  It also records the scalar
normalization that converts the rescaled `sin²` endpoint feed through the
inverse-time initial data used by `UnscaledFeed`.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SourcePackage

universe u

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/--
The cutoff-one Jacobi norm theorem specialized to a source metric with
constant sectional curvature `1`.
-/
theorem source_normA_eq_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E × E}
    {tmin tmax q : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA q s,
        JacobiNormSystem.pinnedB q s,
        JacobiNormSystem.pinnedC q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA g x₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t = Real.sin t ^ 2 * q := by
  exact
    (CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (tmin := tmin) (tmax := tmax) (q := q) hzero Aop
      (hpl := hpl) hAop hγ hΨ htarget hχone hunit horth hGd
      hmem hpinnedmem ha0 hb0 hc0 ht).1

/--
Family-level source quadratic package for the hosted rescaled cascade data.
-/
theorem source_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E × E} {Ψ : E → ℝ → E × E}
    {T tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : ∀ w : E,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedB
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedC
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        Real.sin T ^ 2 *
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w) := by
  intro w
  exact
    source_normA_eq_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax)
      (q := chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hzero Aop (hpl w) hAop hγ (hΨ w) htarget hχone hunit
      (horth w) hGd (hmem w) (hpinnedmem w) (ha0 w) (hb0 w) (hc0 w) hT

/--
Pinned source endpoint formula for the actual hosted rescaled source cascade,
assuming the source interval/norm package above and the linearized uniqueness
data required by `CascadePinned`.
-/
theorem source_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E × E} {Ψ : E → ℝ → E × E}
    {v : E} {T tmin tmax : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E × E =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedB
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedC
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin T ^ 2 *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have hcutT : cutoff (n := 3) x₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ w : E,
        JacobiNormSystem.normA g x₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ w τ).1) T =
          Real.sin T ^ 2 *
            chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w) :=
    source_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hunit
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  exact
    CascadePinned.hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax)
      hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT hcutT
      hendpoint hquad

/-- The normalized angle whose sine is the rescaled transverse factor `sin T / T`. -/
def normalizedRescaledAngle (T : ℝ) : ℝ :=
  Real.arcsin (Real.sin T * T⁻¹)

theorem abs_sin_mul_inv_le_one {T : ℝ} (hT : T ≠ 0) :
    |Real.sin T * T⁻¹| ≤ 1 := by
  have hsin : |Real.sin T| ≤ |T| := Real.abs_sin_le_abs
  have hTpos : 0 < |T| := abs_pos.mpr hT
  calc
    |Real.sin T * T⁻¹| = |Real.sin T| / |T| := by
      rw [abs_mul, abs_inv, div_eq_mul_inv]
    _ ≤ |T| / |T| := div_le_div_of_nonneg_right hsin hTpos.le
    _ = 1 := div_self (ne_of_gt hTpos)

theorem neg_one_le_sin_mul_inv {T : ℝ} (hT : T ≠ 0) :
    -1 ≤ Real.sin T * T⁻¹ :=
  (abs_le.mp (abs_sin_mul_inv_le_one hT)).1

theorem sin_mul_inv_le_one {T : ℝ} (hT : T ≠ 0) :
    Real.sin T * T⁻¹ ≤ 1 :=
  (abs_le.mp (abs_sin_mul_inv_le_one hT)).2

theorem sin_normalizedRescaledAngle {T : ℝ} (hT : T ≠ 0) :
    Real.sin (normalizedRescaledAngle T) = Real.sin T * T⁻¹ := by
  simpa [normalizedRescaledAngle] using
    (Real.sin_arcsin (neg_one_le_sin_mul_inv hT) (sin_mul_inv_le_one hT))

/--
The exact scalar normalization required by `UnscaledFeed` after inverse-time
unscaling of the initial directions.
-/
theorem rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
    {T : ℝ} (hT : T ≠ 0) :
    Real.sin T ^ 2 * (T⁻¹ * T⁻¹) =
      Real.sin (normalizedRescaledAngle T) ^ 2 := by
  rw [sin_normalizedRescaledAngle hT]
  ring

/-- The same scalar written as the square of the hosted transverse scale. -/
theorem hostedTransverseScaleFromSpeed_sq_eq_rescaled_sin_sq (speed T : ℝ) :
    CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T ^ 2 =
      Real.sin (speed * T) ^ 2 * ((speed * T)⁻¹ * (speed * T)⁻¹) := by
  rw [CartanScaleGeneric.hostedTransverseScaleFromSpeed, div_eq_mul_inv]
  ring

/-- For nonzero hosted vectors, the working velocity has norm `δ / 2`. -/
theorem norm_workingVelocity_eq_half
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    ‖CartanHomogeneity.workingVelocity δ v‖ = δ / 2 := by
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm_inv_pos : 0 < ‖v‖⁻¹ := inv_pos.mpr hnorm_pos
  have hhalf_pos : 0 < δ / 2 := by linarith
  rw [CartanHomogeneity.workingVelocity, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hhalf_pos, abs_of_pos hnorm_inv_pos]
  rw [inv_mul_cancel₀ (ne_of_gt hnorm_pos), mul_one]

/--
Rigid-47's hosted time normalization plugged into the scalar normalization.
-/
theorem hostedDeltaForTime_rescaled_sin_sq_factor
    {T : ℝ} (hT : T ≠ 0) {v : E} (hv : v ≠ 0) :
    Real.sin T ^ 2 * (T⁻¹ * T⁻¹) =
      Real.sin
        (normalizedRescaledAngle
          (CartanHomogeneity.workingTime
            (CartanFinalComposition.hostedDeltaForTime T v) v)) ^ 2 := by
  rw [CartanFinalComposition.workingTime_hostedDeltaForTime (T := T) hT hv]
  exact rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hT

/-- The source and target hosted normalized sine factors agree through alignment. -/
theorem hosted_source_target_normalized_sin_sq_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    Real.sin
        (normalizedRescaledAngle
          (CartanScaleGeneric.hostedTargetSpeed L δ v *
            CartanHomogeneity.workingTime δ v)) ^ 2 =
      Real.sin
        (normalizedRescaledAngle
          (CartanScaleGeneric.hostedSourceSpeed g x₀ δ v *
            CartanHomogeneity.workingTime δ v)) ^ 2 := by
  rw [EqualityChain.hostedTargetSpeed_eq_hostedSourceSpeed
    (g := g) (x₀ := x₀) (p₀ := p₀) L δ v]

/--
Common-time rescaled feeds discharge the three scalar hypotheses in
`UnscaledFeed`.
-/
theorem hosted_endpoint_pairing_feed_of_common_rescaled_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {Ψs Ψt : E → ℝ → E × E} {T : ℝ} (hT : T ≠ 0)
    (hSourceRescaled :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          Real.sin T ^ 2 *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          Real.sin T ^ 2 *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ a a' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 :=
  UnscaledFeed.hosted_endpoint_pairing_feed_of_rescaled_sin_sq_anchor_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (Ψs := Ψs) (Ψt := Ψt)
    (Ts := T) (Tt := T)
    (θs := normalizedRescaledAngle T) (θt := normalizedRescaledAngle T)
    (rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hT)
    (rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hT)
    rfl hSourceRescaled hTargetRescaled

/--
Local-isometry consumer with common-time source and target rescaled endpoint
feeds; the scalar assumptions are discharged by the normalizations above.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_common_rescaled_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    {Ψs Ψt : E → ℝ → E × E} {T : ℝ}
    {hadds : ∀ w w' : E,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E),
      (Ψt (c • w) T).1 = c • (Ψt w T).1}
    (hA :
      (A : E →L[ℝ] E) =
        linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls)
    (hB :
      (B : E →L[ℝ] E) =
        linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E) (hT : T ≠ 0)
    (hSourceRescaled :
      ∀ a a' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          Real.sin T ^ 2 *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          Real.sin T ^ 2 *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' :=
  UnscaledFeed.cartanMap_isLocalIsometry_on_normalBall_of_rescaled_sin_sq_hosted_anchor_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
    (Ts := T) (Tt := T)
    (θs := normalizedRescaledAngle T) (θt := normalizedRescaledAngle T)
    hA hB hvsrc hsourceDeriv htargetDeriv u u'
    (rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hT)
    (rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hT)
    rfl hSourceRescaled hTargetRescaled

end SourcePackage
end Poincare
