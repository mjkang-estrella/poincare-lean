import Poincare.Global.CascadePinned
import Poincare.Global.RoundSphereWitness

/-!
# Round-sphere target endpoint package

This module specializes the cutoff-one Jacobi norm assembly to the actual
round-sphere target metric and feeds the resulting family-level quadratic
identities into the pinned cascade bridge.

The final theorem still states the hosted cascade's honest rescaled initial
data: `Ψ w 0 = (0, T⁻¹ • w)`.  This is the non-vacuous target package exported
by the current upstream facts.
-/

noncomputable section

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace TargetPackage

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

open GeodesicTransport

/--
The cutoff-one Jacobi norm theorem specialized to the actual round-sphere
target.  The curvature witness is discharged by
`roundSphereMetric3_hasConstantSectionalCurvature_one`; all remaining
hypotheses are the interval and norm-system hypotheses used by the generic
source theorem.
-/
theorem target_normA_eq_pinned_on_cutoff_one_Icc
    (p₀ : RoundSphere3) {γ Ψ : ℝ → E × E}
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
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA q s,
        JacobiNormSystem.pinnedB q s,
        JacobiNormSystem.pinnedC q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA roundSphereMetric3 p₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t = Real.sin t ^ 2 * q := by
  exact
    (CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc
      (g := roundSphereMetric3)
      roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ)
      (tmin := tmin) (tmax := tmax) (q := q) hzero Aop
      (hpl := hpl) hAop hγ hΨ htarget hχone hunit horth hGd
      hmem hpinnedmem ha0 hb0 hc0 ht).1

/--
Family-level target quadratic package for the hosted rescaled cascade data.
The scalar `q` for each direction is the blended anchor metric of the actual
rescaled initial velocity `T⁻¹ • w`, matching the hypothesis consumed by
`CascadePinned.hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic...`.
-/
theorem target_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
    (p₀ : RoundSphere3) {γ : ℝ → E × E} {Ψ : E → ℝ → E × E}
    {T tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : ∀ w : E,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨ : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedB
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedC
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        Real.sin T ^ 2 *
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w) := by
  intro w
  exact
    target_normA_eq_pinned_on_cutoff_one_Icc
      (p₀ := p₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax)
      (q := chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hzero Aop (hpl w) hAop hγ (hΨ w) htarget hχone hunit
      (horth w) hGd (hmem w) (hpinnedmem w) (ha0 w) (hb0 w) (hc0 w) hT

/--
Pinned target endpoint formula for the actual hosted rescaled target cascade,
assuming the target interval/norm package above and the linearized uniqueness
data required by `CascadePinned`.
-/
theorem target_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package
    (p₀ : RoundSphere3) {γ : ℝ → E × E} {Ψ : E → ℝ → E × E}
    {v : E} {T tmin tmax : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E × E =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField roundSphereMetric3 p₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hunit : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = 1)
    (horth : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedB
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.pinnedC
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        Real.sin T ^ 2 *
          CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have hcutT : cutoff (n := 3) p₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ w : E,
        JacobiNormSystem.normA roundSphereMetric3 p₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ w τ).1) T =
          Real.sin T ^ 2 *
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w) :=
    target_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
      (p₀ := p₀) (γ := γ) (Ψ := Ψ)
      hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hunit
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hpinned :=
    CascadePinned.hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc
      (g := roundSphereMetric3) (x₀ := p₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax)
      hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT hcutT
      hendpoint hquad
  intro w w'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using hpinned w w'

end TargetPackage
end Poincare
