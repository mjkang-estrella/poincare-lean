import Poincare.Global.UniformPL
import Poincare.Global.PLNormFeed

/-!
# Bounded PL packages and homogeneous endpoint extension

The unrestricted norm-system Picard-Lindelöf package is false: the center
carries the quadratic metric value.  This module keeps that package bounded in
the endpoint direction and records the bilinear homogeneous extension used by
the downstream transverse pairing consumers.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace BoundedPackage

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The hosted norm-system PL package on a closed ball of endpoint directions.

This is the direct bounded-center instantiation of
`UniformPL.isPicardLindelof_const_linear_uniform_of_center_norm_bound`: the
only geometric input is a genuine finite bound for the moving quadratic
centers over the chosen ball.
-/
theorem hosted_hplNorm_on_closedBall_of_center_norm_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm B : ℝ≥0}
    (hAopNorm : ‖Aop‖ ≤ (KNorm : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmul :
      (LNorm : ℝ) *
          max (tmax - (0 : ℝ)) ((0 : ℝ) - tmin) ≤
        (radius : ℝ) - (rNorm : ℝ)) :
    ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm := by
  let center : {w : E3 // w ∈ closedBall (0 : E3) (R : ℝ)} → Triple :=
    fun w =>
      ((0 : ℝ), (0 : ℝ),
        GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • (w : E3)) (T⁻¹ • (w : E3)))
  have hcenter' :
      ∀ i, ‖center i‖ + (radius : ℝ) ≤ (B : ℝ) := by
    intro i
    exact hcenter i i.property
  have hpl :=
    UniformPL.isPicardLindelof_const_linear_uniform_of_center_norm_bound
      (A := Aop) (center := center)
      (t₀ := (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax))
      (a := radius) (r := rNorm) (L := LNorm) (K := KNorm) (B := B)
      hAopNorm hcenter' hbound hmul
  intro w hw
  simpa [center] using hpl ⟨w, hw⟩

private theorem scaled_pair_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R S : ℝ} (hS : 0 < S)
    {w w' : E} (hsum : ‖w‖ + ‖w'‖ ≤ R * S) :
    S⁻¹ • w ∈ closedBall (0 : E) R ∧
      S⁻¹ • w' ∈ closedBall (0 : E) R ∧
        S⁻¹ • (w + w') ∈ closedBall (0 : E) R := by
  have hw_le : ‖w‖ ≤ R * S := by
    calc
      ‖w‖ ≤ ‖w‖ + ‖w'‖ := le_add_of_nonneg_right (norm_nonneg w')
      _ ≤ R * S := hsum
  have hw'_le : ‖w'‖ ≤ R * S := by
    calc
      ‖w'‖ ≤ ‖w‖ + ‖w'‖ := le_add_of_nonneg_left (norm_nonneg w)
      _ ≤ R * S := hsum
  have hadd_le : ‖w + w'‖ ≤ R * S := by
    calc
      ‖w + w'‖ ≤ ‖w‖ + ‖w'‖ := norm_add_le w w'
      _ ≤ R * S := hsum
  have hmem_of_le : ∀ {z : E}, ‖z‖ ≤ R * S →
      S⁻¹ • z ∈ closedBall (0 : E) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hz' : S⁻¹ * ‖z‖ ≤ R := by
      rw [inv_mul_le_iff₀ hS]
      simpa [mul_comm] using hz
    calc
      ‖S⁻¹ • z - 0‖ = ‖S⁻¹ • z‖ := by simp
      _ = S⁻¹ * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS)]
      _ ≤ R := hz'
  exact ⟨hmem_of_le hw_le, hmem_of_le hw'_le, hmem_of_le hadd_le⟩

/-- Bilinear scaling for continuous bilinear pairings. -/
private theorem continuousLinearPairing_smul_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c d : ℝ) (u v : E) :
    B (c • u) (d • v) = c * d * B u v := by
  have hleft : B (c • u) = c • B u := by
    exact map_smul B c u
  have hright : (B u) (d • v) = d * B u v := by
    simp [map_smul (B u) d v]
  calc
    B (c • u) (d • v) = (c • B u) (d • v) := by rw [hleft]
    _ = c * (B u (d • v)) := by rfl
    _ = c * (d * B u v) := by rw [hright]
    _ = c * d * B u v := by ring

/--
Extend a bilinear endpoint pairing formula from any positive closed ball to
all directions, assuming the endpoint map is homogeneous and the side
condition is stable under scalar multiplication.
-/
theorem homogeneous_bilinear_pairing_of_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B G : E →L[ℝ] E →L[ℝ] ℝ) (J : E → E) (scale : ℝ)
    (P : E → Prop) {R : ℝ} (hR : 0 < R)
    (hP_smul : ∀ (c : ℝ) w, P w → P (c • w))
    (hJ_smul : ∀ (c : ℝ) w, J (c • w) = c • J w)
    (hsmall : ∀ w w' : E, P w → P w' →
      w ∈ closedBall (0 : E) R →
      w' ∈ closedBall (0 : E) R →
      w + w' ∈ closedBall (0 : E) R →
        G (J w) (J w') = scale * B w w') :
    ∀ w w' : E, P w → P w' →
      G (J w) (J w') = scale * B w w' := by
  intro w w' hwP hw'P
  let S : ℝ := max 1 ((‖w‖ + ‖w'‖) / R)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSge : (‖w‖ + ‖w'‖) / R ≤ S := le_max_right _ _
  have hsum_le : ‖w‖ + ‖w'‖ ≤ R * S := by
    have hmul := mul_le_mul_of_nonneg_left hSge hR.le
    have hleft : R * ((‖w‖ + ‖w'‖) / R) = ‖w‖ + ‖w'‖ := by
      field_simp [ne_of_gt hR]
    simpa [hleft, mul_comm] using hmul
  rcases scaled_pair_mem_closedBall (E := E) hSpos (w := w) (w' := w') hsum_le with
    ⟨hwb, hw'b, haddb⟩
  have hsmall' :=
    hsmall (S⁻¹ • w) (S⁻¹ • w')
      (hP_smul S⁻¹ w hwP) (hP_smul S⁻¹ w' hw'P) hwb hw'b
      (by simpa [smul_add] using haddb)
  have hSw : S • (S⁻¹ • w) = w := by
    have hSinv : S * S⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hSpos)
    simp [smul_smul, hSinv]
  have hSw' : S • (S⁻¹ • w') = w' := by
    have hSinv : S * S⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hSpos)
    simp [smul_smul, hSinv]
  have hJw : J w = S • J (S⁻¹ • w) := by
    calc
      J w = J (S • (S⁻¹ • w)) := by rw [hSw]
      _ = S • J (S⁻¹ • w) := hJ_smul S (S⁻¹ • w)
  have hJw' : J w' = S • J (S⁻¹ • w') := by
    calc
      J w' = J (S • (S⁻¹ • w')) := by rw [hSw']
      _ = S • J (S⁻¹ • w') := hJ_smul S (S⁻¹ • w')
  have hBw : B w w' = S * S * B (S⁻¹ • w) (S⁻¹ • w') := by
    simpa [hSw, hSw'] using
      continuousLinearPairing_smul_smul B S S (S⁻¹ • w) (S⁻¹ • w')
  calc
    G (J w) (J w') =
        S * S * G (J (S⁻¹ • w)) (J (S⁻¹ • w')) := by
      rw [hJw, hJw']
      exact continuousLinearPairing_smul_smul
        G S S (J (S⁻¹ • w)) (J (S⁻¹ • w'))
    _ = S * S * (scale * B (S⁻¹ • w) (S⁻¹ • w')) := by
      rw [hsmall']
    _ = scale * B w w' := by
      rw [hBw]
      ring

section SourceBounded

variable [T2Space M]

open GeodesicTransport

/--
Source transverse quadratic norm identity from a bounded norm-system PL
package.  The PL hypothesis is consumed only for the direction being proved.
-/
theorem source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_plNorm_on_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hpl : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        JacobiNormSystem.normA g x₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ w τ).1) T =
          JacobiNormSystem.speedPinnedScale speed T *
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w) := by
  intro w hwb hw
  exact
    SourcePackage.source_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax) (speed := speed)
      (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hspeed_ne hzero Aop (hpl w hwb) hAop hγ (hΨ w) htarget hχone hspeed
      (horth w hw) hGd (hmem w) (hpinnedmem w) (ha0 w) (hb0 w) (hc0 w) hT

/--
Source transverse-transverse endpoint formula from a bounded norm-system PL
package.  Polarization uses the bounded package only at `w`, `w'`, and
`w + w'`.
-/
theorem source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  intro w w' hw hw' hwb hw'b haddb
  have hcutT : cutoff (n := 3) x₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ z : E3, z ∈ closedBall (0 : E3) (R : ℝ) →
        CartanMap.sourceAnchorChartMetric g x₀ v z = 0 →
          JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ z τ).1) T =
            JacobiNormSystem.speedPinnedScale speed T *
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • z) (T⁻¹ • z) :=
    source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_plNorm_on_closedBall
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hwadd : CartanMap.sourceAnchorChartMetric g x₀ v (w + w') = 0 := by
    simp [hw, hw']
  have hΨadd0 :
      Ψ (w + w') 0 = ((0 : E3), T⁻¹ • w + T⁻¹ • w') := by
    rw [hΨ0 (w + w')]
    simp [smul_add]
  have hPairBlended :
      chartGeodesicMetric g x₀ (γ T).1 (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w') :=
    CascadePinned.actual_jacobi_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ)
      (Ψw := Ψ w) (Ψw' := Ψ w') (Ψadd := Ψ (w + w'))
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (tmin := tmin) (tmax := tmax)
      (S := JacobiNormSystem.speedPinnedScale speed T) hzero
      (a := aLin) (r := rLin) (L := LipLin) (K := KLin)
      (hpl := by simpa [smul_add] using hplLinear w w')
      (hΨw := hΨderWithin w) (hΨw' := hΨderWithin w')
      (hΨadd := hΨderWithin (w + w'))
      (hmem_add := by simpa [smul_add] using hmem_add w w')
      (hmem_sum := by simpa [smul_add] using hmem_sum w w')
      (hΨw0 := hΨ0 w) (hΨw'0 := hΨ0 w') (hΨadd0 := hΨadd0)
      (ht := hT) (hquad_w := hquad w hwb hw)
      (hquad_w' := hquad w' hw'b hw')
      (hquad_add := by simpa [smul_add] using hquad (w + w') haddb hwadd)
  have hPairChart :
      CovariantDerivative.chartMetric g.inner x₀ (γ T).1
          (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
    CascadePinned.chartMetric_pairing_eq_pinned_of_blended_pairing
      (g := g) (x₀ := x₀) (z := (γ T).1)
      (J := (Ψ w T).1) (J' := (Ψ w' T).1)
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := JacobiNormSystem.speedPinnedScale speed T) hcutT hPairBlended
  simpa [hendpoint] using hPairChart

end SourceBounded

section TargetBounded

open GeodesicTransport

/--
Target transverse-transverse endpoint formula from a bounded norm-system PL
package.  This mirrors the source theorem through the round-sphere metric.
-/
theorem target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField roundSphereMetric3 p₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have horthSource : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0 := by
    intro w hw
    exact horth w (by
      simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw)
  have hsource :=
    source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall
      (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT
      hendpoint Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horthSource hGd hmemNorm hpinnedmem ha0 hb0 hc0
  intro w w' hw hw' hwb hw'b haddb
  have hws : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw
  have hw's : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w' = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using hsource w w' hws hw's hwb hw'b haddb

end TargetBounded

section HomogeneousExtensions

open GeodesicTransport

/--
Homogeneous extension of the source transverse-transverse formula from a
positive ball to all transverse directions.
-/
theorem source_transverseTransverse_extend_from_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T speed : ℝ}
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hsmall : ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  let B0 : E3 →L[ℝ] E3 →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  let Brescaled : E3 →L[ℝ] E3 →L[ℝ] ℝ := (T⁻¹ * T⁻¹) • B0
  let G : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x₀
      ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
  let J : E3 → E3 := fun w => (Ψ w T).1
  have hsmall' : ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        G (J w) (J w') =
          JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
    intro w w' hw hw' hwb hw'b haddb
    have h := hsmall w w' hw hw' hwb hw'b haddb
    have hrescale :
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') =
          Brescaled w w' := by
      simpa [B0, Brescaled, ContinuousLinearMap.smul_apply, smul_eq_mul] using
        continuousLinearPairing_smul_smul
          (CartanMap.sourceAnchorChartMetric g x₀) T⁻¹ T⁻¹ w w'
    calc
      G (J w) (J w') =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
        simpa [G, J] using h
      _ = JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
        rw [hrescale]
  have hext :=
    homogeneous_bilinear_pairing_of_closedBall
      (B := Brescaled) (G := G) (J := J)
      (scale := JacobiNormSystem.speedPinnedScale speed T)
      (P := fun w : E3 => CartanMap.sourceAnchorChartMetric g x₀ v w = 0)
      hRpos
      (hP_smul := by
        intro c w hw
        simp [map_smul, smul_eq_mul, hw])
      (hJ_smul := by
        intro c w
        exact hΨsmul c w)
      hsmall'
  intro w w' hw hw'
  have h := hext w w' hw hw'
  have hrescale :
      Brescaled w w' =
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
    simpa [B0, Brescaled, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      (continuousLinearPairing_smul_smul
        (CartanMap.sourceAnchorChartMetric g x₀) T⁻¹ T⁻¹ w w').symm
  calc
    CovariantDerivative.chartMetric g.inner x₀
        ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        (Ψ w T).1 (Ψ w' T).1 =
      JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
        simpa [G, J] using h
    _ = JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
      rw [hrescale]

/--
Homogeneous extension of the target transverse-transverse formula from a
positive ball to all transverse directions.
-/
theorem target_transverseTransverse_extend_from_closedBall
    (p₀ : RoundSphere3)
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} {T speed : ℝ}
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hsmall : ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  let B0 : E3 →L[ℝ] E3 →L[ℝ] ℝ := CartanMap.targetAnchorChartMetric p₀
  let Brescaled : E3 →L[ℝ] E3 →L[ℝ] ℝ := (T⁻¹ * T⁻¹) • B0
  let G : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
  let J : E3 → E3 := fun w => (Ψ w T).1
  have hsmall' : ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        G (J w) (J w') =
          JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
    intro w w' hw hw' hwb hw'b haddb
    have h := hsmall w w' hw hw' hwb hw'b haddb
    have hrescale :
        CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') =
          Brescaled w w' := by
      simpa [B0, Brescaled, ContinuousLinearMap.smul_apply, smul_eq_mul] using
        continuousLinearPairing_smul_smul
          (CartanMap.targetAnchorChartMetric p₀) T⁻¹ T⁻¹ w w'
    calc
      G (J w) (J w') =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
        simpa [G, J] using h
      _ = JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
        rw [hrescale]
  have hext :=
    homogeneous_bilinear_pairing_of_closedBall
      (B := Brescaled) (G := G) (J := J)
      (scale := JacobiNormSystem.speedPinnedScale speed T)
      (P := fun w : E3 => CartanMap.targetAnchorChartMetric p₀ v w = 0)
      hRpos
      (hP_smul := by
        intro c w hw
        simp [map_smul, smul_eq_mul, hw])
      (hJ_smul := by
        intro c w
        exact hΨsmul c w)
      hsmall'
  intro w w' hw hw'
  have h := hext w w' hw hw'
  have hrescale :
      Brescaled w w' =
        CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
    simpa [B0, Brescaled, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      (continuousLinearPairing_smul_smul
        (CartanMap.targetAnchorChartMetric p₀) T⁻¹ T⁻¹ w w').symm
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
        (Ψ w T).1 (Ψ w' T).1 =
      JacobiNormSystem.speedPinnedScale speed T * Brescaled w w' := by
        simpa [G, J] using h
    _ = JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
      rw [hrescale]

end HomogeneousExtensions

end BoundedPackage
end Poincare
