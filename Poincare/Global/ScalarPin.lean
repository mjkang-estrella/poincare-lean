import Poincare.Global.AssemblyDone
import Poincare.Global.BoundedPackage

/-!
# Scalar pin and bounded transverse side-condition adapters

This module records the M5-rigid-102 scalar check.  The scalar demanded by
`PullbackFeed`,

`JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1`,

is false as a general identity.  The true scalar step is the normalized
two-sided sine factor already consumed by `EqualityChain`: after unscaling by
`T⁻²`, the speed-pinned scalar is

`sin (SourcePackage.normalizedRescaledAngle (speed * T))²`,

so the source and target endpoint pairings cancel against each other through a
common normalized angle, not against `T⁻²` alone.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace ScalarPin

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Concrete pin: the unit transverse scalar required by `PullbackFeed` is not a
valid identity.  At `speed = 1` and `T = π`, the sine factor vanishes.
-/
theorem speedPinnedScale_inv_sq_ne_one_at_one_pi :
    JacobiNormSystem.speedPinnedScale 1 Real.pi *
        (Real.pi⁻¹ * Real.pi⁻¹) ≠ 1 := by
  simp [JacobiNormSystem.speedPinnedScale]

/--
The actual scalar relation after the anchor metric contributes the `T⁻²`
factor.  This is the scalar that should be matched on the source and target
sides.
-/
theorem speedPinnedScale_inv_sq_eq_normalized_sin_sq
    {speed T : ℝ} (hspeed : speed ≠ 0) (hT : T ≠ 0) :
    JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) =
      Real.sin (SourcePackage.normalizedRescaledAngle (speed * T)) ^ 2 :=
  SpeedGeneric.speed_rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
    (speed := speed) (T := T) hspeed hT

omit [T2Space M] in
/--
Two-sided endpoint-pairing cancellation for speed-pinned rescaled anchor
pairings.  This is the corrected scalar adapter: both source and target carry
the same normalized sine-square factor.
-/
theorem hosted_endpoint_pairing_feed_of_two_sided_speed_pin
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    (hspeed : speed ≠ 0) (hT : T ≠ 0)
    (hSourceRescaled :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 :=
  SpeedGeneric.hosted_endpoint_pairing_feed_of_common_speed_rescaled_anchor_pairings
    (g := g) (x₀ := x₀) (p₀ := p₀) L
    (v := v) (Ψs := Ψs) (Ψt := Ψt) hspeed hT
    hSourceRescaled hTargetRescaled

/--
Source transverse block adapter with the norm-system PL package produced from
the bounded-center lemma.  The remaining scalar radius and initial norm
identities are the exact non-PL side conditions consumed by `AssemblyDone`.
-/
theorem source_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm B : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hAopNormPL : ‖Aop‖ ≤ (KNorm : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ))
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ))
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_of_lt hT⟩
  have hmul :
      (LNorm : ℝ) * max (T - (0 : ℝ)) ((0 : ℝ) - (0 : ℝ)) ≤
        (radius : ℝ) - (rNorm : ℝ) := by
    simpa [sub_eq_add_neg, max_eq_left hT.le] using hmulT
  have hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := 0) (tmax := T) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm :=
    BoundedPackage.hosted_hplNorm_on_closedBall_of_center_norm_bound
      (g := g) (x₀ := x₀) (T := T) (tmin := 0) (tmax := T)
      hzero Aop hAopNormPL hcenter hbound hmul
  exact
    AssemblyDone.source_transverseTransverse_of_enriched_gronwall_feed
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (C := C) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      hplNorm hAop hC hAopNorm hqBound hgronwallRadius hpinnedRadius
      ha0 hb0 hc0

/--
Target analogue of
`source_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound`.
-/
theorem target_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
    (p₀ : RoundSphere3)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm B : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hAopNormPL : ‖Aop‖ ≤ (KNorm : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ))
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ))
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a') := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_of_lt hT⟩
  have hmul :
      (LNorm : ℝ) * max (T - (0 : ℝ)) ((0 : ℝ) - (0 : ℝ)) ≤
        (radius : ℝ) - (rNorm : ℝ) := by
    simpa [sub_eq_add_neg, max_eq_left hT.le] using hmulT
  have hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := 0) (tmax := T) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm :=
    BoundedPackage.hosted_hplNorm_on_closedBall_of_center_norm_bound
      (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀)
      (T := T) (tmin := 0) (tmax := T)
      hzero Aop hAopNormPL hcenter hbound hmul
  exact
    AssemblyDone.target_transverseTransverse_of_enriched_gronwall_feed
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed)
      (C := C) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      hplNorm hAop hC hAopNorm hqBound hgronwallRadius hpinnedRadius
      ha0 hb0 hc0

end ScalarPin
end Poincare
