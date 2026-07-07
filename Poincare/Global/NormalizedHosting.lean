import Poincare.Global.SpeedPackage

/-!
# Anchor-metric normalized hosting

This module records the non-vacuous algebraic part of the G-normalized
hosting route.  The working time is the square root of the source anchor
metric value and the working velocity is the corresponding inverse-time
rescaling.  For every nonzero endpoint vector this makes the transported
source speed exactly `1`; through a `CartanMap.TangentAlignment`, the aligned
target speed is exactly `1` with the same time.

The PL hosting radius issue is deliberately not hidden: the unit-speed
theorems below assume the existing PL hypotheses at the normalized velocity.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace NormalizedHosting

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- Anchor-metric working time for the source endpoint vector. -/
def sourceNormalizedTime (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (v : E) : ℝ :=
  Real.sqrt (CartanMap.sourceAnchorChartMetric g x₀ v v)

/-- Anchor-metric normalized source working velocity. -/
def sourceNormalizedVelocity (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (v : E) : E :=
  (sourceNormalizedTime g x₀ v)⁻¹ • v

/-- The aligned target working velocity using the same source-normalized time. -/
def alignedTargetNormalizedVelocity
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (_L : CartanMap.TangentAlignment g x₀ p₀) (v : E) : E :=
  (sourceNormalizedTime g x₀ v)⁻¹ • _L v

/-- Bilinear scaling for continuous bilinear chart-metric pairings. -/
theorem continuousLinearPairing_smul_smul
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

/-- Source anchor-metric bilinear scaling under identical rescaling. -/
theorem sourceAnchorChartMetric_smul_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (c : ℝ) (u v : E) :
    CartanMap.sourceAnchorChartMetric g x₀ (c • u) (c • v) =
      c * c * CartanMap.sourceAnchorChartMetric g x₀ u v := by
  simpa using
    continuousLinearPairing_smul_smul
      (CartanMap.sourceAnchorChartMetric g x₀) c c u v

/-- Target anchor-metric bilinear scaling under identical rescaling. -/
theorem targetAnchorChartMetric_smul_smul
    (p₀ : RoundSphere3) (c : ℝ) (u v : E) :
    CartanMap.targetAnchorChartMetric p₀ (c • u) (c • v) =
      c * c * CartanMap.targetAnchorChartMetric p₀ u v := by
  simpa using
    continuousLinearPairing_smul_smul
      (CartanMap.targetAnchorChartMetric p₀) c c u v

theorem sourceNormalizedTime_pos
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E}
    (hv : v ≠ 0) :
    0 < sourceNormalizedTime g x₀ v := by
  exact Real.sqrt_pos.mpr (CartanMap.sourceAnchorChartMetric_pos g x₀ hv)

theorem sourceNormalizedTime_ne_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E}
    (hv : v ≠ 0) :
    sourceNormalizedTime g x₀ v ≠ 0 :=
  ne_of_gt (sourceNormalizedTime_pos g x₀ hv)

/-- The normalized time and velocity still host the original endpoint vector. -/
theorem sourceNormalizedTime_smul_sourceNormalizedVelocity
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E}
    (hv : v ≠ 0) :
    sourceNormalizedTime g x₀ v • sourceNormalizedVelocity g x₀ v = v := by
  rw [sourceNormalizedVelocity, smul_smul]
  have hT : sourceNormalizedTime g x₀ v ≠ 0 :=
    sourceNormalizedTime_ne_zero g x₀ hv
  have hcoef : sourceNormalizedTime g x₀ v * (sourceNormalizedTime g x₀ v)⁻¹ = 1 := by
    field_simp [hT]
  rw [hcoef, one_smul]

/-- Positive endpoint rescaling scales the normalized working time by the same factor. -/
theorem sourceNormalizedTime_pos_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {c : ℝ} (hc : 0 < c) {v : E} (hv : v ≠ 0) :
    sourceNormalizedTime g x₀ (c • v) =
      c * sourceNormalizedTime g x₀ v := by
  let S : ℝ := CartanMap.sourceAnchorChartMetric g x₀ v v
  have hS_pos : 0 < S := CartanMap.sourceAnchorChartMetric_pos g x₀ hv
  have hmetric :
      CartanMap.sourceAnchorChartMetric g x₀ (c • v) (c • v) = c * c * S := by
    simpa [S] using sourceAnchorChartMetric_smul_smul g x₀ c v v
  calc
    sourceNormalizedTime g x₀ (c • v)
        = Real.sqrt (c * c * S) := by
          rw [sourceNormalizedTime, hmetric]
    _ = Real.sqrt (c * c) * Real.sqrt S := by
          rw [Real.sqrt_mul (mul_self_nonneg c) S]
    _ = c * sourceNormalizedTime g x₀ v := by
          rw [Real.sqrt_mul_self hc.le]
          rfl

/--
Shrinking the endpoint along a positive ray does not shrink the G-normalized
working velocity.
-/
theorem sourceNormalizedVelocity_pos_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {c : ℝ} (hc : 0 < c) {v : E} (hv : v ≠ 0) :
    sourceNormalizedVelocity g x₀ (c • v) =
      sourceNormalizedVelocity g x₀ v := by
  have hT : sourceNormalizedTime g x₀ v ≠ 0 :=
    sourceNormalizedTime_ne_zero g x₀ hv
  rw [sourceNormalizedVelocity, sourceNormalizedTime_pos_smul g x₀ hc hv,
    sourceNormalizedVelocity, smul_smul]
  congr 1
  field_simp [ne_of_gt hc, hT]

/-- The aligned target normalized data host the aligned endpoint vector. -/
theorem sourceNormalizedTime_smul_alignedTargetNormalizedVelocity
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) {v : E} (hv : v ≠ 0) :
    sourceNormalizedTime g x₀ v • alignedTargetNormalizedVelocity L v = L v := by
  rw [alignedTargetNormalizedVelocity, smul_smul]
  have hT : sourceNormalizedTime g x₀ v ≠ 0 :=
    sourceNormalizedTime_ne_zero g x₀ hv
  have hcoef : sourceNormalizedTime g x₀ v * (sourceNormalizedTime g x₀ v)⁻¹ = 1 := by
    field_simp [hT]
  rw [hcoef, one_smul]

/-- The source normalized working velocity has anchor-metric speed exactly `1`. -/
theorem sourceAnchorChartMetric_sourceNormalizedVelocity_self
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E}
    (hv : v ≠ 0) :
    CartanMap.sourceAnchorChartMetric g x₀
        (sourceNormalizedVelocity g x₀ v)
        (sourceNormalizedVelocity g x₀ v) = 1 := by
  let T : ℝ := sourceNormalizedTime g x₀ v
  let S : ℝ := CartanMap.sourceAnchorChartMetric g x₀ v v
  have hS_pos : 0 < S := CartanMap.sourceAnchorChartMetric_pos g x₀ hv
  have hS_nonneg : 0 ≤ S := le_of_lt hS_pos
  have hT_ne : T ≠ 0 := by
    dsimp [T]
    exact sourceNormalizedTime_ne_zero g x₀ hv
  have hT_sq : T * T = S := by
    dsimp [T, sourceNormalizedTime, S]
    simpa [pow_two] using Real.sq_sqrt hS_nonneg
  calc
    CartanMap.sourceAnchorChartMetric g x₀
        (sourceNormalizedVelocity g x₀ v)
        (sourceNormalizedVelocity g x₀ v)
        = T⁻¹ * T⁻¹ * S := by
          dsimp [sourceNormalizedVelocity, T, S]
          rw [sourceAnchorChartMetric_smul_smul]
    _ = T⁻¹ * T⁻¹ * (T * T) := by rw [hT_sq]
    _ = 1 := by field_simp [hT_ne]

/--
The same source-normalized time gives aligned target anchor-metric speed
exactly `1`.
-/
theorem targetAnchorChartMetric_alignedTargetNormalizedVelocity_self
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) {v : E} (hv : v ≠ 0) :
    CartanMap.targetAnchorChartMetric p₀
        (alignedTargetNormalizedVelocity L v)
        (alignedTargetNormalizedVelocity L v) = 1 := by
  have hmap :
      CartanMap.targetAnchorChartMetric p₀
          (alignedTargetNormalizedVelocity L v)
          (alignedTargetNormalizedVelocity L v) =
        CartanMap.sourceAnchorChartMetric g x₀
          (sourceNormalizedVelocity g x₀ v)
          (sourceNormalizedVelocity g x₀ v) := by
    simpa [alignedTargetNormalizedVelocity, sourceNormalizedVelocity] using
      CartanMap.TangentAlignment.map_app L
        ((sourceNormalizedTime g x₀ v)⁻¹ • v)
        ((sourceNormalizedTime g x₀ v)⁻¹ • v)
  rw [hmap, sourceAnchorChartMetric_sourceNormalizedVelocity_self g x₀ hv]

/--
Unit-speed source hosted curve on a shrunken interval, once the existing PL
flow hypotheses are available at the G-normalized velocity.
-/
theorem hosted_source_curve_unit_speed_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v : E}
    (hv : v ≠ 0)
    (hα0 :
      α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) 0 =
        (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) x₀
        (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).1 = 1)
    {a b : ℝ} (ha : -ε < a) (hb : b < ε) :
    ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric g.inner x₀
          (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).1
          (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).2
          (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).2 = 1 := by
  intro t ht
  calc
    CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).1
        (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).2
        (α (extChartAt I x₀ x₀, sourceNormalizedVelocity g x₀ v) t).2 =
      CartanMap.sourceAnchorChartMetric g x₀
        (sourceNormalizedVelocity g x₀ v)
        (sourceNormalizedVelocity g x₀ v) := by
        exact SpeedPackage.chartMetric_speed_eq_anchor_on_shrunk_Icc
          (g := g) (x₀ := x₀) (ε := ε) hε
          (α := α) (v₀ := sourceNormalizedVelocity g x₀ v)
          hα0 hαder hαcut ha hb ht
    _ = 1 := sourceAnchorChartMetric_sourceNormalizedVelocity_self g x₀ hv

/--
Unit-speed aligned target hosted curve on a shrunken interval, using the same
source-normalized time.
-/
theorem hosted_aligned_target_curve_unit_speed_on_shrunk_Icc
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v : E}
    (hv : v ≠ 0)
    (hα0 :
      α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) 0 =
        (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) p₀
        (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).1 = 1)
    {a b : ℝ} (ha : -ε < a) (hb : b < ε) :
    ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).1
          (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).2
          (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).2 = 1 := by
  intro t ht
  calc
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).1
        (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).2
        (α (extChartAt I p₀ p₀, alignedTargetNormalizedVelocity L v) t).2 =
      CartanMap.targetAnchorChartMetric p₀
        (alignedTargetNormalizedVelocity L v)
        (alignedTargetNormalizedVelocity L v) := by
        exact SpeedPackage.target_chartMetric_speed_eq_anchor_on_shrunk_Icc
          (p₀ := p₀) (ε := ε) hε
          (α := α) (v₀ := alignedTargetNormalizedVelocity L v)
          hα0 hαder hαcut ha hb ht
    _ = 1 := targetAnchorChartMetric_alignedTargetNormalizedVelocity_self L hv

end NormalizedHosting
end Poincare
