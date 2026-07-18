import Poincare.Global.RoundSphereTargetAnchorUniformity
import Poincare.Global.ExponentialLocalHomeo

/-!
# An anchor-uniform normalized exponential chart on the round sphere

The generic `GeodesicTransport.expAt` is chosen independently at every base
point.  Its current contract gives a positive inverse-function neighborhood at
each base point, but it contains no parameter continuity or uniform lower
bound for those neighborhoods.

For the round sphere there is a narrow way to remove that choice from the
target-anchor direction without changing the generic API.  Fix one reference
anchor and use its charted exponential as a common coordinate map.  At any
other anchor, transport that same coordinate map back through the anchor's
stereographic chart.  Since every extended stereographic chart has target
`univ`, charting the resulting sphere-valued map recovers the common coordinate
map everywhere.

Thus the inverse-function partial homeomorphism, its source and target, and a
ball on which both inverse identities hold are literally shared by every
target anchor.  This is a reference-normalized exponential family; this module
does not identify it with the independently chosen generic `expAt` at every
anchor.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace RoundSphereCanonicalExponential

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-- A fixed concrete anchor used to normalize all round-sphere exponential
coordinates. -/
def referenceAnchor : RoundSphere3 :=
  let v : RoundSphereAmbient4 := .single 0 1
  ⟨v, by simp [v]⟩

/-- The one chart-coordinate exponential map shared by every normalized
round-sphere anchor. -/
def coordinateLocalHomeomorph : OpenPartialHomeomorph E E :=
  GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) referenceAnchor

/-- The reference-normalized sphere-valued exponential at `p`. -/
def expAt (p : RoundSphere3) (v : E) : RoundSphere3 :=
  (extChartAt I p).symm (coordinateLocalHomeomorph v)

/-- The shared coordinate map sends zero to zero. -/
@[simp]
theorem coordinateLocalHomeomorph_zero :
    coordinateLocalHomeomorph (0 : E) = 0 := by
  change extChartAt I referenceAnchor
      (GeodesicTransport.expAt roundSphereMetric3 referenceAnchor 0) = 0
  rw [GeodesicTransport.expAt_zero]
  exact
    RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero
      referenceAnchor

/-- Charting the normalized exponential at any anchor recovers the common
coordinate map, with no smallness hypothesis. -/
theorem extChartAt_expAt (p : RoundSphere3) (v : E) :
    extChartAt I p (expAt p v) = coordinateLocalHomeomorph v := by
  apply (extChartAt I p).right_inv
  rw [RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_target_eq_univ]
  exact Set.mem_univ _

/-- The normalized exponential is based at its supplied anchor. -/
@[simp]
theorem expAt_zero (p : RoundSphere3) : expAt p (0 : E) = p := by
  change (extChartAt I p).symm (coordinateLocalHomeomorph 0) = p
  rw [coordinateLocalHomeomorph_zero]
  rw [← RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p]
  exact (extChartAt I p).left_inv (mem_extChartAt_source p)

/-- Every anchor uses the same inverse-function partial homeomorphism in
normal coordinates.  The anchor argument records which sphere-valued
normalized exponential is being charted. -/
def chartOpenPartialHomeomorph (_p : RoundSphere3) :
    OpenPartialHomeomorph E E :=
  coordinateLocalHomeomorph

/-- The inverse-function partial homeomorphism, including its chosen source
and target, is independent of the round-sphere anchor. -/
theorem chartOpenPartialHomeomorph_anchor_independent
    (p q : RoundSphere3) :
    chartOpenPartialHomeomorph p = chartOpenPartialHomeomorph q :=
  rfl

/-- The common partial homeomorphism is exactly the charted normalized
exponential at every anchor. -/
@[simp]
theorem chartOpenPartialHomeomorph_coe (p : RoundSphere3) :
    (chartOpenPartialHomeomorph p : E → E) =
      fun v : E ↦ extChartAt I p (expAt p v) := by
  funext v
  exact (extChartAt_expAt p v).symm

/-- The charted normalized exponential has identity strict derivative at zero
for every target anchor. -/
theorem chart_expAt_hasStrictFDerivAt_zero (p : RoundSphere3) :
    HasStrictFDerivAt
      (fun v : E ↦ extChartAt I p (expAt p v))
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  have href :=
    GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
      (g := roundSphereMetric3) referenceAnchor
  have hfun :
      (fun v : E ↦ extChartAt I p (expAt p v)) =
        (coordinateLocalHomeomorph : E → E) := by
    funext v
    exact extChartAt_expAt p v
  rw [hfun]
  simpa [coordinateLocalHomeomorph,
    GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using href

/-- On the canonical family, the derivative field is literally independent
of the target anchor. -/
theorem fderiv_chart_expAt_eq_coordinateLocalHomeomorph
    (p : RoundSphere3) :
    fderiv ℝ (fun v : E ↦ extChartAt I p (expAt p v)) =
      fderiv ℝ (coordinateLocalHomeomorph : E → E) := by
  congr 1
  funext v
  exact extChartAt_expAt p v

/-- Zero belongs to the common inverse-function source at every anchor. -/
theorem zero_mem_chartOpenPartialHomeomorph_source (p : RoundSphere3) :
    (0 : E) ∈ (chartOpenPartialHomeomorph p).source := by
  exact GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
    (g := roundSphereMetric3) referenceAnchor

/-- Zero belongs to the common inverse-function target at every anchor. -/
theorem zero_mem_chartOpenPartialHomeomorph_target (p : RoundSphere3) :
    (0 : E) ∈ (chartOpenPartialHomeomorph p).target := by
  have hmap := (chartOpenPartialHomeomorph p).map_source
    (zero_mem_chartOpenPartialHomeomorph_source p)
  simpa [chartOpenPartialHomeomorph] using hmap

/-- One positive coordinate ball lies in both the inverse-function source and
target for every round-sphere anchor. -/
theorem exists_uniform_source_target_ball :
    ∃ r > (0 : ℝ), ∀ p : RoundSphere3,
      ball (0 : E) r ⊆ (chartOpenPartialHomeomorph p).source ∧
      ball (0 : E) r ⊆ (chartOpenPartialHomeomorph p).target := by
  let e := coordinateLocalHomeomorph
  have hzeroSource : (0 : E) ∈ e.source := by
    exact GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := roundSphereMetric3) referenceAnchor
  have hzeroTarget : (0 : E) ∈ e.target := by
    have hmap := e.map_source hzeroSource
    simpa [e, coordinateLocalHomeomorph_zero] using hmap
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hzeroSource) with
    ⟨rSource, hrSource, hSource⟩
  rcases Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hzeroTarget) with
    ⟨rTarget, hrTarget, hTarget⟩
  let r : ℝ := min rSource rTarget
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hrSource hrTarget
  refine ⟨r, hr, ?_⟩
  intro p
  constructor
  · intro v hv
    change v ∈ e.source
    exact hSource (Metric.ball_subset_ball (min_le_left _ _) hv)
  · intro v hv
    change v ∈ e.target
    exact hTarget (Metric.ball_subset_ball (min_le_right _ _) hv)

/-- On one anchor-independent ball, both inverse identities hold for every
normalized round-sphere exponential chart. -/
theorem exists_uniform_inverse_equalities :
    ∃ r > (0 : ℝ), ∀ (p : RoundSphere3) (v : E), ‖v‖ < r →
      (chartOpenPartialHomeomorph p).symm
          (extChartAt I p (expAt p v)) = v ∧
        chartOpenPartialHomeomorph p
            ((chartOpenPartialHomeomorph p).symm v) = v := by
  rcases exists_uniform_source_target_ball with ⟨r, hr, hballs⟩
  refine ⟨r, hr, ?_⟩
  intro p v hv
  have hvBall : v ∈ ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hvSource := (hballs p).1 hvBall
  have hvTarget := (hballs p).2 hvBall
  constructor
  · rw [extChartAt_expAt]
    exact (chartOpenPartialHomeomorph p).left_inv hvSource
  · exact (chartOpenPartialHomeomorph p).right_inv hvTarget

/-- The inverse normal coordinate of the normalized exponential equals its
input on one ball, uniformly over all target anchors.  This is the direct
equality-patch form consumed by normal-coordinate arguments. -/
theorem exists_uniform_normalCoordinate_expAt_eq_on_ball :
    ∃ r > (0 : ℝ), ∀ (p : RoundSphere3) (v : E), ‖v‖ < r →
      (chartOpenPartialHomeomorph p).symm
          (extChartAt I p (expAt p v)) = v := by
  rcases exists_uniform_inverse_equalities with ⟨r, hr, h⟩
  exact ⟨r, hr, fun p v hv ↦ (h p v hv).1⟩

end RoundSphereCanonicalExponential
end Poincare
