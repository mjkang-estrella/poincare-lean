import Poincare.Global.ExponentialLocalHomeo
import Poincare.Global.MetricCompleteness
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Uniform normal neighborhoods on compact manifolds

The per-anchor exponential map gives an open normal-coordinate image around
each anchor.  Compactness uniformizes this cover in the Lebesgue-number sense:
there is one metric radius such that every ball of that radius is contained in
some normal-coordinate image.  The anchor of that image is not forced to be the
center of the metric ball; compactness of an arbitrary pointwise neighborhood
family does not provide that stronger continuity-in-anchor statement.
-/

noncomputable section

open Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

/-- A chosen per-anchor radius on which the fixed-time exponential is a normal chart image. -/
def normalCoordinateRadius (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : ℝ :=
  Classical.choose (expAt_injective_open_image_smallBall (g := g) x₀)

theorem normalCoordinateRadius_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    0 < normalCoordinateRadius g x₀ := by
  simpa [normalCoordinateRadius] using
    (Classical.choose_spec (expAt_injective_open_image_smallBall (g := g) x₀)).1

/-- The chosen normal-coordinate image at an anchor. -/
def normalCoordinateImage (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : Set M :=
  expAt g x₀ '' Metric.ball (0 : E) (normalCoordinateRadius g x₀)

theorem injOn_expAt_normalCoordinateRadius
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    InjOn (expAt g x₀) (Metric.ball (0 : E) (normalCoordinateRadius g x₀)) := by
  simpa [normalCoordinateRadius] using
    (Classical.choose_spec (expAt_injective_open_image_smallBall (g := g) x₀)).2.1

theorem isOpen_normalCoordinateImage
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    IsOpen (normalCoordinateImage g x₀) := by
  simpa [normalCoordinateImage, normalCoordinateRadius] using
    (Classical.choose_spec (expAt_injective_open_image_smallBall (g := g) x₀)).2.2.1

theorem normalCoordinateImage_mem_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    normalCoordinateImage g x₀ ∈ 𝓝 x₀ := by
  simpa [normalCoordinateImage, normalCoordinateRadius] using
    (Classical.choose_spec (expAt_injective_open_image_smallBall (g := g) x₀)).2.2.2

theorem mem_normalCoordinateImage_self
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    x₀ ∈ normalCoordinateImage g x₀ := by
  refine ⟨0, Metric.mem_ball_self (normalCoordinateRadius_pos g x₀), ?_⟩
  simp [expAt_zero]

/--
Uniform Lebesgue-number form of compactness for the cover by normal-coordinate
images.  For every center `x`, its radius-`r` metric ball is contained in a
normal-coordinate image, possibly anchored at another point.
-/
theorem exists_uniform_ball_subset_normalCoordinateImage
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), ∀ x : M, ∃ x₀ : M,
      Metric.ball x r ⊆ normalCoordinateImage g x₀ := by
  letI : MetricSpace M := g.toMetricSpace
  rcases lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set M)) (c := normalCoordinateImage g)
      isCompact_univ
      (fun x₀ => isOpen_normalCoordinateImage g x₀)
      (by
        intro x hx
        exact mem_iUnion.2 ⟨x, mem_normalCoordinateImage_self g x⟩) with
    ⟨r, hr_pos, hr_sub⟩
  refine ⟨r, hr_pos, ?_⟩
  intro x
  simpa using hr_sub x (Set.mem_univ x)

/--
Every pair of points closer than the uniform radius lies in one common
normal-coordinate image.
-/
theorem exists_uniform_common_normalCoordinateImage_of_dist_lt
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), ∀ x y : M, dist x y < r →
      ∃ x₀ : M,
        x ∈ normalCoordinateImage g x₀ ∧
          y ∈ normalCoordinateImage g x₀ := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_ball_subset_normalCoordinateImage (g := g) with
    ⟨r, hr_pos, hr_ball⟩
  refine ⟨r, hr_pos, ?_⟩
  intro x y hxy
  rcases hr_ball x with ⟨x₀, hx₀⟩
  refine ⟨x₀, hx₀ (Metric.mem_ball_self hr_pos), hx₀ ?_⟩
  simpa [Metric.mem_ball, dist_comm] using hxy

end GeodesicTransport
end Poincare
