import Poincare.Global.RoundSphereTargetAnchorUniformity
import Poincare.Global.IsometryInstantiate

/-!
# A fixed-anchor cutoff radius uniform over tangent alignments

For a fixed source anchor, the source exponential chart is independent of the
tangent alignment.  On the round-sphere target, every stereographic chart has
target `univ`, so canonical blending makes the chosen cutoff identically one.
The target cutoff-one locus is therefore all of model space, simultaneously
for every target anchor and tangent alignment; no target-chart continuity or
operator-norm shrink is needed for this cutoff package.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

universe u

namespace RoundSphereTargetAnchorUniformity

local notation "E" => ClosedSmoothModel 3

/-- The cutoff-one locus of every round-sphere target chart is the whole model
space. -/
theorem cutoffOneLocus_roundSphere_eq_univ (p₀ : RoundSphere3) :
    IsometryInstantiate.cutoffOneLocus p₀ = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    change ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := 3) p₀ z' = 1
    exact Filter.Eventually.of_forall fun z' =>
      congrFun (cutoff_roundSphere_eq_one p₀) z'

end RoundSphereTargetAnchorUniformity

namespace CartanMap

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The source cutoff-one preimage contains a positive normal-coordinate ball.
This radius is independent of the alignment because the source exponential
chart is fixed. -/
theorem exists_source_cutoffOneLocus_preimage_ball
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ v ∈
        IsometryInstantiate.cutoffOneLocus x₀ := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have heM_cont : ContinuousAt (eM : E → E) 0 := by
    simpa [eM, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
      GeodesicTransport.expAt_chart_continuousAt_zero (g := g) (x₀ := x₀)
  have heM₀ : eM (0 : E) = extChartAt I x₀ x₀ := by
    simp [eM, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
      GeodesicTransport.expAt_zero]
  have hpreimage :
      eM ⁻¹' IsometryInstantiate.cutoffOneLocus x₀ ∈ nhds (0 : E) := by
    apply heM_cont.preimage_mem_nhds
    rw [heM₀]
    exact IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x₀
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨r, hr, hrsub⟩
  refine ⟨r, hr, ?_⟩
  intro v hv
  apply hrsub
  simpa only [mem_ball, dist_eq_norm, sub_zero] using hv

/-- One positive normal-coordinate radius works for every round-sphere target
anchor and every tangent alignment, because every target cutoff-one locus is
the whole model space. -/
theorem exists_uniform_target_cutoffOneLocus_preimage_ball_all_targets
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ r > (0 : ℝ), ∀ (p₀ : RoundSphere3)
      (L : TangentAlignment g x₀ p₀) (v : E),
      ‖v‖ < r →
        GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀ (L v) ∈
          IsometryInstantiate.cutoffOneLocus p₀ := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro p₀ _L _v _hv
  rw [RoundSphereTargetAnchorUniformity.cutoffOneLocus_roundSphere_eq_univ]
  exact Set.mem_univ _

/-- Fixed-target specialization of the all-target cutoff-one radius. -/
theorem exists_uniform_target_cutoffOneLocus_preimage_ball
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ L : TangentAlignment g x₀ p₀, ∀ v : E,
      ‖v‖ < r →
        GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀ (L v) ∈
          IsometryInstantiate.cutoffOneLocus p₀ := by
  rcases exists_uniform_target_cutoffOneLocus_preimage_ball_all_targets g x₀ with
    ⟨r, hr, hall⟩
  exact ⟨r, hr, hall p₀⟩

/-- One positive radius simultaneously puts the source and every aligned
target exponential image in their fixed-anchor cutoff-one loci. -/
theorem exists_uniform_source_target_cutoffOneLocus_preimage_ball
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3) :
    ∃ r > (0 : ℝ), ∀ L : TangentAlignment g x₀ p₀, ∀ v : E,
      ‖v‖ < r →
        GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ v ∈
            IsometryInstantiate.cutoffOneLocus x₀ ∧
          GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀ (L v) ∈
            IsometryInstantiate.cutoffOneLocus p₀ := by
  rcases exists_source_cutoffOneLocus_preimage_ball g x₀ with ⟨rS, hrS, hS⟩
  rcases exists_uniform_target_cutoffOneLocus_preimage_ball g x₀ p₀ with
    ⟨rT, hrT, hT⟩
  refine ⟨min rS rT, lt_min hrS hrT, ?_⟩
  intro L v hv
  constructor
  · exact hS v (hv.trans_le (min_le_left _ _))
  · exact hT L v (hv.trans_le (min_le_right _ _))

end CartanMap
end Poincare
