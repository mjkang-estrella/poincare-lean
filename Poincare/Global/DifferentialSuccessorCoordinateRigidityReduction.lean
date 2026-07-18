import Poincare.Global.DifferentialSuccessorEqualityStabilityReduction

/-!
# Coordinate rigidity below actual-successor equality stability

Constant curvature and closed-interval geodesic uniqueness already give one
predecessor radius, uniform over fixed source/target anchors and tangent
alignments.  After an actual successor datum is selected, they give a positive
new-anchor normal radius on which the re-centered predecessor chart satisfies
the exponential naturality identity.  Elementary continuity then gives a
positive metric ball on which all source, target-chart, and normal-coordinate
side conditions hold.

The two output radii are still selected after the actual datum.  Compactness
does not reverse that quantifier order because the repository has no topology
on moving differential-successor data, nor joint regularity for the generic
source exponential family.  This file therefore isolates the exact next
geometric input without introducing such a topology: the same three radii
must work locally in `(x,p)`, universally over alignments and actual data.
That coordinate contract contains no germ-equality conclusion, and the
existing exponential-naturality consumer turns it into the locally persistent
equality-radius contract.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorCoordinateRigidityReduction

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

open DifferentialSuccessorAdaptiveMeshCoordinates
open DifferentialSuccessorEqualityStabilityReduction
open DifferentialSuccessorIntervalNaturality

/-- Coordinate-level rigidity for one actual successor on one metric ball.

The first clause is the closed-interval exponential naturality identity in a
new-anchor normal ball.  The second clause says that an ordinary metric ball
lies in both strict germ sources, that the predecessor value stays in the new
target chart, and that the new normal coordinate stays in the normal ball.
No equality of the predecessor and successor germs is assumed. -/
def ActualSuccessorCoordinateRigidityOnBall
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (normalRadius outputRadius : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  (∀ v : E, ‖v‖ < normalRadius →
    DifferentialInducedSuccessor.reanchoredChartMap s z
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) z v) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) (s.map z) (d.alignment v)) ∧
    ∀ q ∈ Metric.ball z outputRadius,
      q ∈ s.germ.source ∩ d.successor.germ.source ∧
        s.map q ∈ (extChartAt I (s.map z)).source ∧
          ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) z).symm ((chartAt E z) q)‖ < normalRadius

/-- Any positive exponential-naturality radius has a positive metric ball on
which all coordinate side conditions required by the equality consumer hold.

This is a pointwise topology argument only.  Its output radius may depend on
the predecessor state, successor anchor, and actual datum. -/
theorem exists_actualSuccessorCoordinateRigidityOnBall
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {normalRadius : ℝ} (hnormalRadius : 0 < normalRadius)
    (hnaturality : ∀ v : E, ‖v‖ < normalRadius →
      DifferentialInducedSuccessor.reanchoredChartMap s z
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) z v) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map z) (d.alignment v)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ outputRadius > (0 : ℝ),
      ActualSuccessorCoordinateRigidityOnBall
        g s d normalRadius outputRadius := by
  letI : MetricSpace M := g.toMetricSpace
  have hzOld : z ∈ s.germ.source := d.anchor_mem_predecessor_source
  have hzNew : z ∈ d.successor.germ.source := by
    simpa [DifferentialInducedSuccessor.Data.successor] using
      CartanAdjacentContinuation.chainAdjacent_anchor_mem_successor_source
        s z d.alignment
  have hsources :
      s.germ.source ∩ d.successor.germ.source ∈ 𝓝 z :=
    (s.germ.open_source.inter d.successor.germ.open_source).mem_nhds
      ⟨hzOld, hzNew⟩
  have hsourcesEventually : ∀ᶠ q in 𝓝 z,
      q ∈ s.germ.source ∩ d.successor.germ.source :=
    hsources
  have hsContinuous : ContinuousAt s.map z := by
    change ContinuousAt s.germ z
    exact s.germ.continuousOn.continuousAt
      (s.germ.open_source.mem_nhds hzOld)
  have hmapNew : ∀ᶠ q in 𝓝 z,
      s.map q ∈ (extChartAt I (s.map z)).source :=
    hsContinuous.preimage_mem_nhds
      ((isOpen_extChartAt_source (s.map z)).mem_nhds
        (mem_extChartAt_source (s.map z)))
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) z
  have hzeroSource : (0 : E) ∈ eM.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) z
  have hzeroTarget : eM (0 : E) ∈ eM.target :=
    eM.map_source hzeroSource
  have heMzero : eM (0 : E) = extChartAt I z z := by
    change GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) z (0 : E) = (chartAt E z) z
    exact CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor g z
  have hnormalContinuous : ContinuousAt
      (fun q : M ↦ eM.symm (extChartAt I z q)) z := by
    have heContinuous : ContinuousAt eM.symm (extChartAt I z z) := by
      rw [← heMzero]
      exact eM.continuousAt_symm hzeroTarget
    simpa [Function.comp_def] using
      heContinuous.comp (continuousAt_extChartAt z)
  have hnormalAnchor : eM.symm (extChartAt I z z) = (0 : E) := by
    rw [← heMzero]
    exact eM.left_inv hzeroSource
  have hnormalSmall : ∀ᶠ q in 𝓝 z,
      ‖eM.symm ((chartAt E z) q)‖ < normalRadius := by
    have hballN : Metric.ball (0 : E) normalRadius ∈
        𝓝 (eM.symm (extChartAt I z z)) := by
      rw [hnormalAnchor]
      exact Metric.ball_mem_nhds (0 : E) hnormalRadius
    have hmem := hnormalContinuous.eventually hballN
    simpa only [extChartAt_coe, Metric.mem_ball, dist_eq_norm,
      sub_zero] using hmem
  have hgood :
      {q : M |
        q ∈ s.germ.source ∩ d.successor.germ.source ∧
          s.map q ∈ (extChartAt I (s.map z)).source ∧
            ‖eM.symm ((chartAt E z) q)‖ < normalRadius} ∈ 𝓝 z := by
    filter_upwards [hsourcesEventually, hmapNew, hnormalSmall] with
      q hsource hmap hnormal
    exact ⟨hsource, hmap, hnormal⟩
  rcases Metric.mem_nhds_iff.mp hgood with
    ⟨outputRadius, houtputRadius, hball⟩
  refine ⟨outputRadius, houtputRadius, hnaturality, ?_⟩
  intro q hq
  have hcontrol := hball hq
  exact ⟨hcontrol.1, hcontrol.2.1, by
    simpa only [eM] using hcontrol.2.2⟩

/-- The pointwise coordinate-rigidity output of constant curvature at fixed
source/target anchors.

The input metric radius precedes `L`, `z`, and `d`.  For a nonzero actual
datum, both output radii are selected afterward.  A zero datum is separated
because its successor is algebraically identical to its predecessor. -/
def FixedAnchorPointwiseActualSuccessorCoordinateRigidity
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ inputRadius > (0 : ℝ),
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk x p L) z),
      dist z x < inputRadius →
        d.v = 0 ∨
          ∃ normalRadius > (0 : ℝ),
            ∃ outputRadius > (0 : ℝ),
              ActualSuccessorCoordinateRigidityOnBall
                g (CartanChain.ChainState.mk x p L) d
                  normalRadius outputRadius

/-- Constant curvature proves every pointwise coordinate-rigidity package
without placing a topology on actual successor data. -/
theorem fixedAnchorPointwiseActualSuccessorCoordinateRigidity_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    FixedAnchorPointwiseActualSuccessorCoordinateRigidity g x p := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      DifferentialSuccessorIntervalNaturality.exists_uniform_reanchoredChartMap_expAtChart_naturality_ball
        g hcurv x p with
    ⟨normalInputRadius, hnormalInputRadius, hnaturality⟩
  let anchor : Unit → M := fun _ ↦ x
  rcases
      exists_uniform_distance_radius_for_finite_anchors
        (g := g) anchor hnormalInputRadius with
    ⟨inputRadius, hinputRadius, hcoordinate⟩
  refine ⟨inputRadius, hinputRadius, ?_⟩
  intro L z d hzx
  by_cases hdzero : d.v = 0
  · exact Or.inl hdzero
  · right
    have hdSmall : ‖d.v‖ < normalInputRadius := by
      exact hcoordinate ()
        (CartanChain.ChainState.mk x p L) (by simp [anchor]) d
        (by simpa [anchor] using hzx)
    rcases hnaturality L d hdSmall hdzero with
      ⟨normalRadius, hnormalRadius, hnormalNaturality⟩
    rcases exists_actualSuccessorCoordinateRigidityOnBall
        g (CartanChain.ChainState.mk x p L) d
        hnormalRadius hnormalNaturality with
      ⟨outputRadius, houtputRadius, hcoordinateBall⟩
    exact
      ⟨normalRadius, hnormalRadius,
        outputRadius, houtputRadius, hcoordinateBall⟩

/-- Three radii give coordinate rigidity uniformly over every actual
successor based at one source-target pair.

This predicate still contains no predecessor/successor equality assertion.
It asks only for the precise exponential identity and coordinate-domain
controls consumed by
`predecessor_germ_eq_successor_germ_of_expAtChart_norm_lt`. -/
def ActualSuccessorCoordinateRigidityRadiiAdmissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (inputRadius normalRadius outputRadius : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : DifferentialInducedSuccessor.Data
      (CartanChain.ChainState.mk x p L) z),
    dist z x < inputRadius →
      d.v = 0 ∨
        ActualSuccessorCoordinateRigidityOnBall
          g (CartanChain.ChainState.mk x p L) d
            normalRadius outputRadius

/-- The narrow locally uniform source/injectivity/rigidity contract.

At every `(x,p)`, one input radius, one normal naturality radius, and one
ordinary output-ball radius remain valid at all nearby source-target pairs.
Alignments and actual successor data stay under universal quantifiers, so no
topology on their dependent spaces is introduced. -/
def ActualSuccessorCoordinateRigidityLocalUniformity
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ xp : M × RoundSphere3,
    ∃ inputRadius > (0 : ℝ),
      ∃ normalRadius > (0 : ℝ),
        ∃ outputRadius > (0 : ℝ),
          ∀ᶠ yq in 𝓝 xp,
            ActualSuccessorCoordinateRigidityRadiiAdmissible
              g yq.1 yq.2 inputRadius normalRadius outputRadius

/-- Locally uniform coordinate rigidity closes the exact equality-radius
local-persistence boundary. -/
theorem actualSuccessorEqualityRadiusLocalPersistence_of_coordinateRigidity
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hrigidity : ActualSuccessorCoordinateRigidityLocalUniformity g) :
    ActualSuccessorEqualityRadiusLocalPersistence g := by
  letI : MetricSpace M := g.toMetricSpace
  intro xp
  rcases hrigidity xp with
    ⟨inputRadius, hinputRadius,
      normalRadius, _hnormalRadius,
      outputRadius, houtputRadius, hlocal⟩
  let radius : ℝ := min inputRadius outputRadius
  have hradius : 0 < radius := lt_min hinputRadius houtputRadius
  refine ⟨radius, hradius, ?_⟩
  filter_upwards [hlocal] with yq hyq
  intro L z d hzx
  rcases hyq L z d
      (hzx.trans_le (by
        dsimp only [radius]
        exact min_le_left _ _)) with
    hdzero | hcoordinate
  · have hsuccessor :
        d.successor = CartanChain.ChainState.mk yq.1 yq.2 L :=
      DifferentialSuccessorZero.successor_eq_of_vector_eq_zero d hdzero
    rw [hsuccessor]
    intro q hq
    rfl
  · intro q hq
    have hqOutput : q ∈ Metric.ball z outputRadius :=
      Metric.ball_subset_ball (by
        dsimp only [radius]
        exact min_le_right _ _) hq
    have hcontrol := hcoordinate.2 q hqOutput
    exact
      predecessor_germ_eq_successor_germ_of_expAtChart_norm_lt
        (CartanChain.ChainState.mk yq.1 yq.2 L) d
        hcoordinate.1 hcontrol.1 hcontrol.2.1 hcontrol.2.2

/-- The coordinate contract therefore gives the raw uniform equality ball by
the lower-semicontinuous compactness reduction. -/
theorem uniformActualSuccessorEquality_of_coordinateRigidity
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hrigidity : ActualSuccessorCoordinateRigidityLocalUniformity g) :
    UniformActualSuccessorEquality g := by
  exact
    uniformActualSuccessorEquality_of_localPersistence g
      (actualSuccessorEqualityRadiusLocalPersistence_of_coordinateRigidity
        g hrigidity)

end DifferentialSuccessorCoordinateRigidityReduction
end Poincare
