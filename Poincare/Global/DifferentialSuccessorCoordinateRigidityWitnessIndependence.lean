import Poincare.Global.DifferentialSuccessorCoordinateRigidityReduction

/-!
# Witness-independent coordinate rigidity for differential successors

The complete `DifferentialInducedSuccessor.Data` structure contains choices of
strict-derivative witnesses.  Those choices do not create an additional
compactness problem for coordinate rigidity: at a fixed predecessor state and
successor anchor, the stored normal vector, induced alignment, and successor
state are already proved unique.

This file records the resulting quantifier commutation.  For fixed source and
target anchors, the two positive output radii may be selected after the
alignment and successor anchor but before *all* actual `Data` witnesses.  It
also separates the evaluation-variable side conditions into an explicit
neighborhood locus.  Consequently, no topology on the dependent `Data` type
is needed; the remaining uniformity problem lies only in the moving
source/target anchors, tangent alignment, and successor anchor.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorCoordinateRigidityWitnessIndependence

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

open DifferentialSuccessorCoordinateRigidityReduction
open DifferentialSuccessorIntervalNaturality

/-! ## The open evaluation locus -/

/-- The evaluation-variable side conditions in coordinate rigidity, with the
exponential-naturality identity deliberately omitted.

The locus depends on a `Data` witness only through its successor state.  The
theorems below show that even this apparent dependency is witness-independent.
-/
def ActualSuccessorCoordinateControlLocus
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (normalRadius : ℝ) : Set M :=
  {q : M |
    q ∈ s.germ.source ∩ d.successor.germ.source ∧
      s.map q ∈ (extChartAt I (s.map z)).source ∧
        ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) z).symm ((chartAt E z) q)‖ < normalRadius}

/-- Every positive normal radius makes the exact coordinate-control locus a
neighborhood of the actual successor anchor.

This is the open-locus continuation statement strictly below the three-radius
contract: it contains no exponential-naturality conclusion and selects no
ordinary metric output radius. -/
theorem actualSuccessorCoordinateControlLocus_mem_nhds
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {normalRadius : ℝ} (hnormalRadius : 0 < normalRadius) :
    ActualSuccessorCoordinateControlLocus g s d normalRadius ∈ 𝓝 z := by
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
  filter_upwards [hsources, hmapNew, hnormalSmall] with
    q hsource hmap hnormal
  exact ⟨hsource, hmap, by simpa [eM] using hnormal⟩

/-- Open-set form of the coordinate-control neighborhood.  This avoids
choosing a metric radius until a downstream consumer actually needs one. -/
theorem exists_open_actualSuccessorCoordinateControlNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {normalRadius : ℝ} (hnormalRadius : 0 < normalRadius) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      V ⊆ ActualSuccessorCoordinateControlLocus
        g s d normalRadius := by
  letI : MetricSpace M := g.toMetricSpace
  rcases _root_.mem_nhds_iff.mp
      (actualSuccessorCoordinateControlLocus_mem_nhds
        g s d hnormalRadius) with
    ⟨V, hVsub, hVopen, hzV⟩
  exact ⟨V, hVopen, hzV, hVsub⟩

/-- The three-radius predicate is exactly exponential naturality together
with containment of its ordinary output ball in the open control locus. -/
theorem actualSuccessorCoordinateRigidityOnBall_iff_controlLocus
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (normalRadius outputRadius : ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    ActualSuccessorCoordinateRigidityOnBall
        g s d normalRadius outputRadius ↔
      ( (∀ v : E, ‖v‖ < normalRadius →
          DifferentialInducedSuccessor.reanchoredChartMap s z
              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) z v) =
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (s.map z) (d.alignment v)) ∧
        Metric.ball z outputRadius ⊆
          ActualSuccessorCoordinateControlLocus
            g s d normalRadius) := by
  letI : MetricSpace M := g.toMetricSpace
  rfl

/-! ## Independence from derivative-field witnesses -/

/-- The coordinate-control locus is independent of the chosen actual
differential-successor witness. -/
theorem actualSuccessorCoordinateControlLocus_congr_data
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d₁ d₂ : DifferentialInducedSuccessor.Data s z)
    (normalRadius : ℝ) :
    ActualSuccessorCoordinateControlLocus g s d₁ normalRadius =
      ActualSuccessorCoordinateControlLocus g s d₂ normalRadius := by
  unfold ActualSuccessorCoordinateControlLocus
  rw [d₁.successor_eq d₂]

/-- Coordinate rigidity on fixed balls is independent of the chosen actual
differential-successor witness. -/
theorem actualSuccessorCoordinateRigidityOnBall_congr_data
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d₁ d₂ : DifferentialInducedSuccessor.Data s z)
    (normalRadius outputRadius : ℝ) :
    ActualSuccessorCoordinateRigidityOnBall
        g s d₁ normalRadius outputRadius ↔
      ActualSuccessorCoordinateRigidityOnBall
        g s d₂ normalRadius outputRadius := by
  letI : MetricSpace M := g.toMetricSpace
  unfold ActualSuccessorCoordinateRigidityOnBall
  rw [d₁.alignment_eq d₂, d₁.successor_eq d₂]

/-- Once one actual witness has a naturality ball, a single positive ordinary
output radius works for every actual witness at the same predecessor and
successor anchor. -/
theorem exists_actualSuccessorCoordinateRigidityOnBall_all_data
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {z : M}
    (d₀ : DifferentialInducedSuccessor.Data s z)
    {normalRadius : ℝ} (hnormalRadius : 0 < normalRadius)
    (hnaturality : ∀ v : E, ‖v‖ < normalRadius →
      DifferentialInducedSuccessor.reanchoredChartMap s z
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) z v) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map z) (d₀.alignment v)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ outputRadius > (0 : ℝ),
      ∀ d : DifferentialInducedSuccessor.Data s z,
        ActualSuccessorCoordinateRigidityOnBall
          g s d normalRadius outputRadius := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_actualSuccessorCoordinateRigidityOnBall
      g s d₀ hnormalRadius hnaturality with
    ⟨outputRadius, houtputRadius, hrigidity⟩
  refine ⟨outputRadius, houtputRadius, ?_⟩
  intro d
  exact
    (actualSuccessorCoordinateRigidityOnBall_congr_data
      d₀ d normalRadius outputRadius).mp hrigidity

/-- The fixed-three-radii predicate with the zero/nonzero split moved ahead
of all actual `Data` witnesses. -/
def ActualSuccessorCoordinateRigidityDataIndependentRadiiAdmissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (inputRadius normalRadius outputRadius : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
    dist z x < inputRadius →
      (∀ d : DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk x p L) z, d.v = 0) ∨
        ∀ d : DifferentialInducedSuccessor.Data
            (CartanChain.ChainState.mk x p L) z,
          ActualSuccessorCoordinateRigidityOnBall
            g (CartanChain.ChainState.mk x p L) d
              normalRadius outputRadius

/-- At fixed radii, moving the disjunction and actual-data quantifier changes
no content. -/
theorem actualSuccessorCoordinateRigidityRadiiAdmissible_iff_dataIndependent
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3)
    (inputRadius normalRadius outputRadius : ℝ) :
    ActualSuccessorCoordinateRigidityRadiiAdmissible
        g x p inputRadius normalRadius outputRadius ↔
      ActualSuccessorCoordinateRigidityDataIndependentRadiiAdmissible
        g x p inputRadius normalRadius outputRadius := by
  letI : MetricSpace M := g.toMetricSpace
  constructor
  · classical
    intro hrigidity L z hzx
    by_cases hdata : Nonempty
        (DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk x p L) z)
    · let d₀ := Classical.choice hdata
      rcases hrigidity L z d₀ hzx with hzero | hcoordinate
      · left
        intro d
        exact (d.vector_eq d₀).trans hzero
      · right
        intro d
        exact
          (actualSuccessorCoordinateRigidityOnBall_congr_data
            d₀ d normalRadius outputRadius).mp hcoordinate
    · left
      intro d
      exact (hdata ⟨d⟩).elim
  · intro hrigidity L z d hzx
    rcases hrigidity L z hzx with hzero | hcoordinate
    · exact Or.inl (hzero d)
    · exact Or.inr (hcoordinate d)

/-- Locally uniform coordinate rigidity stated without any apparent topology
or radius dependence on the actual derivative-field witness. -/
def ActualSuccessorCoordinateRigidityDataIndependentLocalUniformity
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ xp : M × RoundSphere3,
    ∃ inputRadius > (0 : ℝ),
      ∃ normalRadius > (0 : ℝ),
        ∃ outputRadius > (0 : ℝ),
          ∀ᶠ yq in 𝓝 xp,
            ActualSuccessorCoordinateRigidityDataIndependentRadiiAdmissible
              g yq.1 yq.2 inputRadius normalRadius outputRadius

/-- The repository's locally uniform coordinate-rigidity boundary is exactly
its witness-independent formulation.  Hence the unresolved uniformity cannot
be attributed to the proof-bearing fields of `Data`. -/
theorem actualSuccessorCoordinateRigidityLocalUniformity_iff_dataIndependent
    (g : ClosedSmoothRiemannianMetric 3 M) :
    ActualSuccessorCoordinateRigidityLocalUniformity g ↔
      ActualSuccessorCoordinateRigidityDataIndependentLocalUniformity g := by
  constructor
  · intro hrigidity xp
    rcases hrigidity xp with
      ⟨inputRadius, hinputRadius,
        normalRadius, hnormalRadius,
        outputRadius, houtputRadius, hlocal⟩
    refine
      ⟨inputRadius, hinputRadius,
        normalRadius, hnormalRadius,
        outputRadius, houtputRadius, ?_⟩
    filter_upwards [hlocal] with yq hyq
    exact
      (actualSuccessorCoordinateRigidityRadiiAdmissible_iff_dataIndependent
        g yq.1 yq.2 inputRadius normalRadius outputRadius).mp hyq
  · intro hrigidity xp
    rcases hrigidity xp with
      ⟨inputRadius, hinputRadius,
        normalRadius, hnormalRadius,
        outputRadius, houtputRadius, hlocal⟩
    refine
      ⟨inputRadius, hinputRadius,
        normalRadius, hnormalRadius,
        outputRadius, houtputRadius, ?_⟩
    filter_upwards [hlocal] with yq hyq
    exact
      (actualSuccessorCoordinateRigidityRadiiAdmissible_iff_dataIndependent
        g yq.1 yq.2 inputRadius normalRadius outputRadius).mpr hyq

/-! ## Exact fixed-anchor quantifier commutation -/

/-- Fixed-anchor pointwise coordinate rigidity with all actual `Data`
witnesses placed after the two output radii.

If no actual data exist the zero branch is vacuous.  If data do exist, their
stored vector is unique, so the zero/nonzero split and both rigidity radii are
independent of the witness. -/
def FixedAnchorDataIndependentActualSuccessorCoordinateRigidity
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ inputRadius > (0 : ℝ),
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
      dist z x < inputRadius →
        (∀ d : DifferentialInducedSuccessor.Data
            (CartanChain.ChainState.mk x p L) z, d.v = 0) ∨
          ∃ normalRadius > (0 : ℝ),
            ∃ outputRadius > (0 : ℝ),
              ∀ d : DifferentialInducedSuccessor.Data
                  (CartanChain.ChainState.mk x p L) z,
                ActualSuccessorCoordinateRigidityOnBall
                  g (CartanChain.ChainState.mk x p L) d
                    normalRadius outputRadius

/-- Moving the `Data` quantifier across the two output-radius choices changes
no mathematical content.  In particular, a topology on the dependent
successor-data type cannot help with the remaining radius problem because
that dependency has already disappeared propositionally. -/
theorem fixedAnchorDataIndependentActualSuccessorCoordinateRigidity_iff
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) :
    FixedAnchorDataIndependentActualSuccessorCoordinateRigidity g x p ↔
      FixedAnchorPointwiseActualSuccessorCoordinateRigidity g x p := by
  letI : MetricSpace M := g.toMetricSpace
  constructor
  · rintro ⟨inputRadius, hinputRadius, hrigidity⟩
    refine ⟨inputRadius, hinputRadius, ?_⟩
    intro L z d hzx
    rcases hrigidity L z hzx with hzero | hcoordinate
    · exact Or.inl (hzero d)
    · rcases hcoordinate with
        ⟨normalRadius, hnormalRadius,
          outputRadius, houtputRadius, hcoordinate⟩
      exact Or.inr
        ⟨normalRadius, hnormalRadius,
          outputRadius, houtputRadius, hcoordinate d⟩
  · classical
    rintro ⟨inputRadius, hinputRadius, hrigidity⟩
    refine ⟨inputRadius, hinputRadius, ?_⟩
    intro L z hzx
    by_cases hdata : Nonempty
        (DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk x p L) z)
    · let d₀ := Classical.choice hdata
      rcases hrigidity L z d₀ hzx with hzero | hcoordinate
      · left
        intro d
        exact (d.vector_eq d₀).trans hzero
      · right
        rcases hcoordinate with
          ⟨normalRadius, hnormalRadius,
            outputRadius, houtputRadius, hcoordinate⟩
        refine
          ⟨normalRadius, hnormalRadius,
            outputRadius, houtputRadius, ?_⟩
        intro d
        exact
          (actualSuccessorCoordinateRigidityOnBall_congr_data
            d₀ d normalRadius outputRadius).mp hcoordinate
    · left
      intro d
      exact (hdata ⟨d⟩).elim

/-- Constant curvature proves the witness-independent fixed-anchor package.
The only radii still selected late are indexed by the alignment and successor
anchor, never by a derivative-field witness. -/
theorem fixedAnchorDataIndependentActualSuccessorCoordinateRigidity_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    FixedAnchorDataIndependentActualSuccessorCoordinateRigidity g x p := by
  exact
    (fixedAnchorDataIndependentActualSuccessorCoordinateRigidity_iff
      g x p).mpr
      (fixedAnchorPointwiseActualSuccessorCoordinateRigidity_of_constantCurvature
        g hcurv x p)

end DifferentialSuccessorCoordinateRigidityWitnessIndependence
end Poincare
