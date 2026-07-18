import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates

/-!
# Finite-anchor metric radii for differential successors

The fixed-anchor interval-naturality theorem selects one predecessor normal
radius before the tangent alignment and successor datum.  A finite minimum
makes that input radius uniform over a finite family of source and target
anchors, while continuity of the source normal coordinate converts it into a
metric-distance bound.

The equality neighborhood produced after a successor datum is known remains
datum-dependent.  This file preserves that quantifier order explicitly.  For
a finite family of actual data, and only after those data have been fixed, a
second finite minimum gives one common positive equality-ball radius.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorFiniteAnchorRadius

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdaptiveMeshCoordinates

/-- An open local equality seed at a differential-successor anchor contains
a positive metric ball on which the predecessor and successor germs agree.

The source intersection in the seed causes no loss: the successor anchor
belongs to the predecessor source by the data package and to the successor
source by construction. -/
private theorem exists_metricBall_eqOn_of_open_local_eqOn
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {V : Set M} (hVopen : IsOpen V) (hzV : z ∈ V)
    (hEq : EqOn s.germ d.successor.germ
      (V ∩ (s.germ.source ∩ d.successor.germ.source))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ),
      EqOn s.germ d.successor.germ (Metric.ball z r) := by
  letI : MetricSpace M := g.toMetricSpace
  have hzOld : z ∈ s.germ.source := d.anchor_mem_predecessor_source
  have hzNew : z ∈ d.successor.germ.source := by
    simpa [DifferentialInducedSuccessor.Data.successor] using
      CartanAdjacentContinuation.chainAdjacent_anchor_mem_successor_source
        s z d.alignment
  have hopen : IsOpen
      (V ∩ (s.germ.source ∩ d.successor.germ.source)) :=
    hVopen.inter (s.germ.open_source.inter d.successor.germ.open_source)
  have hz : z ∈ V ∩ (s.germ.source ∩ d.successor.germ.source) :=
    ⟨hzV, hzOld, hzNew⟩
  rcases (Metric.isOpen_iff.mp hopen) z hz with ⟨r, hr, hball⟩
  exact ⟨r, hr, fun _q hq ↦ hEq (hball hq)⟩

/-- For finitely many fixed source/target anchor pairs, one positive metric
distance bound is selected before the family member, tangent alignment, and
successor datum.  Every datum based inside that distance has a positive
metric equality ball, whose radius may honestly depend on the datum.

This is the strongest direct finite-anchor approximation to a
state-uniform successor-ball theorem available from the current local
naturality API: `epsilon` is uniform, but `r` remains inside the quantifiers
for `L` and `d`. -/
theorem exists_uniform_distance_radius_with_datum_eqOn_ball_on_finite_family
    [CompactSpace M] [ConnectedSpace M]
    {iota : Type v} [Fintype iota] [Nonempty iota]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : iota → M) (p : iota → RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (i : iota) (L : CartanMap.TangentAlignment g (x i) (p i)),
        ∀ {z : M}
          (d : DifferentialInducedSuccessor.Data
            (CartanChain.ChainState.mk (x i) (p i) L) z),
          dist z (x i) < epsilon →
            ∃ r > (0 : ℝ),
              EqOn (CartanChain.ChainState.mk (x i) (p i) L).germ
                d.successor.germ (Metric.ball z r) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      DifferentialSuccessorIntervalNaturalityFiniteFamily.exists_uniform_local_eqOn_differentialSuccessor_all_on_finite_family
        g hcurv x p with
    ⟨rho, hrho, hlocal⟩
  rcases exists_uniform_distance_radius_for_finite_anchors
      (g := g) x hrho with
    ⟨epsilon, hepsilon, hcoordinate⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro i L z d hdist
  let s : CartanChain.ChainState g :=
    CartanChain.ChainState.mk (x i) (p i) L
  have hdSmall : ‖d.v‖ < rho := by
    exact hcoordinate i s rfl d (by simpa [s] using hdist)
  rcases hlocal i L d hdSmall with ⟨V, hVopen, hzV, hEq⟩
  exact exists_metricBall_eqOn_of_open_local_eqOn
    s d hVopen hzV (by simpa [s] using hEq)

/-- Once a finite family of actual differential-successor data has been
fixed inside the common input distance, the datum-dependent equality radii
have a positive finite minimum.  Thus one ball radius works for every actual
datum in the family.

The common output radius is selected after `L`, `z`, and `d`; the theorem does
not promote this finite minimum to a uniform radius over counterfactual chain
states or over a subsequently changed mesh. -/
theorem exists_uniform_distance_radius_and_common_eqOn_ball_for_finite_data
    [CompactSpace M] [ConnectedSpace M]
    {iota : Type v} [Fintype iota] [Nonempty iota]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : iota → M) (p : iota → RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (L : ∀ i : iota,
          CartanMap.TangentAlignment g (x i) (p i))
        (z : iota → M)
        (d : ∀ i : iota,
          DifferentialInducedSuccessor.Data
            (CartanChain.ChainState.mk (x i) (p i) (L i)) (z i)),
        (∀ i : iota, dist (z i) (x i) < epsilon) →
          ∃ r > (0 : ℝ), ∀ i : iota,
            EqOn
              (CartanChain.ChainState.mk (x i) (p i) (L i)).germ
              (d i).successor.germ (Metric.ball (z i) r) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_uniform_distance_radius_with_datum_eqOn_ball_on_finite_family
        g hcurv x p with
    ⟨epsilon, hepsilon, hlocal⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z d hdist
  have hdatum : ∀ i : iota, ∃ r > (0 : ℝ),
      EqOn
        (CartanChain.ChainState.mk (x i) (p i) (L i)).germ
        (d i).successor.germ (Metric.ball (z i) r) := by
    intro i
    exact hlocal i (L i) (d i) (hdist i)
  choose radius hradius hEq using hdatum
  let r : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hr : 0 < r := by
    dsimp [r]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨r, hr, ?_⟩
  intro i q hq
  apply hEq i
  exact Metric.ball_subset_ball
    (Finset.inf'_le radius (Finset.mem_univ i)) hq

end DifferentialSuccessorFiniteAnchorRadius
end Poincare
