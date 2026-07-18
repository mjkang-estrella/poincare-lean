import Poincare.Global.CartanAdjacentContinuation
import Poincare.Global.DifferentialInducedSuccessor

/-!
# Cartan chain compatibility from adjacent path independence

The existing chain API stages every successor step behind
`ChainRigidCompatible`, an equality on the complete adjacent germ overlap.
For preconnected adjacent overlaps this equality is now a theorem: the
successor construction supplies the anchor seed, while induced-alignment path
independence supplies local rigidity.  This module lifts that result over an
entire iterated chain.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanChainRigidity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The alignment hidden in `ChainState.next`, named for explicit-alignment
continuation theorems. -/
def chosenNextAlignment
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M) :
    CartanMap.TangentAlignment g z (s.map z) :=
  Classical.choice
    (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := z) (p₀ := s.map z))

@[simp]
theorem nextWithChosenAlignment_eq_next
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M) :
    InducedAlignment.CompatibleStep.nextWithAlignment
        s z (chosenNextAlignment s z) =
      s.next z :=
  rfl

/-- The global choice of a tangent alignment is dependent only on its indexed
anchor data.  Equal target indices therefore give heterogeneous equality of
the chosen alignments. -/
theorem chosenTangentAlignment_heq_of_target_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {z : M}
    {p₁ p₂ : RoundSphere3} (h : p₁ = p₂) :
    HEq
      (Classical.choice
        (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := z) (p₀ := p₁)))
      (Classical.choice
        (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := z) (p₀ := p₂))) := by
  subst p₂
  rfl

/-- Once two predecessor maps have the same value at the new anchor, the
alignments selected by `ChainState.next` are heterogeneously equal. -/
theorem next_alignment_heq_of_map_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (h : s₁.map z = s₂.map z) :
    HEq (s₁.next z).alignment (s₂.next z).alignment := by
  exact chosenTangentAlignment_heq_of_target_eq h

/-- Equal predecessor values at an anchor identify the entire chosen successor
state, not only its target and alignment fields separately. -/
theorem next_eq_next_of_map_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (h : s₁.map z = s₂.map z) :
    s₁.next z = s₂.next z := by
  let mkNext : RoundSphere3 → CartanChain.ChainState g := fun p ↦
    { anchor := z
      target := p
      alignment := Classical.choice
        (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := z) (p₀ := p)) }
  change mkNext (s₁.map z) = mkNext (s₂.map z)
  exact congrArg mkNext h

/-- Single-insertion endpoint germ equality needs no alignment side condition.
The rigid step first identifies the endpoint targets; the globally chosen
successor alignments then agree automatically at the equal indexed data. -/
theorem endpoint_germ_eq_insert_of_rigidStepCompatible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (y z : M)
    (h : s.RigidStepCompatible y)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source) :
    (s.next z).germ = ((s.next y).next z).germ := by
  have hp : (s.next z).target = ((s.next y).next z).target :=
    CartanChain.endpoint_target_eq_insert (g := g) h hz
  have hL : HEq (s.next z).alignment ((s.next y).next z).alignment :=
    next_alignment_heq_of_map_eq s (s.next y) z (by simpa using hp)
  exact CartanChain.endpoint_germ_eq_insert_of_alignment (g := g) h hz hL

/-- State-level single-insertion independence.  A compatible re-anchor at `y`
does not change the chosen endpoint state subsequently formed at `z`. -/
theorem endpoint_state_eq_insert_of_rigidStepCompatible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (y z : M)
    (h : s.RigidStepCompatible y)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source) :
    s.next z = (s.next y).next z := by
  have hmap : s.map z = (s.next y).map z :=
    (CartanChain.ChainState.next_map_eq_of_rigidStepCompatible
      (g := g) h hz).symm
  exact next_eq_next_of_map_eq s (s.next y) z hmap

/-- Equality of two continuation histories after re-anchoring at the same point
forces equality of their carried values at that point. -/
theorem germ_value_eq_of_next_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (hnext : s₁.next z = s₂.next z) :
    s₁.germ z = s₂.germ z := by
  have htarget := congrArg CartanChain.ChainState.target hnext
  simpa [CartanChain.ChainState.germ, CartanChain.ChainState.map,
    CartanChain.ChainState.next] using htarget

/-- Endpoint-state monodromy supplies the component seed required by overlap
continuation: at an overlap point `z`, choose `z` itself as the seed. -/
theorem component_seed_of_next_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (hz : z ∈ s₁.germ.source ∩ s₂.germ.source)
    (hnext : s₁.next z = s₂.next z) :
    ∃ w ∈ connectedComponentIn
        (s₁.germ.source ∩ s₂.germ.source) z,
      s₁.germ w = s₂.germ w := by
  exact ⟨z, mem_connectedComponentIn hz,
    germ_value_eq_of_next_eq s₁ s₂ z hnext⟩

/-- A single chosen successor step is rigid-compatible once its overlap is
preconnected and its induced alignments are path-independent at equality
points.  This is the one-step form used to replace the old staged hypothesis in
endpoint insertion consumers. -/
theorem rigidStepCompatible_of_preconnected_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (hzold : z ∈ s.germ.source)
    (hpre : IsPreconnected (s.germ.source ∩ (s.next z).germ.source))
    (hpath :
      ∀ q ∈ s.germ.source ∩ (s.next z).germ.source,
        (hvalue : s.map q = (s.next z).map q) →
          ∃ (Ls : CartanMap.TangentAlignment g q (s.map q))
            (Ln : CartanMap.TangentAlignment g q ((s.next z).map q)),
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith s q Ls ∧
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                (s.next z) q Ln ∧
              HEq Ls Ln) :
    s.RigidStepCompatible z := by
  let Lz := chosenNextAlignment s z
  have hEq :=
    CartanAdjacentContinuation.chainAdjacent_eqOn_of_preconnected_overlap_of_alignment_pathIndependence
      s z Lz hzold
      (by simpa [Lz] using hpre)
      (by
        intro q hq hvalue
        rcases hpath q (by simpa [Lz] using hq)
            (by simpa [Lz] using hvalue) with
          ⟨Ls, Ln, hs, hn, hL⟩
        exact ⟨Ls, Ln, hs, by simpa [Lz] using hn, hL⟩)
  simpa [CartanChain.ChainState.RigidStepCompatible, Lz] using hEq

/-- The insertion endpoint target comparison without a
`RigidStepCompatible` assumption. -/
theorem endpoint_target_eq_insert_of_preconnected_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (y z : M)
    (hyold : y ∈ s.germ.source)
    (hpre : IsPreconnected (s.germ.source ∩ (s.next y).germ.source))
    (hpath :
      ∀ q ∈ s.germ.source ∩ (s.next y).germ.source,
        (hvalue : s.map q = (s.next y).map q) →
          ∃ (Ls : CartanMap.TangentAlignment g q (s.map q))
            (Ln : CartanMap.TangentAlignment g q ((s.next y).map q)),
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith s q Ls ∧
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                (s.next y) q Ln ∧
              HEq Ls Ln)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source) :
    (s.next z).target = ((s.next y).next z).target := by
  exact CartanChain.endpoint_target_eq_insert
    (g := g)
    (rigidStepCompatible_of_preconnected_pathIndependence
      s y hyold hpre hpath) hz

/--
Single-insertion endpoint germ comparison with adjacent full-overlap
compatibility discharged.  No separate endpoint-alignment hypothesis is
needed: after the endpoint targets agree, the two successors invoke the same
global tangent-alignment choice at the same indexed anchor data.
-/
theorem endpoint_germ_eq_insert_of_preconnected_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (y z : M)
    (hyold : y ∈ s.germ.source)
    (hpre : IsPreconnected (s.germ.source ∩ (s.next y).germ.source))
    (hpath :
      ∀ q ∈ s.germ.source ∩ (s.next y).germ.source,
        (hvalue : s.map q = (s.next y).map q) →
          ∃ (Ls : CartanMap.TangentAlignment g q (s.map q))
            (Ln : CartanMap.TangentAlignment g q ((s.next y).map q)),
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith s q Ls ∧
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                (s.next y) q Ln ∧
              HEq Ls Ln)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source) :
    (s.next z).germ = ((s.next y).next z).germ := by
  exact endpoint_germ_eq_insert_of_rigidStepCompatible s y z
    (rigidStepCompatible_of_preconnected_pathIndependence
      s y hyold hpre hpath) hz

/-- Two carried Cartan germs that agree at a point are locally equal there as
soon as each is compatible with its chosen successor at that point.  Equality
of the successor alignments is automatic from equality of the carried target
values. -/
theorem locally_eq_of_rigidSteps
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (hp : s₁.map z = s₂.map z)
    (h₁ : s₁.RigidStepCompatible z)
    (h₂ : s₂.RigidStepCompatible z) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      EqOn s₁.germ s₂.germ
        (V ∩ (s₁.germ.source ∩ s₂.germ.source)) := by
  let L₁ := chosenNextAlignment s₁ z
  let L₂ := chosenNextAlignment s₂ z
  have hL : HEq L₁ L₂ := by
    exact next_alignment_heq_of_map_eq s₁ s₂ z hp
  apply CartanLocalRigidity.locally_eq_of_rigidSteps_of_alignment_heq
    s₁ s₂ z L₁ L₂ hp hL
  · simpa only [InducedAlignment.CompatibleStep.RigidStepCompatibleWith,
      L₁, nextWithChosenAlignment_eq_next,
      CartanChain.ChainState.RigidStepCompatible] using h₁
  · simpa only [InducedAlignment.CompatibleStep.RigidStepCompatibleWith,
      L₂, nextWithChosenAlignment_eq_next,
      CartanChain.ChainState.RigidStepCompatible] using h₂

/--
All-anchor globalization payload with the alignment path-independence datum
removed.

It retains exactly the two geometric inputs not supplied by dependent choice:
one equality seed in each connected component of a pairwise overlap, and
compatibility of each carried germ with its chosen re-anchor at an equality
point.  In particular, it assumes neither local equality of two different
carried germs nor equality of independently supplied tangent alignments.
-/
def UnitCurvatureComponentwiseChosenReanchorRigidity3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          (∀ x y z : M,
            z ∈ (CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source →
              ∃ w ∈ connectedComponentIn
                  ((CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                    (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source) z,
                (CartanLocalRigidity.anchoredFamilyState g p L x).germ w =
                  (CartanLocalRigidity.anchoredFamilyState g p L y).germ w) ∧
          (∀ x y z : M,
            z ∈ (CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source →
            (CartanLocalRigidity.anchoredFamilyState g p L x).map z =
                (CartanLocalRigidity.anchoredFamilyState g p L y).map z →
              (CartanLocalRigidity.anchoredFamilyState g p L x).RigidStepCompatible z ∧
                (CartanLocalRigidity.anchoredFamilyState g p L y).RigidStepCompatible z)

/-- Component seeds and chosen re-anchor rigidity produce the actual
pairwise-compatible Cartan atlas consumed by unit-curvature recognition. -/
theorem compatibleCartanAtlas_of_componentwiseChosenReanchorRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureComponentwiseChosenReanchorRigidity3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  apply
    CartanOverlapContinuation.compatibleCartanAtlas_of_componentwiseOverlapLocalRigidity
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hseed, hstep⟩
  refine ⟨p, L, ?_⟩
  intro x y
  let sₓ := CartanLocalRigidity.anchoredFamilyState g p L x
  let sᵧ := CartanLocalRigidity.anchoredFamilyState g p L y
  constructor
  · intro z hz
    simpa [sₓ, sᵧ] using hseed x y z (by simpa [sₓ, sᵧ] using hz)
  · intro z hz hvalue
    have hz' : z ∈ sₓ.germ.source ∩ sᵧ.germ.source := by
      simpa [sₓ, sᵧ] using hz
    have hvalue' : sₓ.map z = sᵧ.map z := by
      simpa [sₓ, sᵧ] using hvalue
    rcases hstep x y z (by simpa [sₓ, sᵧ] using hz')
        (by simpa [sₓ, sᵧ] using hvalue') with ⟨hₓ, hᵧ⟩
    simpa [sₓ, sᵧ] using locally_eq_of_rigidSteps sₓ sᵧ z hvalue' hₓ hᵧ

/--
Compatible-atlas consumer with the component-seed field removed.

Instead of asking for a seed in every overlap component, it consumes endpoint
monodromy: the two continuation histories re-anchored at an arbitrary overlap
point give the same successor state.  `component_seed_of_next_eq` derives the
old seed internally.  The only remaining local field is chosen re-anchor
rigidity at an equality point.
-/
theorem compatibleCartanAtlas_of_nextMonodromy_and_chosenReanchorRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g 1 →
        ∃ (p : M → RoundSphere3)
          (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
            (∀ x y z : M,
              z ∈ (CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                  (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source →
                (CartanLocalRigidity.anchoredFamilyState g p L x).next z =
                  (CartanLocalRigidity.anchoredFamilyState g p L y).next z) ∧
            (∀ x y z : M,
              z ∈ (CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                  (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source →
              (CartanLocalRigidity.anchoredFamilyState g p L x).map z =
                  (CartanLocalRigidity.anchoredFamilyState g p L y).map z →
                CartanChain.ChainState.RigidStepCompatible
                    (CartanLocalRigidity.anchoredFamilyState g p L x) z ∧
                  CartanChain.ChainState.RigidStepCompatible
                    (CartanLocalRigidity.anchoredFamilyState g p L y) z)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  apply compatibleCartanAtlas_of_componentwiseChosenReanchorRigidity
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hmonodromy, hstep⟩
  refine ⟨p, L, ?_, hstep⟩
  intro x y z hz
  exact component_seed_of_next_eq
    (CartanLocalRigidity.anchoredFamilyState g p L x)
    (CartanLocalRigidity.anchoredFamilyState g p L y) z hz
    (hmonodromy x y z hz)

/-- A finite iterated chain contained in one compatible root chart is
independent of all intermediate anchors.  Its state after `n + 1` steps is the
direct chosen successor of the root at the last node.  This is the discrete
refinement lemma needed for subdivision and homotopy-grid arguments. -/
theorem chainState_succ_eq_direct_next
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (nodes : ℕ → M)
    (hcompat : ∀ n : ℕ, s.RigidStepCompatible (nodes (n + 1)))
    (hmem : ∀ n : ℕ,
      nodes (n + 2) ∈
        s.germ.source ∩ (s.next (nodes (n + 1))).germ.source) :
    ∀ n : ℕ,
      CartanChain.chainState g nodes s (n + 1) = s.next (nodes (n + 1)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        CartanChain.chainState g nodes s (n.succ + 1) =
            (CartanChain.chainState g nodes s (n + 1)).next
              (nodes (n + 2)) := by
                simp only [Nat.succ_eq_add_one, Nat.add_assoc]
                exact CartanChain.chainState_succ g nodes s (n + 1)
        _ = (s.next (nodes (n + 1))).next (nodes (n + 2)) := by rw [ih]
        _ = s.next (nodes (n + 2)) :=
          (endpoint_state_eq_insert_of_rigidStepCompatible
            s (nodes (n + 1)) (nodes (n + 2)) (hcompat n) (hmem n)).symm
        _ = s.next (nodes (n.succ + 1)) := by
          simp only [Nat.succ_eq_add_one, Nat.add_assoc]

/-- Connected smooth manifolds are path connected, so the uniform normal
subdivision theorem reaches any prescribed pair of anchors.  This removes any
separate path-existence assumption from later Cartan-chain constructions. -/
theorem exists_path_uniform_normal_subdivision_between
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x y : M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ γ : Path x y,
      ∃ r > (0 : ℝ), ∃ t : ℕ → unitInterval,
        t 0 = 0 ∧
          Monotone t ∧
            (∃ m, ∀ n ≥ m, t n = 1) ∧
              (∀ n, dist (γ (t n)) (γ (t (n + 1))) < r) ∧
                ∀ n, ∃ a : M,
                  γ (t n) ∈ GeodesicTransport.normalCoordinateImage g a ∧
                    γ (t (n + 1)) ∈
                      GeodesicTransport.normalCoordinateImage g a := by
  letI : MetricSpace M := g.toMetricSpace
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace E M
  letI : PathConnectedSpace M :=
    PathConnectedSpace.of_locPathConnectedSpace
  let γ : Path x y := (PathConnectedSpace.joined x y).somePath
  refine ⟨γ, ?_⟩
  simpa [γ] using
    (CartanChain.exists_uniform_normal_subdivision g γ.toContinuousMap)

/-- Every Cartan state has an explicit positive metric ball around its anchor
contained in its strict partial-homeomorphism source. -/
theorem exists_ball_subset_germ_source
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), Metric.ball s.anchor r ⊆ s.germ.source := by
  letI : MetricSpace M := g.toMetricSpace
  exact Metric.isOpen_iff.mp s.germ.open_source s.anchor
    (CartanMap.anchor_mem_source g s.anchor s.target s.alignment)

/-- If the new anchor is in the old strict source, a positive metric ball
around it lies in the complete old/successor source intersection.  This is the
exact radius fact needed for each diagonal membership in a homotopy-grid cell;
membership in an unrelated normal-coordinate image is not sufficient. -/
theorem exists_ball_subset_adjacent_germ_overlap
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M) (hz : z ∈ s.germ.source) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ),
      Metric.ball z r ⊆ s.germ.source ∩ (s.next z).germ.source := by
  letI : MetricSpace M := g.toMetricSpace
  have hznext : z ∈ (s.next z).germ.source := by
    exact CartanMap.anchor_mem_source g z (s.map z) (s.next z).alignment
  exact Metric.isOpen_iff.mp
    (s.germ.open_source.inter (s.next z).germ.open_source) z ⟨hz, hznext⟩

/-- A continuous homotopy rectangle admits one finite monotone grid such that
the image of every closed grid cell lies in a single normal-coordinate image.
The same subdivision is used in both coordinate directions, which is the
shape required by the ladder comparison below. -/
theorem exists_homotopy_normal_grid
    (g : ClosedSmoothRiemannianMetric 3 M)
    (H : C(unitInterval × unitInterval, M)) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
        Monotone t ∧
          (∃ k, ∀ n ≥ k, t n = 1) ∧
            ∀ n m, ∃ a : M,
              ∀ s ∈ Icc (t n) (t (n + 1)),
                ∀ u ∈ Icc (t m) (t (m + 1)),
                  H (s, u) ∈ GeodesicTransport.normalCoordinateImage g a := by
  let c : M → Set (unitInterval × unitInterval) := fun a ↦
    H ⁻¹' GeodesicTransport.normalCoordinateImage g a
  have hcOpen : ∀ a : M, IsOpen (c a) := by
    intro a
    exact (GeodesicTransport.isOpen_normalCoordinateImage g a).preimage H.continuous
  have hcCover : (Set.univ : Set (unitInterval × unitInterval)) ⊆ ⋃ a, c a := by
    intro q _hq
    exact mem_iUnion.2 ⟨H q, GeodesicTransport.mem_normalCoordinateImage_self g (H q)⟩
  rcases exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      hcOpen hcCover with ⟨t, ht0, htmono, hteventual, hcell⟩
  refine ⟨t, ht0, htmono, hteventual, ?_⟩
  intro n m
  rcases hcell n m with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro s hs u hu
  exact ha ⟨hs, hu⟩

/--
Rectangular ladder invariant for two discretized paths.

Write `b n` and `t n` for the chain states along the lower and upper rows.
The conclusion says that after every positive number of columns, the upper
state is obtained by adding the vertical rung to the lower state.  The base
cell uses lower-edge insertion independence; each successor cell first removes
the previous rung and then inserts the next lower edge.  Thus no equality of
intermediate states at different grid vertices is assumed.
-/
theorem closeChain_ladder_invariant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (hbottom : ∀ j : ℕ,
      (CartanChain.chainState g lower initial j).RigidStepCompatible
        (lower (j + 1)))
    (hcross : ∀ j : ℕ,
      upper (j + 1) ∈
        (CartanChain.chainState g lower initial j).germ.source ∩
          ((CartanChain.chainState g lower initial j).next
            (lower (j + 1))).germ.source)
    (hrung : ∀ j : ℕ,
      (CartanChain.chainState g lower initial (j + 1)).RigidStepCompatible
        (upper (j + 1)))
    (hrungCross : ∀ j : ℕ,
      upper (j + 2) ∈
        (CartanChain.chainState g lower initial (j + 1)).germ.source ∩
          ((CartanChain.chainState g lower initial (j + 1)).next
            (upper (j + 1))).germ.source) :
    ∀ n : ℕ,
      CartanChain.chainState g upper initial (n + 1) =
        (CartanChain.chainState g lower initial (n + 1)).next
          (upper (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact endpoint_state_eq_insert_of_rigidStepCompatible
        initial (lower 1) (upper 1) (hbottom 0) (hcross 0)
  | succ n ih =>
      calc
        CartanChain.chainState g upper initial (n.succ + 1) =
            (CartanChain.chainState g upper initial (n + 1)).next
              (upper (n + 2)) := by
                simp only [Nat.succ_eq_add_one, Nat.add_assoc]
                exact CartanChain.chainState_succ g upper initial (n + 1)
        _ = ((CartanChain.chainState g lower initial (n + 1)).next
              (upper (n + 1))).next (upper (n + 2)) := by rw [ih]
        _ = (CartanChain.chainState g lower initial (n + 1)).next
              (upper (n + 2)) :=
          (endpoint_state_eq_insert_of_rigidStepCompatible
            (CartanChain.chainState g lower initial (n + 1))
            (upper (n + 1)) (upper (n + 2))
            (hrung n) (hrungCross n)).symm
        _ = ((CartanChain.chainState g lower initial (n + 1)).next
              (lower (n + 2))).next (upper (n + 2)) :=
          endpoint_state_eq_insert_of_rigidStepCompatible
            (CartanChain.chainState g lower initial (n + 1))
            (lower (n + 2)) (upper (n + 2))
            (hbottom (n + 1)) (hcross (n + 1))
        _ = (CartanChain.chainState g lower initial (n.succ + 1)).next
              (upper (n.succ + 1)) := by
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
            congrArg (fun state : CartanChain.ChainState g ↦
              state.next (upper (n + 2)))
              (CartanChain.chainState_succ
                g lower initial (n + 1)).symm

/-- Endpoint comparison for two finite, sufficiently close discrete paths.
If the rows share their final vertex after `N + 2` steps, the ladder invariant
and the last vertical cell identify their endpoint chain states. -/
theorem closeChains_endpoint_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (hbottom : ∀ j : ℕ,
      (CartanChain.chainState g lower initial j).RigidStepCompatible
        (lower (j + 1)))
    (hcross : ∀ j : ℕ,
      upper (j + 1) ∈
        (CartanChain.chainState g lower initial j).germ.source ∩
          ((CartanChain.chainState g lower initial j).next
            (lower (j + 1))).germ.source)
    (hrung : ∀ j : ℕ,
      (CartanChain.chainState g lower initial (j + 1)).RigidStepCompatible
        (upper (j + 1)))
    (hrungCross : ∀ j : ℕ,
      upper (j + 2) ∈
        (CartanChain.chainState g lower initial (j + 1)).germ.source ∩
          ((CartanChain.chainState g lower initial (j + 1)).next
            (upper (j + 1))).germ.source)
    (N : ℕ) (hend : lower (N + 2) = upper (N + 2)) :
    CartanChain.chainState g lower initial (N + 2) =
      CartanChain.chainState g upper initial (N + 2) := by
  have hinv := closeChain_ladder_invariant
    initial lower upper hbottom hcross hrung hrungCross N
  calc
    CartanChain.chainState g lower initial (N + 2) =
        (CartanChain.chainState g lower initial (N + 1)).next
          (lower (N + 2)) := by
            rw [show N + 2 = (N + 1) + 1 by omega]
            exact CartanChain.chainState_succ g lower initial (N + 1)
    _ = (CartanChain.chainState g lower initial (N + 1)).next
          (upper (N + 2)) := by rw [hend]
    _ = ((CartanChain.chainState g lower initial (N + 1)).next
          (upper (N + 1))).next (upper (N + 2)) :=
      endpoint_state_eq_insert_of_rigidStepCompatible
        (CartanChain.chainState g lower initial (N + 1))
        (upper (N + 1)) (upper (N + 2))
        (hrung N) (hrungCross N)
    _ = (CartanChain.chainState g upper initial (N + 1)).next
          (upper (N + 2)) := by rw [← hinv]
    _ = CartanChain.chainState g upper initial (N + 2) := by
      rw [show N + 2 = (N + 1) + 1 by omega]
      exact (CartanChain.chainState_succ g upper initial (N + 1)).symm

/--
Endpoint monodromy across a finite homotopy grid.

The four cell hypotheses are precisely the lower horizontal step, the first
diagonal membership, the vertical rung step, and the second diagonal
membership used by `closeChains_endpoint_eq`.  Applying that comparison to
each adjacent pair of homotopy rows and iterating from grid parameter `0` to
`1` proves equality of the two boundary-path endpoint states.
-/
theorem homotopyGrid_chain_endpoint_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (t : ℕ → unitInterval)
    (ht0 : t 0 = 0) (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (hbottom : ∀ m j : ℕ,
      CartanChain.ChainState.RigidStepCompatible
        (CartanChain.chainState g (fun n ↦ F (t m, t n)) initial j)
        (F (t m, t (j + 1))))
    (hcross : ∀ m j : ℕ,
      F (t (m + 1), t (j + 1)) ∈
        (CartanChain.chainState g
          (fun n ↦ F (t m, t n)) initial j).germ.source ∩
          ((CartanChain.chainState g (fun n ↦ F (t m, t n)) initial j).next
            (F (t m, t (j + 1)))).germ.source)
    (hrung : ∀ m j : ℕ,
      CartanChain.ChainState.RigidStepCompatible
        (CartanChain.chainState g
          (fun n ↦ F (t m, t n)) initial (j + 1))
        (F (t (m + 1), t (j + 1))))
    (hrungCross : ∀ m j : ℕ,
      F (t (m + 1), t (j + 2)) ∈
        (CartanChain.chainState g
          (fun n ↦ F (t m, t n)) initial (j + 1)).germ.source ∩
          ((CartanChain.chainState g (fun n ↦ F (t m, t n)) initial (j + 1)).next
            (F (t (m + 1), t (j + 1)))).germ.source) :
    CartanChain.chainState g (fun n ↦ p₀ (t n)) initial (k + 2) =
      CartanChain.chainState g (fun n ↦ p₁ (t n)) initial (k + 2) := by
  let nodes : ℕ → ℕ → M := fun m n ↦ F (t m, t n)
  let endpointState : ℕ → CartanChain.ChainState g := fun m ↦
    CartanChain.chainState g (nodes m) initial (k + 2)
  have hk_le : k ≤ k + 2 := Nat.le_add_right k 2
  have htK : t (k + 2) = 1 := htone (k + 2) hk_le
  have hadj : ∀ m : ℕ, endpointState m = endpointState (m + 1) := by
    intro m
    apply closeChains_endpoint_eq initial (nodes m) (nodes (m + 1))
      (fun j ↦ by simpa [nodes] using hbottom m j)
      (fun j ↦ by simpa [nodes] using hcross m j)
      (fun j ↦ by simpa [nodes] using hrung m j)
      (fun j ↦ by simpa [nodes] using hrungCross m j)
      k
    simp only [nodes, htK]
    exact (F.target (t m)).trans (F.target (t (m + 1))).symm
  have hiterate : ∀ m : ℕ, endpointState 0 = endpointState m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        exact ih.trans (by simpa [Nat.succ_eq_add_one] using hadj m)
  have hends := hiterate (k + 2)
  simpa [endpointState, nodes, ht0, htK] using hends

/--
Simply connected specialization of the rectangular comparison.

Any two paths with the same endpoints are connected by a relative homotopy.  A single
finite grid is then chosen so every closed cell lies in one normal-coordinate
image.  The final conjunct packages the proved ladder implication on that
specific grid: once the four local Cartan step/source facts hold on its cells,
the two boundary continuations have equal endpoint states.
-/
theorem exists_simplyConnected_homotopy_normal_grid_endpoint_comparison
    [SimplyConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) {x y : M}
    (p₀ p₁ : Path x y) :
    ∃ (F : p₀.Homotopy p₁) (t : ℕ → unitInterval) (k : ℕ),
      t 0 = 0 ∧
        Monotone t ∧
          (∀ n ≥ k, t n = 1) ∧
            (∀ n m, ∃ a : M,
              ∀ s ∈ Icc (t n) (t (n + 1)),
                ∀ u ∈ Icc (t m) (t (m + 1)),
                  F (s, u) ∈ GeodesicTransport.normalCoordinateImage g a) ∧
            ∀ initial : CartanChain.ChainState g,
              (∀ m j : ℕ,
                CartanChain.ChainState.RigidStepCompatible
                  (CartanChain.chainState g
                    (fun n ↦ F (t m, t n)) initial j)
                  (F (t m, t (j + 1)))) →
              (∀ m j : ℕ,
                F (t (m + 1), t (j + 1)) ∈
                  (CartanChain.chainState g
                    (fun n ↦ F (t m, t n)) initial j).germ.source ∩
                    ((CartanChain.chainState g
                      (fun n ↦ F (t m, t n)) initial j).next
                        (F (t m, t (j + 1)))).germ.source) →
              (∀ m j : ℕ,
                CartanChain.ChainState.RigidStepCompatible
                  (CartanChain.chainState g
                    (fun n ↦ F (t m, t n)) initial (j + 1))
                  (F (t (m + 1), t (j + 1)))) →
              (∀ m j : ℕ,
                F (t (m + 1), t (j + 2)) ∈
                  (CartanChain.chainState g
                    (fun n ↦ F (t m, t n)) initial (j + 1)).germ.source ∩
                    ((CartanChain.chainState g
                      (fun n ↦ F (t m, t n)) initial (j + 1)).next
                        (F (t (m + 1), t (j + 1)))).germ.source) →
                CartanChain.chainState g (fun n ↦ p₀ (t n)) initial (k + 2) =
                  CartanChain.chainState g
                    (fun n ↦ p₁ (t n)) initial (k + 2) := by
  rcases SimplyConnectedSpace.paths_homotopic p₀ p₁ with ⟨F⟩
  rcases exists_homotopy_normal_grid g F.toContinuousMap with
    ⟨t, ht0, htmono, ⟨k, htone⟩, hcells⟩
  refine ⟨F, t, k, ht0, htmono, htone, ?_, ?_⟩
  · simpa using hcells
  · intro initial hbottom hcross hrung hrungCross
    exact homotopyGrid_chain_endpoint_eq
      F initial t ht0 k htone hbottom hcross hrung hrungCross

/--
Preconnected adjacent overlaps and induced-alignment path independence produce
the exact `ChainRigidCompatible` payload expected by the existing iterated
chain API.  No full-overlap equality is assumed.
-/
theorem chainRigidCompatible_of_preconnected_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (hnode : ∀ n : ℕ,
      nodes (n + 1) ∈ (CartanChain.chainState g nodes initial n).germ.source)
    (hpre : ∀ n : ℕ,
      IsPreconnected
        ((CartanChain.chainState g nodes initial n).germ.source ∩
          ((CartanChain.chainState g nodes initial n).next
            (nodes (n + 1))).germ.source))
    (hpath : ∀ n : ℕ, ∀ q ∈
        (CartanChain.chainState g nodes initial n).germ.source ∩
          ((CartanChain.chainState g nodes initial n).next
            (nodes (n + 1))).germ.source,
      (hvalue : (CartanChain.chainState g nodes initial n).map q =
        ((CartanChain.chainState g nodes initial n).next
          (nodes (n + 1))).map q) →
        ∃ (Ls : CartanMap.TangentAlignment g q
              ((CartanChain.chainState g nodes initial n).map q))
          (Ln : CartanMap.TangentAlignment g q
              (((CartanChain.chainState g nodes initial n).next
                (nodes (n + 1))).map q)),
          InducedAlignment.CompatibleStep.RigidStepCompatibleWith
              (CartanChain.chainState g nodes initial n) q Ls ∧
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith
              ((CartanChain.chainState g nodes initial n).next
                (nodes (n + 1))) q Ln ∧
            HEq Ls Ln) :
    CartanChain.ChainRigidCompatible g nodes initial := by
  intro n
  let s := CartanChain.chainState g nodes initial n
  let z := nodes (n + 1)
  let Lz := chosenNextAlignment s z
  have hEq :=
    CartanAdjacentContinuation.chainAdjacent_eqOn_of_preconnected_overlap_of_alignment_pathIndependence
      s z Lz
      (by simpa [s, z] using hnode n)
      (by simpa [s, z, Lz] using hpre n)
      (by
        intro q hq hvalue
        rcases hpath n q (by simpa [s, z, Lz] using hq)
            (by simpa [s, z, Lz] using hvalue) with
          ⟨Ls, Ln, hs, hn, hL⟩
        exact ⟨Ls, Ln, hs, by simpa [s, z, Lz] using hn, hL⟩)
  simpa [CartanChain.ChainState.RigidStepCompatible, s, z, Lz] using hEq

/--
The restricted-source agreement for every chain step, with the old
`ChainRigidCompatible` argument eliminated in favor of the weaker geometric
preconnectedness/path-independence data.
-/
theorem chain_step_restr_eqOnSource_of_preconnected_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (hnode : ∀ n : ℕ,
      nodes (n + 1) ∈ (CartanChain.chainState g nodes initial n).germ.source)
    (hpre : ∀ n : ℕ,
      IsPreconnected
        ((CartanChain.chainState g nodes initial n).germ.source ∩
          ((CartanChain.chainState g nodes initial n).next
            (nodes (n + 1))).germ.source))
    (hpath : ∀ n : ℕ, ∀ q ∈
        (CartanChain.chainState g nodes initial n).germ.source ∩
          ((CartanChain.chainState g nodes initial n).next
            (nodes (n + 1))).germ.source,
      (hvalue : (CartanChain.chainState g nodes initial n).map q =
        ((CartanChain.chainState g nodes initial n).next
          (nodes (n + 1))).map q) →
        ∃ (Ls : CartanMap.TangentAlignment g q
              ((CartanChain.chainState g nodes initial n).map q))
          (Ln : CartanMap.TangentAlignment g q
              (((CartanChain.chainState g nodes initial n).next
                (nodes (n + 1))).map q)),
          InducedAlignment.CompatibleStep.RigidStepCompatibleWith
              (CartanChain.chainState g nodes initial n) q Ls ∧
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith
              ((CartanChain.chainState g nodes initial n).next
                (nodes (n + 1))) q Ln ∧
            HEq Ls Ln)
    (n : ℕ) :
    (CartanChain.chainGerm g nodes initial n).restr
        (CartanChain.chainGerm g nodes initial (n + 1)).source ≈
      (CartanChain.chainGerm g nodes initial (n + 1)).restr
        (CartanChain.chainGerm g nodes initial n).source := by
  exact CartanChain.chain_step_restr_eqOnSource
    (g := g)
    (chainRigidCompatible_of_preconnected_pathIndependence
      nodes initial hnode hpre hpath) n

end CartanChainRigidity
end Poincare
