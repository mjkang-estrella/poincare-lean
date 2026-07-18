import Poincare.Global.CartanLocalRigidity

/-!
# Seed-free continuation for adjacent Cartan germs

A re-anchored successor germ has a canonical equality seed at its new anchor:
the old state takes the value `s.map z` there by definition, and the successor
Cartan germ sends its own anchor to that same target.  Consequently no
component-seed hypothesis is needed on the connected component containing the
new anchor.  If the whole overlap is preconnected, this closes equality on the
entire overlap.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanAdjacentContinuation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The carried state and its re-anchored successor agree at the new anchor.
This is the canonical seed absent from arbitrary pairwise overlaps. -/
theorem chainAdjacent_anchor_seed
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (Lz : CartanMap.TangentAlignment g z (s.map z)) :
    s.germ z =
      (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ z := by
  change s.map z = CartanMap.cartanMap g z (s.map z) Lz z
  exact (CartanMap.cartanMap_anchor (g := g) (x₀ := z) (p₀ := s.map z) Lz).symm

/-- The new anchor lies in the successor source, independently of the old
source. -/
theorem chainAdjacent_anchor_mem_successor_source
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (Lz : CartanMap.TangentAlignment g z (s.map z)) :
    z ∈ (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source := by
  simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
    CartanChain.ChainState.germ] using
    CartanMap.anchor_mem_source g z (s.map z) Lz

/--
Local rigidity propagates the canonical adjacent-chain seed through the
connected component of the overlap containing the new anchor.  No seed in any
other component is assumed or manufactured.
-/
theorem chainAdjacent_eqOn_anchorComponent_of_local_rigidity
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (Lz : CartanMap.TangentAlignment g z (s.map z))
    (hzold : z ∈ s.germ.source)
    (hlocal :
      ∀ q ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source,
        s.germ q =
            (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ q →
          ∃ V : Set M, IsOpen V ∧ q ∈ V ∧
            EqOn s.germ
              (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ
              (V ∩
                (s.germ.source ∩
                  (InducedAlignment.CompatibleStep.nextWithAlignment
                    s z Lz).germ.source))) :
    EqOn s.germ
      (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ
      (connectedComponentIn
        (s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source)
        z) := by
  let n := InducedAlignment.CompatibleStep.nextWithAlignment s z Lz
  let S : Set M := s.germ.source ∩ n.germ.source
  let C : Set M := connectedComponentIn S z
  have hznew : z ∈ n.germ.source := by
    simpa [n] using chainAdjacent_anchor_mem_successor_source s z Lz
  have hzS : z ∈ S := ⟨hzold, hznew⟩
  have hCsub : C ⊆ S := by
    simpa [C] using connectedComponentIn_subset S z
  have hscont : ContinuousOn s.germ C :=
    s.germ.continuousOn.mono (hCsub.trans inter_subset_left)
  have hncont : ContinuousOn n.germ C :=
    n.germ.continuousOn.mono (hCsub.trans inter_subset_right)
  have hseed : s.germ z = n.germ z := by
    simpa [n] using chainAdjacent_anchor_seed s z Lz
  apply
    CartanOverlapContinuation.eqOn_of_preconnected_of_continuousOn_of_local_rigidity
      (by simpa [C] using
        (isPreconnected_connectedComponentIn : IsPreconnected C))
      hscont hncont
      ⟨z, by simpa [C] using mem_connectedComponentIn hzS, hseed⟩
  intro q hqC hEq
  rcases hlocal q (by simpa [S, n] using hCsub hqC) (by simpa [n] using hEq) with
    ⟨V, hV, hqV, hVS⟩
  refine ⟨V, hV, hqV, ?_⟩
  intro w hw
  exact hVS ⟨hw.1, by simpa [S, n] using hCsub hw.2⟩

/--
For a preconnected adjacent overlap, the canonical new-anchor seed and local
rigidity imply equality on the full overlap.  This is the seed-free
preconnected-overlap replacement for the componentwise interface.
-/
theorem chainAdjacent_eqOn_of_preconnected_overlap_of_local_rigidity
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (Lz : CartanMap.TangentAlignment g z (s.map z))
    (hzold : z ∈ s.germ.source)
    (hpre : IsPreconnected
      (s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source))
    (hlocal :
      ∀ q ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source,
        s.germ q =
            (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ q →
          ∃ V : Set M, IsOpen V ∧ q ∈ V ∧
            EqOn s.germ
              (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ
              (V ∩
                (s.germ.source ∩
                  (InducedAlignment.CompatibleStep.nextWithAlignment
                    s z Lz).germ.source))) :
    EqOn s.germ
      (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ
      (s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source) := by
  let n := InducedAlignment.CompatibleStep.nextWithAlignment s z Lz
  have hznew : z ∈ n.germ.source := by
    simpa [n] using chainAdjacent_anchor_mem_successor_source s z Lz
  have hseed : s.germ z = n.germ z := by
    simpa [n] using chainAdjacent_anchor_seed s z Lz
  apply
    CartanOverlapContinuation.openPartialHomeomorph_eqOn_of_preconnected_overlap_of_local_rigidity
      s.germ n.germ (by simpa [n] using hpre)
  · intro _hnonempty
    exact ⟨z, ⟨hzold, hznew⟩, hseed⟩
  · intro q hq hEq
    simpa [n] using hlocal q (by simpa [n] using hq) (by simpa [n] using hEq)

/--
For adjacent germs on a preconnected overlap, induced-alignment path
independence is now the only continuation input.  The value seed is canonical
at the new anchor, while the two rigid re-anchor steps and heterogeneous
alignment equality discharge local rigidity at every equality point.
-/
theorem chainAdjacent_eqOn_of_preconnected_overlap_of_alignment_pathIndependence
    [T2Space RoundSphere3]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M)
    (Lz : CartanMap.TangentAlignment g z (s.map z))
    (hzold : z ∈ s.germ.source)
    (hpre : IsPreconnected
      (s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source))
    (hpath :
      ∀ q ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source,
        (hvalue : s.map q =
          (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).map q) →
          ∃ (Ls : CartanMap.TangentAlignment g q (s.map q))
            (Ln : CartanMap.TangentAlignment g q
              ((InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).map q)),
            InducedAlignment.CompatibleStep.RigidStepCompatibleWith s q Ls ∧
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz) q Ln ∧
              HEq Ls Ln) :
    EqOn s.germ
      (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ
      (s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s z Lz).germ.source) := by
  let n := InducedAlignment.CompatibleStep.nextWithAlignment s z Lz
  apply chainAdjacent_eqOn_of_preconnected_overlap_of_local_rigidity
    s z Lz hzold hpre
  intro q hq hEq
  have hvalue : s.map q = n.map q := by
    simpa [n, CartanChain.ChainState.germ, CartanChain.ChainState.map] using hEq
  rcases hpath q (by simpa [n] using hq) (by simpa [n] using hvalue) with
    ⟨Ls, Ln, hs, hn, hL⟩
  simpa [n] using
    CartanLocalRigidity.locally_eq_of_rigidSteps_of_alignment_heq
      s n q Ls Ln hvalue hL hs hn

end CartanAdjacentContinuation
end Poincare
