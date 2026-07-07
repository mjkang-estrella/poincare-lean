import Poincare.Global.GeodesicPreservation

/-!
# Off-anchor exponential naturality from re-centered Cartan germs

This module isolates the strict-partial bridge after the genuine re-centering
input is known: if the carried Cartan germ and the explicitly re-anchored germ
agree on their common strict source, then the anchor-based exponential
naturality identity becomes the off-anchor identity for the carried map.

The remaining hard input is still the non-vacuous production of the
`RigidStepCompatibleWith` hypothesis, i.e. identifying the old germ with the
new-anchor Cartan germ on an overlap.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace OffAnchorNaturality

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Strict off-anchor exponential naturality for the carried Cartan map, assuming
the old germ has already been re-centered to the explicitly aligned new-anchor
Cartan germ on the common source.
-/
theorem carried_target_chart_exp_naturality_of_rigidStepCompatibleWith
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (hcompat : InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁)
    {x : M}
    (hx :
      x ∈ s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source) :
    GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) (s.map x₁)
        (L₁
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₁).symm ((chartAt E x₁) x))) =
      (chartAt E (s.map x₁)) (s.map x) := by
  have hx_new :
      x ∈ (CartanMap.openPartialHomeomorph g x₁ (s.map x₁) L₁).source := by
    simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ] using hx.2
  have hanchor :=
    GeodesicPreservation.cartanMap_target_chart_exp_naturality
      (g := g) (x₀ := x₁) (p₀ := s.map x₁) L₁ (x := x) hx_new
  have hmap :
      CartanMap.cartanMap g x₁ (s.map x₁) L₁ x = s.map x := by
    have hpoint := hcompat hx
    simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ, CartanChain.ChainState.map] using hpoint.symm
  rw [hanchor, hmap]

end OffAnchorNaturality
end Poincare

