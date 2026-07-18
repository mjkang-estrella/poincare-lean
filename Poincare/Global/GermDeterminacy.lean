import Poincare.Global.CartanChain
import Poincare.Global.CartanNormalCoords

/-!
# Cartan germ determinacy from the linear tangent action

This module isolates the formal determinacy step that is available from the
current Cartan-germ interface: once two same-anchor Cartan germs have the same
target value and the same underlying linear tangent action, they agree on the
common strict source.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace GermDeterminacy

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Same-anchor Cartan germs with the same target value are determined by the
underlying linear tangent action.

The first conjunct is the explicit normal-coordinate overlap statement:
after conjugating by the source and target exponential partial homeomorphisms,
both chart Cartan maps read as the same linear map.  The second conjunct is the
corresponding strict germ agreement on the common source.  For successors made
by `CartanChain.ChainState.next`, equality of the target indices identifies the
two `Classical.choice` alignments automatically; the remaining geometric input
is compatibility of each carried germ with its re-anchored successor.
-/
theorem cartanGerm_determinacy_of_tangentAlignment_apply_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    {L₁ L₂ : CartanMap.TangentAlignment g x₀ p₀}
    (hL : ∀ v : E, L₁ v = L₂ v) :
    EqOn (CartanDifferential.cartanChartMap g x₀ p₀ L₁)
        (CartanDifferential.cartanChartMap g x₀ p₀ L₂)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) ''
          (((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source ∩
              {v : E | L₁ v ∈
                (GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀).source}) ∩
            {v : E | L₂ v ∈
              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀).source})) ∧
      EqOn (CartanMap.openPartialHomeomorph g x₀ p₀ L₁)
        (CartanMap.openPartialHomeomorph g x₀ p₀ L₂)
        ((CartanMap.openPartialHomeomorph g x₀ p₀ L₁).source ∩
          (CartanMap.openPartialHomeomorph g x₀ p₀ L₂).source) := by
  constructor
  · intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    rcases hv with ⟨⟨hvsrc, hvtgt₁⟩, hvtgt₂⟩
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
    let eS :=
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀
    have hconj₁ :
        eS.symm
          (CartanDifferential.cartanChartMap g x₀ p₀ L₁ (eM v)) = L₁ v := by
      simpa [eM, eS] using
        CartanNormalCoords.expChart_symm_cartanChartMap_expChart_eq_tangentAlignment
          (g := g) (x₀ := x₀) (p₀ := p₀) L₁ hvsrc hvtgt₁
    have hconj₂ :
        eS.symm
          (CartanDifferential.cartanChartMap g x₀ p₀ L₂ (eM v)) = L₂ v := by
      simpa [eM, eS] using
        CartanNormalCoords.expChart_symm_cartanChartMap_expChart_eq_tangentAlignment
          (g := g) (x₀ := x₀) (p₀ := p₀) L₂ hvsrc hvtgt₂
    have hsymm :
        eS.symm
            (CartanDifferential.cartanChartMap g x₀ p₀ L₁ (eM v)) =
          eS.symm
            (CartanDifferential.cartanChartMap g x₀ p₀ L₂ (eM v)) := by
      calc
        eS.symm
            (CartanDifferential.cartanChartMap g x₀ p₀ L₁ (eM v)) = L₁ v := hconj₁
        _ = L₂ v := hL v
        _ = eS.symm
            (CartanDifferential.cartanChartMap g x₀ p₀ L₂ (eM v)) := hconj₂.symm
    have hleft : eM.symm (eM v) = v :=
      eM.left_inv hvsrc
    have hchart₁ :
        CartanDifferential.cartanChartMap g x₀ p₀ L₁ (eM v) =
          eS (L₁ v) := by
      change eS (L₁ (eM.symm (eM v))) = eS (L₁ v)
      rw [hleft]
    have hchart₂ :
        CartanDifferential.cartanChartMap g x₀ p₀ L₂ (eM v) =
          eS (L₂ v) := by
      change eS (L₂ (eM.symm (eM v))) = eS (L₂ v)
      rw [hleft]
    have htgt₁ :
        CartanDifferential.cartanChartMap g x₀ p₀ L₁ (eM v) ∈ eS.target := by
      rw [hchart₁]
      exact eS.map_source hvtgt₁
    have htgt₂ :
        CartanDifferential.cartanChartMap g x₀ p₀ L₂ (eM v) ∈ eS.target := by
      rw [hchart₂]
      exact eS.map_source hvtgt₂
    exact eS.symm.injOn htgt₁ htgt₂ hsymm
  · have hL_eq : L₁ = L₂ := by
      exact DFunLike.ext L₁ L₂ hL
    cases hL_eq
    intro x _hx
    rfl

end GermDeterminacy
end Poincare
