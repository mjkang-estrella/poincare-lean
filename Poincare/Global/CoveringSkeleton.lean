import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Lifting

/-!
# Abstract covering-space globalization skeleton

This file isolates the pure topology used by the rigidity endgame: compact
local homeomorphisms give covering maps, and a covering map over a simply
connected locally path connected base with connected total space is a
homeomorphism.
-/

noncomputable section

open Function Set Topology
open scoped ContinuousMap

universe u v

namespace Poincare
namespace GlobalCoveringSkeleton

variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

omit [TopologicalSpace E] in
/--
A nonempty clopen image in a preconnected target is all of the target.

This is the elementary surjectivity step for local-homeomorphism images once
closedness has been supplied separately.
-/
theorem surjective_of_isOpen_isClosed_range [PreconnectedSpace X] [Nonempty E]
    (hopen : IsOpen (range p)) (hclosed : IsClosed (range p)) :
    Surjective p := by
  have hclopen : IsClopen (range p) := ⟨hclosed, hopen⟩
  have hrange : range p = univ := hclopen.eq_univ (range_nonempty p)
  intro x
  have hx : x ∈ range p := by
    simp [hrange]
  simpa [mem_range] using hx

/--
A local homeomorphism with closed image into a preconnected target is
surjective, provided the total space is nonempty.
-/
theorem IsLocalHomeomorph.surjective_of_isClosed_range [PreconnectedSpace X] [Nonempty E]
    (hp : IsLocalHomeomorph p) (hclosed : IsClosed (range p)) :
    Surjective p :=
  surjective_of_isOpen_isClosed_range
    (by simpa using hp.isOpenMap univ isOpen_univ) hclosed

/--
Compact Hausdorff source plus local homeomorphism gives a covering map.

This is a thin wrapper around Mathlib's compact `OpenPartialHomeomorph`
criterion for `IsCoveringMapOn`, specialized to the whole target.
-/
theorem isCoveringMap_of_compact_isLocalHomeomorph
    [T2Space E] [T2Space X] [CompactSpace E]
    (hp : IsLocalHomeomorph p) :
    IsCoveringMap p := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsCoveringMapOn.of_openPartialHomeomorph
    (f := p) (s := univ) hp.continuous fun e _he => by
      rcases hp e with ⟨φ, hφ_source, hφ_eq⟩
      exact ⟨φ, hφ_source, hφ_eq.symm⟩

/--
A covering map with connected total space over a simply connected locally path
connected base is bijective.

Mathlib covering maps are not definitionally surjective. Here surjectivity and
injectivity are both extracted from the lifting theorem applied to
`id : X → X` and the uniqueness of lifts from the connected total space.
-/
theorem bijective_of_isCoveringMap_simplyConnected
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hp : IsCoveringMap p) :
    Bijective p := by
  let e₀ : E := Classical.arbitrary E
  let idX : C(X, X) := ContinuousMap.id X
  rcases hp.existsUnique_continuousMap_lifts idX (p e₀) e₀ rfl with
    ⟨F, hF, _hF_unique⟩
  have hright : ∀ x : X, p (F x) = x := by
    intro x
    simpa [idX] using congr_fun hF.2 x
  have hcomp : p ∘ (F ∘ p) = p ∘ id := by
    funext e
    simpa [Function.comp_def] using hright (p e)
  have hsection : F ∘ p = id :=
    hp.eq_of_comp_eq
      (g₁ := F ∘ p) (g₂ := id)
      (F.continuous.comp hp.continuous) continuous_id
      hcomp e₀ (by simpa using hF.1)
  refine ⟨?_, ?_⟩
  · intro e₁ e₂ heq
    calc
      e₁ = F (p e₁) := by simpa [Function.comp_def] using congr_fun hsection e₁ |>.symm
      _ = F (p e₂) := by rw [heq]
      _ = e₂ := by simpa [Function.comp_def] using congr_fun hsection e₂
  · intro x
    exact ⟨F x, hright x⟩

/--
The unbundled homeomorphism statement for the globalization endgame.
-/
theorem isHomeomorph_of_isCoveringMap_simplyConnected
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hp : IsCoveringMap p) :
    IsHomeomorph p :=
  ⟨hp.continuous, hp.isOpenMap, bijective_of_isCoveringMap_simplyConnected hp⟩

/--
Bundled homeomorphism version of
`isHomeomorph_of_isCoveringMap_simplyConnected`.
-/
def homeomorphOfIsCoveringMapSimplyConnected
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hp : IsCoveringMap p) :
    E ≃ₜ X :=
  hp.isLocalHomeomorph.toHomeomorphOfBijective
    (bijective_of_isCoveringMap_simplyConnected hp)

end GlobalCoveringSkeleton
end Poincare
