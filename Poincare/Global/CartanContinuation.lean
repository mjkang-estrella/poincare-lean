import Poincare.Global.TangentAlignmentExists

/-!
# Cartan continuation staging lemmas

This module records the first globalization glue for the Cartan germ.  The
local Cartan map is already an `OpenPartialHomeomorph` determined by its source
anchor, target value, and tangent alignment.  The lemmas here package that
determinacy and the first re-anchoring step used in Cartan--Ambrose--Hicks
continuation.

The still-missing rigid input is intentionally left as an equality-on-common-
source hypothesis in `twoStep_restr_eqOnSource_of_differential_action`: rigid
local-isometry work should prove that hypothesis from equality of the
first-order Cartan data at the re-anchor.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanContinuation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The local Cartan `OpenPartialHomeomorph` is determined by its anchor data.

This is the formal seed for the "same value and same tangent action imply the
same Cartan germ" step: once the source anchor and target value have been
identified, heterogeneous equality of the tangent-alignment data identifies the
actual partial homeomorphisms.
-/
theorem openPartialHomeomorph_eq_of_anchor_data_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    {p₁ p₂ : RoundSphere3} (hp : p₁ = p₂)
    {L₁ : CartanMap.TangentAlignment g x₀ p₁}
    {L₂ : CartanMap.TangentAlignment g x₀ p₂}
    (hL : HEq L₁ L₂) :
    CartanMap.openPartialHomeomorph g x₀ p₁ L₁ =
      CartanMap.openPartialHomeomorph g x₀ p₂ L₂ := by
  subst hp
  cases hL
  rfl

/-- Function-level determinacy of the Cartan map from the same anchor data. -/
theorem cartanMap_eq_of_anchor_data_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    {p₁ p₂ : RoundSphere3} (hp : p₁ = p₂)
    {L₁ : CartanMap.TangentAlignment g x₀ p₁}
    {L₂ : CartanMap.TangentAlignment g x₀ p₂}
    (hL : HEq L₁ L₂) :
    CartanMap.cartanMap g x₀ p₁ L₁ =
      CartanMap.cartanMap g x₀ p₂ L₂ := by
  subst hp
  cases hL
  rfl

/--
Same anchor data gives agreement on the common normal source.

The set is written as a common-source intersection because later continuation
uses this exact shape after re-anchoring, when equality is supplied by the
constant-curvature differential action rather than by definitional equality.
-/
theorem cartanMap_eqOn_common_source_of_anchor_data_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    {p₁ p₂ : RoundSphere3} (hp : p₁ = p₂)
    {L₁ : CartanMap.TangentAlignment g x₀ p₁}
    {L₂ : CartanMap.TangentAlignment g x₀ p₂}
    (hL : HEq L₁ L₂) :
    EqOn (CartanMap.cartanMap g x₀ p₁ L₁)
      (CartanMap.cartanMap g x₀ p₂ L₂)
      ((CartanMap.openPartialHomeomorph g x₀ p₁ L₁).source ∩
        (CartanMap.openPartialHomeomorph g x₀ p₂ L₂).source) := by
  have hmap :=
    cartanMap_eq_of_anchor_data_eq (g := g) (x₀ := x₀) hp (L₁ := L₁) (L₂ := L₂) hL
  intro x _hx
  exact congr_fun hmap x

/--
The re-anchored Cartan germ at `x₁`, with target value supplied by the previous
Cartan map.
-/
def reanchoredOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) (x₁ : M)
    (L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)) :
    OpenPartialHomeomorph M RoundSphere3 :=
  CartanMap.openPartialHomeomorph g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁

/-- The re-anchored germ sends its new source anchor to the continued target value. -/
theorem reanchored_cartanMap_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) (x₁ : M)
    (L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)) :
    CartanMap.cartanMap g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁ x₁ =
      CartanMap.cartanMap g x₀ p₀ L₀ x₁ := by
  simpa using
    CartanMap.cartanMap_anchor
      (g := g) (x₀ := x₁) (p₀ := CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁

/-- If `x₁` lies in the first normal source, its continued value lies in the first target. -/
theorem firstStep_value_mem_target
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    {L₀ : CartanMap.TangentAlignment g x₀ p₀} {x₁ : M}
    (hx₁ : x₁ ∈ (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source) :
    CartanMap.cartanMap g x₀ p₀ L₀ x₁ ∈
      (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).target :=
  (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).map_source hx₁

/-- The new anchor belongs to the source of the re-anchored normal germ. -/
theorem reanchored_anchor_mem_source
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) (x₁ : M)
    (L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)) :
    x₁ ∈ (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source := by
  exact
    CartanMap.anchor_mem_source
      (g := g) (x₀ := x₁) (p₀ := CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁

/-- The continued target value belongs to the target of the re-anchored normal germ. -/
theorem reanchored_anchor_mem_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) (x₁ : M)
    (L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)) :
    CartanMap.cartanMap g x₀ p₀ L₀ x₁ ∈
      (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).target := by
  exact
    CartanMap.anchor_mem_target
      (g := g) (x₀ := x₁) (p₀ := CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁

/--
Every point admits a re-anchored Cartan germ with the continued target value.

This uses the existing tangent-alignment existence theorem, not a new
certificate.
-/
theorem exists_reanchoredOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) (x₁ : M) :
    ∃ L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁),
      x₁ ∈ (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source ∧
        CartanMap.cartanMap g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁ x₁ =
          CartanMap.cartanMap g x₀ p₀ L₀ x₁ := by
  rcases CartanMap.tangentAlignment_nonempty
      (g := g) (x₀ := x₁) (p₀ := CartanMap.cartanMap g x₀ p₀ L₀ x₁) with
    ⟨L₁⟩
  exact
    ⟨L₁, reanchored_anchor_mem_source g x₀ p₀ L₀ x₁ L₁,
      reanchored_cartanMap_anchor g x₀ p₀ L₀ x₁ L₁⟩

/--
Two-step Cartan continuation, restricted to the common source.

The hypothesis is the intended rigid-10 output shape: after re-anchoring at
`x₁`, the original Cartan germ and the re-anchored germ agree on the common
normal source because their value and tangent action at `x₁` match.  This lemma
turns that pointwise equality into Mathlib's source-equivalence of restricted
open partial homeomorphisms, which is the form needed for later gluing.
-/
theorem twoStep_restr_eqOnSource_of_differential_action
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    {L₀ : CartanMap.TangentAlignment g x₀ p₀} {x₁ : M}
    {L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)}
    (hDifferentialAction :
      EqOn (CartanMap.openPartialHomeomorph g x₀ p₀ L₀)
        (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁)
        ((CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source ∩
          (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source)) :
    (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).restr
        (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source ≈
      (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).restr
        (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source := by
  exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hDifferentialAction

/-- Pointwise form of the two-step continuation agreement. -/
theorem twoStep_cartanMap_eq_of_differential_action
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    {L₀ : CartanMap.TangentAlignment g x₀ p₀} {x₁ x₂ : M}
    {L₁ : CartanMap.TangentAlignment g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁)}
    (hDifferentialAction :
      EqOn (CartanMap.openPartialHomeomorph g x₀ p₀ L₀)
        (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁)
        ((CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source ∩
          (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source))
    (hx₂ :
      x₂ ∈ (CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source ∩
        (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source) :
    CartanMap.cartanMap g x₁ (CartanMap.cartanMap g x₀ p₀ L₀ x₁) L₁ x₂ =
      CartanMap.cartanMap g x₀ p₀ L₀ x₂ := by
  exact (hDifferentialAction hx₂).symm

end CartanContinuation
end Poincare
