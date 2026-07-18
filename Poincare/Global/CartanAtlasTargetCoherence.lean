import Poincare.Global.UnitRecognitionNext

/-!
# Target coherence forced by a compatible Cartan atlas

The target point of the Cartan germ based at `x` is the value of the eventual
developing map at `x`.  It is therefore not an arbitrary pointwise choice.
This file makes that constraint explicit: overlap compatibility forces every
target `p y` to be the value at `y` of every earlier germ whose source contains
`y`.

In particular, a constant target field can only be compatible if every Cartan
germ source contains no point other than its anchor.  This rules out treating a
fixed north-pole target as an automatic replacement for the genuine
path-continuation construction.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

omit [T2Space M] in
/-- Pairwise agreement determines the target at `y` from any compatible germ
whose source contains `y`. -/
theorem cartanAtlas_target_eq_germ_value
    (g : ClosedSmoothRiemannianMetric 3 M)
    (p : M → RoundSphere3)
    (L : ∀ x : M, CartanMap.TangentAlignment g x (p x))
    (hcompat : ∀ x y : M,
      EqOn
        (CartanMap.openPartialHomeomorph g x (p x) (L x))
        (CartanMap.openPartialHomeomorph g y (p y) (L y))
        ((CartanMap.openPartialHomeomorph g x (p x) (L x)).source ∩
          (CartanMap.openPartialHomeomorph g y (p y) (L y)).source))
    {x y : M}
    (hy : y ∈ (CartanMap.openPartialHomeomorph g x (p x) (L x)).source) :
    p y = CartanMap.openPartialHomeomorph g x (p x) (L x) y := by
  have hyy :
      y ∈ (CartanMap.openPartialHomeomorph g y (p y) (L y)).source :=
    CartanMap.anchor_mem_source g y (p y) (L y)
  have hagree := hcompat x y ⟨hy, hyy⟩
  calc
    p y = CartanMap.openPartialHomeomorph g y (p y) (L y) y := by
      simpa [CartanMap.openPartialHomeomorph] using
        (CartanMap.cartanMap_anchor
          (g := g) (x₀ := y) (p₀ := p y) (L y)).symm
    _ = CartanMap.openPartialHomeomorph g x (p x) (L x) y := hagree.symm

omit [T2Space M] in
/-- If a compatible atlas uses one constant target point, membership in a
germ source forces equality with that germ's anchor.  A genuine developing
atlas on a positive-dimensional manifold must therefore construct its target
field by continuation rather than choose it constantly. -/
theorem eq_anchor_of_mem_cartan_source_of_constant_compatible_target
    (g : ClosedSmoothRiemannianMetric 3 M)
    (p : M → RoundSphere3)
    (L : ∀ x : M, CartanMap.TangentAlignment g x (p x))
    (hcompat : ∀ x y : M,
      EqOn
        (CartanMap.openPartialHomeomorph g x (p x) (L x))
        (CartanMap.openPartialHomeomorph g y (p y) (L y))
        ((CartanMap.openPartialHomeomorph g x (p x) (L x)).source ∩
          (CartanMap.openPartialHomeomorph g y (p y) (L y)).source))
    (p₀ : RoundSphere3) (hp : ∀ z : M, p z = p₀)
    {x y : M}
    (hy : y ∈ (CartanMap.openPartialHomeomorph g x (p x) (L x)).source) :
    y = x := by
  let F := CartanMap.openPartialHomeomorph g x (p x) (L x)
  have hx : x ∈ F.source :=
    CartanMap.anchor_mem_source g x (p x) (L x)
  have hFy : F y = p y := by
    exact (cartanAtlas_target_eq_germ_value g p L hcompat hy).symm
  have hFx : F x = p x := by
    simpa [F, CartanMap.openPartialHomeomorph] using
      CartanMap.cartanMap_anchor
        (g := g) (x₀ := x) (p₀ := p x) (L x)
  apply F.injOn hy hx
  rw [hFy, hFx, hp y, hp x]

end Poincare
