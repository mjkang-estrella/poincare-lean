/-
Chart identifications for tangent spaces.

In Mathlib, the tangent space at `x` is the model space `E`, identified
through the extended chart at `x`.  This module makes that identification
explicit: the manifold derivative of `extChartAt I x` at `x` itself is the
identity, and consequently the manifold Lie bracket at `x` is literally the
vector-space Lie bracket (within `range I`) of the pulled-back fields at the
chart image.  These are the base identities for transferring second-order
identities (the bracket-derivation property, curvature tensoriality) from
the model space to manifolds.
-/

import Mathlib.Geometry.Manifold.VectorField.LieBracket

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/--
The manifold Lie bracket at `x` is the vector-space Lie bracket of the
pulled-back fields, evaluated at the chart image of `x`.
-/
theorem mlieBracket_apply_chart (X Y : Π y : M, TangentSpace I y) (x : M) :
    VectorField.mlieBracket I X Y x =
      VectorField.lieBracketWithin 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X
          (range I))
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y
          (range I))
        (range I) (extChartAt I x x) := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_apply, mfderiv_extChartAt_self]
  simp only [preimage_univ, univ_inter]
  have key : ∀ v : TangentSpace I x,
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)).inverse v = v := by
    intro v
    rw [ContinuousLinearMap.inverse_id]
    rfl
  exact key _

/--
The pullback of a vector field under the inverse chart, evaluated at the
chart image of the base point, is the original vector at the base point.
-/
theorem mpullbackWithin_extChartAt_symm_self
    (X : Π y : M, TangentSpace I y) (x : M) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I)
      (extChartAt I x x) = X x := by
  rw [VectorField.mpullbackWithin]
  have h2 : mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 E := by
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (mem_extChartAt_source (I := I) x)
    rw [mfderiv_extChartAt_self] at hcomp
    simpa using hcomp
  rw [h2]
  have key : ∀ v : TangentSpace I x,
      (ContinuousLinearMap.id 𝕜 E).inverse v = v := by
    intro v
    rw [ContinuousLinearMap.inverse_id]
    rfl
  rw [show (extChartAt I x).symm (extChartAt I x x) = x from
    (extChartAt I x).left_inv (mem_extChartAt_source x)]
  exact key _

section Boundaryless

variable [I.Boundaryless]

omit [IsManifold I 1 M] in
/--
On a boundaryless manifold, the exterior derivative of a scalar function at
`x` is the ordinary derivative of the chart representative at the chart
image.
-/
theorem extDerivFun_apply_chart {f : M → 𝕜} {x : M} (hf : MDiffAt f x)
    (v : TangentSpace I x) :
    extDerivFun f x v =
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
  have h1 : mfderiv% f x =
      fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x f) (range I)
        (extChartAt I x x) := by
    rw [mfderiv, if_pos hf]
  have h2 : writtenInExtChartAt I 𝓘(𝕜, 𝕜) x f =
      f ∘ (extChartAt I x).symm := by
    funext z
    simp [writtenInExtChartAt]
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, h1, h2,
    I.range_eq_univ, fderivWithin_univ]
  rfl

end Boundaryless
