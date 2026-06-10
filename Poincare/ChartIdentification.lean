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
