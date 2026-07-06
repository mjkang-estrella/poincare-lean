import Poincare.Global.RoundSphereMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stereographic coordinates for the round three-sphere

This file records the first concrete coefficient computation for the round
metric on `S³`: the Euclidean pullback of the ambient metric by Mathlib's
stereographic inverse parametrization is conformal with factor
`16 / (‖z‖² + 4)²`.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare

section AmbientStereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rational conformal factor for Mathlib's `stereoInvFunAux` normalization. -/
def stereoInvFunAuxConformalFactor (z : E) : ℝ :=
  16 / (‖z‖ ^ 2 + 4) ^ 2

/-- The simplified Fréchet derivative of Mathlib's stereographic inverse auxiliary map. -/
noncomputable def stereoInvFunAuxFDeriv (v z : E) : E →L[ℝ] E :=
  (4 * (‖z‖ ^ 2 + 4)⁻¹) • ContinuousLinearMap.id ℝ E
    - (8 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2) • (innerSL ℝ z).smulRight z
    + (16 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2) • (innerSL ℝ z).smulRight v

theorem stereoInvFunAuxFDeriv_apply (v z u : E) :
    stereoInvFunAuxFDeriv v z u =
      (4 * (‖z‖ ^ 2 + 4)⁻¹) • u
        - (8 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ z u) • z
        + (16 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ z u) • v := by
  simp [stereoInvFunAuxFDeriv, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, mul_assoc, smul_smul]

theorem hasFDerivAt_stereoInvFunAuxFDeriv (v z : E) :
    HasFDerivAt (stereoInvFunAux v) (stereoInvFunAuxFDeriv v z) z := by
  let r : ℝ := ‖z‖ ^ 2 + 4
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hnorm :
      HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hinv :
      HasFDerivAt (fun y : E => (‖y‖ ^ 2 + 4)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(r ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
          (2 • innerSL ℝ z)) z := by
    have hsum :
        HasFDerivAt (fun y : E => ‖y‖ ^ 2 + 4) (2 • innerSL ℝ z) z := by
      exact hnorm.add_const 4
    simpa [r] using (hasFDerivAt_inv hrpos.ne').comp z hsum
  have hvec :
      HasFDerivAt
        (fun y : E => (4 : ℝ) • y + (‖y‖ ^ 2 - 4) • v)
        ((4 : ℝ) • ContinuousLinearMap.id ℝ E + (2 • innerSL ℝ z).smulRight v) z := by
    convert
      ((hasFDerivAt_const (4 : ℝ) z).smul (hasFDerivAt_id z)).add
        ((hnorm.sub (hasFDerivAt_const (4 : ℝ) z)).smul
          (hasFDerivAt_const v z)) using 1
    · ext y
      simp
  have hprod := hinv.smul hvec
  convert hprod using 1
  ext u
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hvcoeff :
      16 * (((‖z‖ ^ 2 + 4) ^ 2)⁻¹ * inner ℝ z u) =
        (‖z‖ ^ 2 + 4)⁻¹ * (2 * inner ℝ z u)
          + (-(2 * (inner ℝ z u * (((‖z‖ ^ 2 + 4) ^ 2)⁻¹ * ‖z‖ ^ 2)))
            + 2 * (inner ℝ z u * (((‖z‖ ^ 2 + 4) ^ 2)⁻¹ * 4))) := by
    field_simp [hden]
    ring
  rw [stereoInvFunAuxFDeriv_apply]
  simp [r, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.smulRight_apply, Function.comp_def,
    smul_add, add_smul, smul_smul, sub_eq_add_neg, mul_assoc]
  rw [hvcoeff]
  module

theorem fderiv_stereoInvFunAux (v z : E) :
    fderiv ℝ (stereoInvFunAux v) z = stereoInvFunAuxFDeriv v z :=
  (hasFDerivAt_stereoInvFunAuxFDeriv v z).fderiv

theorem fderiv_stereoInvFunAux_comp_subtype (v : E) (z : (ℝ ∙ v)ᗮ) :
    fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z =
      (stereoInvFunAuxFDeriv v (z : E)).comp (ℝ ∙ v)ᗮ.subtypeL := by
  have hsub :
      HasFDerivAt ((↑) : (ℝ ∙ v)ᗮ → E) (ℝ ∙ v)ᗮ.subtypeL z := by
    simpa using (ℝ ∙ v)ᗮ.subtypeL.hasFDerivAt
  exact ((hasFDerivAt_stereoInvFunAuxFDeriv v (z : E)).comp z hsub).fderiv

theorem inner_stereoInvFunAuxFDeriv_of_mem_orthogonal {v z u w : E}
    (hv : ‖v‖ = 1) (hz : z ∈ (ℝ ∙ v)ᗮ)
    (hu : u ∈ (ℝ ∙ v)ᗮ) (hw : w ∈ (ℝ ∙ v)ᗮ) :
    inner ℝ (stereoInvFunAuxFDeriv v z u) (stereoInvFunAuxFDeriv v z w) =
      stereoInvFunAuxConformalFactor z * inner ℝ u w := by
  have hzv : inner ℝ v z = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hz
  have huv : inner ℝ v u = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu
  have hwv : inner ℝ v w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hzv' : inner ℝ z v = 0 := by simpa [real_inner_comm] using hzv
  have huv' : inner ℝ u v = 0 := by simpa [real_inner_comm] using huv
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  rw [stereoInvFunAuxFDeriv_apply, stereoInvFunAuxFDeriv_apply]
  simp [stereoInvFunAuxConformalFactor, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hzv, hzv', huv', hwv, real_inner_comm, mul_assoc]
  field_simp [hden]
  simp [hv]
  ring

theorem inner_fderiv_stereoInvFunAux_comp_subtype (v : E) (hv : ‖v‖ = 1)
    (z u w : (ℝ ∙ v)ᗮ) :
    inner ℝ
        (fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z u)
        (fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) z w) =
      stereoInvFunAuxConformalFactor (z : E) * inner ℝ u w := by
  rw [fderiv_stereoInvFunAux_comp_subtype]
  simpa using
    inner_stereoInvFunAuxFDeriv_of_mem_orthogonal (v := v) (z := (z : E))
      (u := (u : E)) (w := (w : E)) hv z.2 u.2 w.2

end AmbientStereographic

end Poincare
