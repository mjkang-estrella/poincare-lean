/-
Tensoriality of the curvature in the field slot.

This module proves the Leibniz expansion of the Riemann curvature operator
in its field slot: `R(X,Y)(f • Z) = f • R(X,Y)Z` at every point where `f`
and `Z` are `C²` and `X, Y` are differentiable, on a boundaryless smooth
finite-dimensional real manifold with a `C¹` connection.  The first-order
cross terms cancel pairwise, and the second-order defect
`X(Yf) - Y(Xf) - [X,Y]f` vanishes by the bracket-derivation identity.
-/

import Poincare.LocalConnectionRegularity
import Poincare.ChartIdentification

noncomputable section

open Bundle Set FiberBundle Filter VectorField
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable [ContMDiffCovariantDerivative cov 1]

/--
The scalar function `y ↦ df(U y)` is differentiable at `x` when `f` is `C²`
and `U` is differentiable at `x`.
-/
theorem mdiffAt_extDerivFun_apply {f : M → ℝ} {x : M}
    (hf : CMDiffAt 2 f x) {U : Π y : M, TangentSpace I y}
    (hU : MDiffAt (T% U) x) :
    MDiffAt (fun y ↦ extDerivFun f y (U y)) x := by
  have hFc : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm)
      (extChartAt I x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [I.range_eq_univ, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I x).symm =
        f ∘ (extChartAt I x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hinv : (mfderiv% (extChartAt I x).symm
      (extChartAt I x x)).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm
      (mem_extChartAt_target (I := I) x)
    rwa [I.range_eq_univ, mfderivWithin_univ] at h
  have hpull : DifferentiableAt ℝ
      (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm U) (extChartAt I x x) := by
    have hsm : CMDiffAt 2 ((extChartAt I x).symm : E → M)
        (extChartAt I x x) := by
      have h := contMDiffWithinAt_extChartAt_symm_range (n := 2) x
        (mem_extChartAt_target (I := I) x)
      rwa [I.range_eq_univ, contMDiffWithinAt_univ] at h
    have hU' : MDiffAt[univ] (T% U)
        ((extChartAt I x).symm (extChartAt I x x)) := by
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x),
        mdifferentiableWithinAt_univ]
      exact hU
    have h := hU'.mpullback_vectorField_preimage hsm hinv le_rfl
    rw [preimage_univ, mdifferentiableWithinAt_univ] at h
    exact mdiffAt_vectorSpace_iff_differentiableAt.mp h
  have hcd : DifferentiableAt ℝ
      (fun z ↦ fderiv ℝ (f ∘ (extChartAt I x).symm) z
        (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm U z))
      (extChartAt I x x) := by
    apply DifferentiableAt.clm_apply
    · exact (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero
    · exact hpull
  refine MDifferentiableAt.congr_of_eventuallyEq ?_
    ((extDerivFun_section_eventually_chart hf U).mono fun y hy ↦ hy)
  exact (mdifferentiableAt_iff_differentiableAt.mpr hcd).comp x
    (mdifferentiableAt_extChartAt (mem_chart_source H x))

/--
**Tensoriality of the curvature operator in the field slot** (Leibniz
expansion): `R(X,Y)(f • Z) = f • R(X,Y)Z` pointwise, for `f, Z` `C²` and
`X, Y` differentiable at `x`.
-/
theorem curvatureOp_smul_field {f : M → ℝ}
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt 2 f x) (hZ : CMDiffAt 2 (T% Z) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvatureOp cov X Y (f • Z) x = f x • curvatureOp cov X Y Z x := by
  have hcovD := cov.isCovariantDerivativeOnUniv
  -- Differentiability of `f` and `Z` near `x`.
  have hfd : ∀ᶠ y in 𝓝 x, MDiffAt f y := by
    obtain ⟨v, hv, hfv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hf
    filter_upwards [interior_mem_nhds.mpr hv] with y hy
    exact (((hfv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hZd : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := by
    obtain ⟨v, hv, hZv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
    filter_upwards [interior_mem_nhds.mpr hv] with y hy
    exact (((hZv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hfx : MDiffAt f x := hf.mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hfZ : CMDiffAt 2 (T% (f • Z)) x := hf.smul_section hZ
  -- The Leibniz section identity near `x`, applied to a direction field.
  have hsec : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ cov (f • Z) y (W y)) =ᶠ[𝓝 x]
        fun y ↦ f y • cov Z y (W y) + extDerivFun f y (W y) • Z y := by
    intro W
    filter_upwards [hfd, hZd] with y hfy hZy
    rw [hcovD.leibniz hZy hfy]
    simp
  -- Names for the inner sections.
  set DY : Π y : M, TangentSpace I y := fun y ↦ cov Z y (Y y) with hDY
  set DX : Π y : M, TangentSpace I y := fun y ↦ cov Z y (X y) with hDX
  set gY : M → ℝ := fun y ↦ extDerivFun f y (Y y) with hgY
  set gX : M → ℝ := fun y ↦ extDerivFun f y (X y) with hgX
  -- Differentiability of all ingredients at `x`.
  have hDYd : MDiffAt (T% DY) x := mdiffAt_cov_section_of_contMDiffAt cov hZ hY
  have hDXd : MDiffAt (T% DX) x := mdiffAt_cov_section_of_contMDiffAt cov hZ hX
  have hgYd : MDiffAt gY x := mdiffAt_extDerivFun_apply hf hY
  have hgXd : MDiffAt gX x := mdiffAt_extDerivFun_apply hf hX
  have hA'Y : MDiffAt (T% (f • DY + gY • Z)) x :=
    mdifferentiableAt_add_section (hfx.smul_section hDYd)
      (hgYd.smul_section hZx)
  have hA'X : MDiffAt (T% (f • DX + gX • Z)) x :=
    mdifferentiableAt_add_section (hfx.smul_section hDXd)
      (hgXd.smul_section hZx)
  have hAY : MDiffAt (T% (fun y ↦ cov (f • Z) y (Y y))) x :=
    mdiffAt_cov_section_of_contMDiffAt cov hfZ hY
  have hAX : MDiffAt (T% (fun y ↦ cov (f • Z) y (X y))) x :=
    mdiffAt_cov_section_of_contMDiffAt cov hfZ hX
  -- Replace the iterated sections through germ locality.
  have hrepl : ∀ (W : Π y : M, TangentSpace I y) (DW : _) (gW : M → ℝ),
      DW = (fun y ↦ cov Z y (W y)) → gW = (fun y ↦ extDerivFun f y (W y)) →
      MDiffAt (T% (fun y ↦ cov (f • Z) y (W y))) x →
      MDiffAt (T% (f • DW + gW • Z)) x →
      cov (fun y ↦ cov (f • Z) y (W y)) x =
        cov (f • DW + gW • Z) x := by
    intro W DW gW hDWdef hgWdef hAW hA'W
    apply hcovD.congr_of_eventuallyEq hAW hA'W univ_mem
    filter_upwards [hsec W] with y hy
    rw [hy, hDWdef, hgWdef]
    simp
  have e1 := hrepl Y DY gY rfl rfl hAY hA'Y
  have e2 := hrepl X DX gX rfl rfl hAX hA'X
  -- Expand the outer derivatives by additivity and Leibniz at `x`.
  have hexp : ∀ (DW : Π y : M, TangentSpace I y) (gW : M → ℝ),
      MDiffAt (T% DW) x → MDiffAt gW x →
      cov (f • DW + gW • Z) x =
        f x • cov DW x + (extDerivFun f x).smulRight (DW x)
        + (gW x • cov Z x + (extDerivFun gW x).smulRight (Z x)) := by
    intro DW gW hDWd hgWd
    rw [hcovD.add (hfx.smul_section hDWd) (hgWd.smul_section hZx),
      hcovD.leibniz hDWd hfx, hcovD.leibniz hZx hgWd]
  rw [hexp DY gY hDYd hgYd] at e1
  rw [hexp DX gX hDXd hgXd] at e2
  -- Leibniz for the bracket term at `x`.
  have e3 : cov (f • Z) x (mlieBracket I X Y x) =
      f x • cov Z x (mlieBracket I X Y x)
        + extDerivFun f x (mlieBracket I X Y x) • Z x := by
    rw [hcovD.leibniz hZx hfx]
    simp
  -- The bracket-derivation identity kills the second-order defect.
  have e4 := extDerivFun_apply_mlieBracket hf hX hY
  -- Assemble.
  rw [curvatureOp_apply, curvatureOp_apply, e1, e2, e3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hgY, hgX] at *
  rw [e4]
  module

end CovariantDerivative
