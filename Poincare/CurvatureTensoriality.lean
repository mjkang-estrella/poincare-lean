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

/-- The curvature operator vanishes on the zero field. -/
theorem curvatureOp_zero_field
    {X Y : Π y : M, TangentSpace I y} {x : M} :
    curvatureOp cov X Y 0 x = 0 := by
  have hcovD := cov.isCovariantDerivativeOnUniv
  have h0 : cov (0 : Π y : M, TangentSpace I y) = 0 := by
    ext1 y
    exact hcovD.zero
  rw [curvatureOp_apply]
  simp [h0]
  rw [show (fun y : M ↦ (0 : TangentSpace I y)) =
    (0 : Π y : M, TangentSpace I y) from rfl, h0]
  simp

omit [I.Boundaryless] [CompleteSpace E] in
/--
**Additivity of the curvature operator in the field slot**:
`R(X,Y)(Z + Z') = R(X,Y)Z + R(X,Y)Z'` pointwise for `Z, Z'` `C²` and
`X, Y` differentiable at `x`.
-/
theorem curvatureOp_add_field
    {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) (hZ' : CMDiffAt 2 (T% Z') x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvatureOp cov X Y (Z + Z') x =
      curvatureOp cov X Y Z x + curvatureOp cov X Y Z' x := by
  have hcovD := cov.isCovariantDerivativeOnUniv
  have hZd : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := by
    obtain ⟨v, hv, hZv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
    filter_upwards [interior_mem_nhds.mpr hv] with y hy
    exact (((hZv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hZ'd : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z') y := by
    obtain ⟨v, hv, hZv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ'
    filter_upwards [interior_mem_nhds.mpr hv] with y hy
    exact (((hZv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hZ'x : MDiffAt (T% Z') x := hZ'.mdifferentiableAt two_ne_zero
  have hZZ' : CMDiffAt 2 (T% (Z + Z')) x := hZ.add_section hZ'
  have hsec : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ cov (Z + Z') y (W y)) =ᶠ[𝓝 x]
        fun y ↦ cov Z y (W y) + cov Z' y (W y) := by
    intro W
    filter_upwards [hZd, hZ'd] with y hZy hZ'y
    rw [hcovD.add hZy hZ'y]
    simp
  set DY : Π y : M, TangentSpace I y := fun y ↦ cov Z y (Y y)
  set DY' : Π y : M, TangentSpace I y := fun y ↦ cov Z' y (Y y)
  set DX : Π y : M, TangentSpace I y := fun y ↦ cov Z y (X y)
  set DX' : Π y : M, TangentSpace I y := fun y ↦ cov Z' y (X y)
  have hDYd : MDiffAt (T% DY) x := mdiffAt_cov_section_of_contMDiffAt cov hZ hY
  have hDY'd : MDiffAt (T% DY') x :=
    mdiffAt_cov_section_of_contMDiffAt cov hZ' hY
  have hDXd : MDiffAt (T% DX) x := mdiffAt_cov_section_of_contMDiffAt cov hZ hX
  have hDX'd : MDiffAt (T% DX') x :=
    mdiffAt_cov_section_of_contMDiffAt cov hZ' hX
  have hrepl : ∀ (W : Π y : M, TangentSpace I y)
      (DW DW' : Π y : M, TangentSpace I y),
      DW = (fun y ↦ cov Z y (W y)) → DW' = (fun y ↦ cov Z' y (W y)) →
      MDiffAt (T% (fun y ↦ cov (Z + Z') y (W y))) x →
      MDiffAt (T% (DW + DW')) x →
      cov (fun y ↦ cov (Z + Z') y (W y)) x = cov (DW + DW') x := by
    intro W DW DW' hDWdef hDW'def hAW hA'W
    apply hcovD.congr_of_eventuallyEq hAW hA'W univ_mem
    filter_upwards [hsec W] with y hy
    rw [hy, hDWdef, hDW'def]
    simp
  have e1 := hrepl Y DY DY' rfl rfl
    (mdiffAt_cov_section_of_contMDiffAt cov hZZ' hY)
    (mdifferentiableAt_add_section hDYd hDY'd)
  have e2 := hrepl X DX DX' rfl rfl
    (mdiffAt_cov_section_of_contMDiffAt cov hZZ' hX)
    (mdifferentiableAt_add_section hDXd hDX'd)
  rw [hcovD.add hDYd hDY'd] at e1
  rw [hcovD.add hDXd hDX'd] at e2
  have e3 : cov (Z + Z') x = cov Z x + cov Z' x := hcovD.add hZx hZ'x
  rw [curvatureOp_apply, curvatureOp_apply, curvatureOp_apply, e1, e2, e3]
  simp only [ContinuousLinearMap.add_apply]
  module

/-- The curvature operator distributes over finite sums of `C²` fields. -/
theorem curvatureOp_finsetSum_field {ι : Type*} [DecidableEq ι]
    {X Y : Π y : M, TangentSpace I y} {x : M} (s : Finset ι)
    (Z : ι → Π y : M, TangentSpace I y)
    (hZ : ∀ i ∈ s, CMDiffAt 2 (T% (Z i)) x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvatureOp cov X Y (fun y ↦ ∑ i ∈ s, Z i y) x =
      ∑ i ∈ s, curvatureOp cov X Y (Z i) x := by
  induction s using Finset.induction with
  | empty => simpa using curvatureOp_zero_field cov
  | insert a s ha ih =>
    have hsum : (fun y ↦ ∑ i ∈ insert a s, Z i y) =
        Z a + fun y ↦ ∑ i ∈ s, Z i y := by
      funext y
      simp [Finset.sum_insert ha]
    rw [hsum, curvatureOp_add_field cov
      (hZ a (Finset.mem_insert_self a s))
      (ContMDiffAt.sum_section fun i hi ↦ hZ i (Finset.mem_insert_of_mem hi))
      hX hY,
      Finset.sum_insert ha, ih fun i hi ↦ hZ i (Finset.mem_insert_of_mem hi)]

open Trivialization in
/--
**Value-dependence of the curvature in the field slot**: a `C²` field
vanishing at `x` has vanishing curvature at `x`.  Consequently `R(X,Y)Z|ₓ`
depends only on `Z x` among `C²` fields.
-/
theorem curvatureOp_eq_zero_of_value_eq_zero
    {X Y D : Π y : M, TangentSpace I y} {x : M}
    (hD : CMDiffAt 2 (T% D) x) (hDx : D x = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvatureOp cov X Y D x = 0 := by
  classical
  set e := trivializationAt E (TangentSpace I) x with he
  set b := Module.finBasis ℝ E with hb
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hev := e.eventually_eq_localFrame_sum_coeff_smul (I := I) b
    (s := D) hxe
  have hframe : ∀ i, CMDiffAt 2 (T% (e.localFrame b i)) x := fun i ↦
    contMDiffAt_localFrame_of_mem (I := I) (n := 2) (e := e) (b := b) i hxe
  have hcoeff : ∀ i, CMDiffAt 2
      (fun y ↦ e.localFrame_coeff I b i y (D y)) x := fun i ↦
    (contMDiffAt_iff_localFrame_coeff (I := I) (e := e) (b := b) hxe).mp hD i
  set Zs : _ → Π y : M, TangentSpace I y := fun i ↦
    (fun y ↦ e.localFrame_coeff I b i y (D y)) • e.localFrame b i with hZs
  have hsummand : ∀ i, CMDiffAt 2 (T% (Zs i)) x := fun i ↦
    (hcoeff i).smul_section (hframe i)
  have hSd : CMDiffAt 2 (T% (fun y ↦ ∑ i, Zs i y)) x :=
    ContMDiffAt.sum_section fun i _ ↦ hsummand i
  have h1 : curvatureOp cov X Y D x =
      curvatureOp cov X Y (fun y ↦ ∑ i, Zs i y) x := by
    apply curvatureOp_congr_of_eventuallyEq cov hD hSd hX hY
    filter_upwards [hev] with y hy
    simpa [hZs] using hy
  rw [h1, curvatureOp_finsetSum_field cov Finset.univ Zs
    (fun i _ ↦ hsummand i) hX hY]
  have hzero : ∀ i, curvatureOp cov X Y (Zs i) x = 0 := by
    intro i
    rw [hZs]
    rw [curvatureOp_smul_field cov (hcoeff i) (hframe i) hX hY]
    have hc0 : e.localFrame_coeff I b i x (D x) = 0 := by
      rw [hDx]
      exact map_zero _
    rw [hc0, zero_smul]
  simp [hzero]

/--
**The curvature depends only on the field value**: two `C²` fields agreeing
at `x` have the same curvature there.  In particular the canonical Ricci
form `ricciBilinearAt` is extension-independent.
-/
theorem curvatureOp_congr_of_value_eq
    {X Y Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) (hZ' : CMDiffAt 2 (T% Z') x)
    (hZZ' : Z x = Z' x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvatureOp cov X Y Z x = curvatureOp cov X Y Z' x := by
  have hneg : CMDiffAt 2 (T% ((fun _ : M ↦ (-1 : ℝ)) • Z')) x :=
    contMDiffAt_const.smul_section hZ'
  have hD : CMDiffAt 2 (T% (Z + (fun _ : M ↦ (-1 : ℝ)) • Z')) x :=
    hZ.add_section hneg
  have hDx : (Z + (fun _ : M ↦ (-1 : ℝ)) • Z') x = 0 := by
    simp [hZZ']
  have h0 := curvatureOp_eq_zero_of_value_eq_zero cov hD hDx hX hY
  rw [curvatureOp_add_field cov hZ hneg hX hY,
    curvatureOp_smul_field cov contMDiffAt_const hZ' hX hY] at h0
  have : curvatureOp cov X Y Z x - curvatureOp cov X Y Z' x = 0 := by
    rw [show curvatureOp cov X Y Z x - curvatureOp cov X Y Z' x =
      curvatureOp cov X Y Z x + (-1 : ℝ) • curvatureOp cov X Y Z' x by
        module]
    exact h0
  exact sub_eq_zero.mp this

end CovariantDerivative
