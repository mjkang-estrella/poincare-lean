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
import Poincare.LeviCivitaUniqueness

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

/-! ## The genuine Ricci tensor

With value-dependence established, the canonical Ricci form is
extension-independent and bilinear: it is the Ricci tensor.
-/

/--
**Extension-independence of the Ricci form**: the Ricci trace against any
admissible `C²` field equals the canonical Ricci form at the field value.
-/
theorem ricciTraceAt_eq_ricciBilinearAt
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 2 (T% Z) x)
    (hreg : DerivRegularAt cov Z x) (u : TangentSpace I x) :
    ricciTraceAt cov hreg u = ricciBilinearAt cov x u (Z x) := by
  unfold ricciBilinearAt ricciTraceAt
  congr 1
  apply LinearMap.ext
  intro v
  rw [curvatureEndAt_apply, curvatureEndAt_apply]
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend]
  exact curvatureOp_congr_of_value_eq cov hZ
    (contMDiffAt_extend' (k := 2) I E (Z x)) (by simp)
    (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)

/-- The Ricci tensor is additive in its first argument. -/
theorem ricciBilinearAt_add_left (x : M) (u u' w : TangentSpace I x) :
    ricciBilinearAt cov x (u + u') w =
      ricciBilinearAt cov x u w + ricciBilinearAt cov x u' w :=
  ricciTraceAt_add cov _ u u'

/-- The Ricci tensor is homogeneous in its first argument. -/
theorem ricciBilinearAt_smul_left (x : M) (c : ℝ) (u w : TangentSpace I x) :
    ricciBilinearAt cov x (c • u) w = c • ricciBilinearAt cov x u w :=
  ricciTraceAt_smul cov _ c u

/--
Curvature against extensions is additive in the extended value.
-/
theorem curvatureOp_extend_add
    {x : M} (w w' v u : TangentSpace I x) :
    curvatureOp cov (extend E v) (extend E u) (extend E (w + w')) x =
      curvatureOp cov (extend E v) (extend E u) (extend E w) x
        + curvatureOp cov (extend E v) (extend E u) (extend E w') x := by
  have h1 : curvatureOp cov (extend E v) (extend E u) (extend E (w + w')) x =
      curvatureOp cov (extend E v) (extend E u)
        (extend E w + extend E w') x := by
    apply curvatureOp_congr_of_value_eq cov
      (contMDiffAt_extend' (k := 2) I E (w + w'))
      ((contMDiffAt_extend' (k := 2) I E w).add_section
        (contMDiffAt_extend' (k := 2) I E w'))
      (by simp) (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
  rw [h1, curvatureOp_add_field cov
    (contMDiffAt_extend' (k := 2) I E w)
    (contMDiffAt_extend' (k := 2) I E w')
    (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]

/--
Curvature against extensions is homogeneous in the extended value.
-/
theorem curvatureOp_extend_smul
    {x : M} (c : ℝ) (w v u : TangentSpace I x) :
    curvatureOp cov (extend E v) (extend E u) (extend E (c • w)) x =
      c • curvatureOp cov (extend E v) (extend E u) (extend E w) x := by
  have h1 : curvatureOp cov (extend E v) (extend E u) (extend E (c • w)) x =
      curvatureOp cov (extend E v) (extend E u)
        ((fun _ : M ↦ c) • extend E w) x := by
    apply curvatureOp_congr_of_value_eq cov
      (contMDiffAt_extend' (k := 2) I E (c • w))
      (contMDiffAt_const.smul_section (contMDiffAt_extend' (k := 2) I E w))
      (by simp) (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
  rw [h1, curvatureOp_smul_field cov contMDiffAt_const
    (contMDiffAt_extend' (k := 2) I E w)
    (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]

/-- The Ricci tensor is additive in its second argument. -/
theorem ricciBilinearAt_add_right (x : M) (u w w' : TangentSpace I x) :
    ricciBilinearAt cov x u (w + w') =
      ricciBilinearAt cov x u w + ricciBilinearAt cov x u w' := by
  unfold ricciBilinearAt ricciTraceAt
  rw [← map_add]
  congr 1
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, curvatureEndAt_apply]
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend,
    TensorialAt.mkHom₂_apply_eq_extend]
  exact curvatureOp_extend_add cov w w' v u

/-- The Ricci tensor is homogeneous in its second argument. -/
theorem ricciBilinearAt_smul_right (x : M) (c : ℝ) (u w : TangentSpace I x) :
    ricciBilinearAt cov x u (c • w) = c • ricciBilinearAt cov x u w := by
  unfold ricciBilinearAt ricciTraceAt
  rw [← map_smul]
  congr 1
  apply LinearMap.ext
  intro v
  simp only [LinearMap.smul_apply, curvatureEndAt_apply]
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend]
  exact curvatureOp_extend_smul cov c w v u

/-- A `C²`-at-`x` field is differentiable near `x`. -/
private theorem eventually_mdiffAt_of_contMDiffAt
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 2 (T% Z) x) :
    ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := by
  obtain ⟨v, hv, hZv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
  filter_upwards [interior_mem_nhds.mpr hv] with y hy
  exact (((hZv.mono interior_subset) y hy).contMDiffAt
    (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero

/--
**First Bianchi identity, pointwise form**: for a torsion-free connection
and fields `C²` at `x`, the cyclic curvature sum vanishes at `x`.
-/
theorem bianchi_first_at (htf : ∀ y : M, TorsionFreeAt cov y)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 2 (T% Z) x) :
    curvatureOp cov X Y Z x + curvatureOp cov Y Z X x
      + curvatureOp cov Z X Y x = 0 := by
  haveI : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by
    rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    exact_mod_cast (inferInstance : IsManifold I 3 M)
  have hcovD := cov.isCovariantDerivativeOnUniv
  have hXd := eventually_mdiffAt_of_contMDiffAt hX
  have hYd := eventually_mdiffAt_of_contMDiffAt hY
  have hZd := eventually_mdiffAt_of_contMDiffAt hZ
  have hX1 : MDiffAt (T% X) x := hX.mdifferentiableAt two_ne_zero
  have hY1 : MDiffAt (T% Y) x := hY.mdifferentiableAt two_ne_zero
  have hZ1 : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  -- Brackets are differentiable at `x`.
  have hbr : ∀ {A B : Π y : M, TangentSpace I y},
      CMDiffAt 2 (T% A) x → CMDiffAt 2 (T% B) x →
        MDiffAt (T% (mlieBracket I A B)) x := by
    intro A B hA hB
    have h2 : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ ((2 : ℕ∞) : ℕ∞ω) := by
      simp
      norm_num
    exact (ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2)
      hA hB h2).mdifferentiableAt one_ne_zero
  -- Direction-grouped torsion conversion, localized.
  have egrp : ∀ (A B W : Π y : M, TangentSpace I y),
      CMDiffAt 2 (T% A) x → CMDiffAt 2 (T% B) x → MDiffAt (T% W) x →
      cov (fun y ↦ cov B y (A y)) x (W x)
        - cov (fun y ↦ cov A y (B y)) x (W x)
        = cov (mlieBracket I A B) x (W x) := by
    intro A B W hA hB hW
    have hDBA := mdiffAt_cov_section_of_contMDiffAt cov hB
      (hA.mdifferentiableAt two_ne_zero)
    have hDAB := mdiffAt_cov_section_of_contMDiffAt cov hA
      (hB.mdifferentiableAt two_ne_zero)
    have hsub : cov ((fun y ↦ cov B y (A y)) - fun y ↦ cov A y (B y)) x =
        cov (fun y ↦ cov B y (A y)) x - cov (fun y ↦ cov A y (B y)) x := by
      have hns : -(fun y ↦ cov A y (B y)) =
          (-1 : ℝ) • fun y ↦ cov A y (B y) :=
        (neg_one_smul ℝ _).symm
      have hd : MDiffAt (T% (-(fun y ↦ cov A y (B y)))) x := by
        rw [hns]
        exact mdifferentiableAt_const.smul_section hDAB
      have hneg : cov (-(fun y ↦ cov A y (B y))) x =
          - cov (fun y ↦ cov A y (B y)) x := by
        rw [hns, hcovD.smul_const (-1 : ℝ) hDAB]
        simp
      calc cov ((fun y ↦ cov B y (A y)) - fun y ↦ cov A y (B y)) x
          = cov ((fun y ↦ cov B y (A y)) + -(fun y ↦ cov A y (B y))) x := by
            rw [sub_eq_add_neg]
        _ = cov (fun y ↦ cov B y (A y)) x
            + cov (-(fun y ↦ cov A y (B y))) x := hcovD.add hDBA hd
        _ = _ := by rw [hneg, sub_eq_add_neg]
    have hcongr : cov ((fun y ↦ cov B y (A y)) - fun y ↦ cov A y (B y)) x =
        cov (mlieBracket I A B) x := by
      apply hcovD.congr_of_eventuallyEq
        (mdifferentiableAt_sub_section hDBA hDAB) (hbr hA hB) univ_mem
      filter_upwards [eventually_mdiffAt_of_contMDiffAt hA,
        eventually_mdiffAt_of_contMDiffAt hB] with y hAy hBy
      simpa using htf y hAy hBy
    rw [← ContinuousLinearMap.sub_apply, ← hsub, hcongr]
  have e1 := egrp Y Z X hY hZ hX1
  have e2 := egrp Z X Y hZ hX hY1
  have e3 := egrp X Y Z hX hY hZ1
  -- Pointwise torsion against brackets.
  have t1 : cov (mlieBracket I Y Z) x (X x) - cov X x (mlieBracket I Y Z x)
      = mlieBracket I X (mlieBracket I Y Z) x := htf x hX1 (hbr hY hZ)
  have t2 : cov (mlieBracket I Z X) x (Y x) - cov Y x (mlieBracket I Z X x)
      = mlieBracket I Y (mlieBracket I Z X) x := htf x hY1 (hbr hZ hX)
  have t3 : cov (mlieBracket I X Y) x (Z x) - cov Z x (mlieBracket I X Y x)
      = mlieBracket I Z (mlieBracket I X Y) x := htf x hZ1 (hbr hX hY)
  -- Cyclic Jacobi.
  have mX : CMDiffAt (minSmoothness ℝ 2) (T% X) x := by simpa using hX
  have mY : CMDiffAt (minSmoothness ℝ 2) (T% Y) x := by simpa using hY
  have mZ : CMDiffAt (minSmoothness ℝ 2) (T% Z) x := by simpa using hZ
  have l1 := leibniz_identity_mlieBracket_apply (x := x) mX mY mZ
  have l2 := leibniz_identity_mlieBracket_apply (x := x) mY mZ mX
  have l3 := leibniz_identity_mlieBracket_apply (x := x) mZ mX mY
  have l4 := leibniz_identity_mlieBracket_apply (x := x) mY mX mZ
  have l5 := leibniz_identity_mlieBracket_apply (x := x) mZ mY mX
  have l6 := leibniz_identity_mlieBracket_apply (x := x) mX mZ mY
  have s1 : mlieBracket I (mlieBracket I X Y) Z x
      = - mlieBracket I Z (mlieBracket I X Y) x := mlieBracket_swap_apply
  have s2 : mlieBracket I (mlieBracket I Y Z) X x
      = - mlieBracket I X (mlieBracket I Y Z) x := mlieBracket_swap_apply
  have s3 : mlieBracket I (mlieBracket I Z X) Y x
      = - mlieBracket I Y (mlieBracket I Z X) x := mlieBracket_swap_apply
  have s4 : mlieBracket I (mlieBracket I Y X) Z x
      = - mlieBracket I Z (mlieBracket I Y X) x := mlieBracket_swap_apply
  have s5 : mlieBracket I (mlieBracket I Z Y) X x
      = - mlieBracket I X (mlieBracket I Z Y) x := mlieBracket_swap_apply
  have s6 : mlieBracket I (mlieBracket I X Z) Y x
      = - mlieBracket I Y (mlieBracket I X Z) x := mlieBracket_swap_apply
  have h1 : (2 : ℝ) • (mlieBracket I X (mlieBracket I Y Z) x
      + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x)
      = mlieBracket I Y (mlieBracket I X Z) x
        + mlieBracket I Z (mlieBracket I Y X) x
        + mlieBracket I X (mlieBracket I Z Y) x := by
    linear_combination (norm := module) l1 + l2 + l3 + s1 + s2 + s3
  have h2 : (2 : ℝ) • (mlieBracket I Y (mlieBracket I X Z) x
      + mlieBracket I Z (mlieBracket I Y X) x
      + mlieBracket I X (mlieBracket I Z Y) x)
      = mlieBracket I X (mlieBracket I Y Z) x
        + mlieBracket I Y (mlieBracket I Z X) x
        + mlieBracket I Z (mlieBracket I X Y) x := by
    linear_combination (norm := module) l4 + l5 + l6 + s4 + s5 + s6
  have jac : mlieBracket I X (mlieBracket I Y Z) x
      + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0 := by
    linear_combination (norm := module)
      ((1 : ℝ)/3) • ((2 : ℝ) • h1 + h2)
  simp only [curvatureOp_apply]
  linear_combination (norm := module) e1 + e2 + e3 + t1 + t2 + t3 + jac

/-! ## The Ricci antisymmetry identity -/

/--
The pair-curvature endomorphism `v ↦ R(u, w) v` at `x`, defined through
canonical extensions; linear by field-slot tensoriality.
-/
noncomputable def pairCurvatureEndAt (x : M) (u w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := curvatureOp cov (extend E u) (extend E w) (extend E v) x
  map_add' v v' := curvatureOp_extend_add cov v v' u w
  map_smul' c v := curvatureOp_extend_smul cov c v u w

/--
**The Ricci antisymmetry identity**: for a torsion-free connection, the
antisymmetric part of the Ricci tensor is minus the trace of the
pair-curvature operator.  (For Levi-Civita connections that trace vanishes
by metric antisymmetry, giving symmetry of the Ricci tensor.)
-/
theorem ricciBilinearAt_sub_swap (htf : ∀ y : M, TorsionFreeAt cov y)
    (x : M) (u w : TangentSpace I x) :
    ricciBilinearAt cov x u w - ricciBilinearAt cov x w u =
      - LinearMap.trace ℝ (TangentSpace I x)
          (pairCurvatureEndAt cov x u w) := by
  have hABC : curvatureEndAt cov (derivRegularAt_extend cov w) u
      + pairCurvatureEndAt cov x u w
      - curvatureEndAt cov (derivRegularAt_extend cov u) w = 0 := by
    apply LinearMap.ext
    intro v
    have hb := bianchi_first_at cov htf
      (contMDiffAt_extend' (k := 2) I E v)
      (contMDiffAt_extend' (k := 2) I E u)
      (contMDiffAt_extend' (k := 2) I E w)
    have hA : curvatureEndAt cov (derivRegularAt_extend cov w) u v =
        curvatureOp cov (extend E v) (extend E u) (extend E w) x := by
      rw [curvatureEndAt_apply]
      unfold curvatureTensorAt
      rw [TensorialAt.mkHom₂_apply_eq_extend]
    have hC : curvatureEndAt cov (derivRegularAt_extend cov u) w v =
        curvatureOp cov (extend E v) (extend E w) (extend E u) x := by
      rw [curvatureEndAt_apply]
      unfold curvatureTensorAt
      rw [TensorialAt.mkHom₂_apply_eq_extend]
    have hC' : curvatureOp cov (extend E w) (extend E v) (extend E u) x =
        - curvatureOp cov (extend E v) (extend E w) (extend E u) x :=
      curvatureOp_antisymm_apply cov _ _ _ x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.zero_apply,
      hA, hC]
    have hB : pairCurvatureEndAt cov x u w v =
        curvatureOp cov (extend E u) (extend E w) (extend E v) x := rfl
    rw [hB]
    linear_combination (norm := module) hb - hC'
  have htr := congrArg (LinearMap.trace ℝ (TangentSpace I x)) hABC
  simp only [map_add, map_sub, map_zero] at htr
  have hA : LinearMap.trace ℝ (TangentSpace I x)
      (curvatureEndAt cov (derivRegularAt_extend cov w) u) =
      ricciBilinearAt cov x u w := rfl
  have hC : LinearMap.trace ℝ (TangentSpace I x)
      (curvatureEndAt cov (derivRegularAt_extend cov u) w) =
      ricciBilinearAt cov x w u := rfl
  rw [hA, hC] at htr
  linarith

end CovariantDerivative
