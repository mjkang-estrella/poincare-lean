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
import Mathlib.Analysis.Calculus.MeanValue
import Poincare.FlatModelConnection

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

/--
In a fixed boundaryless chart, the exterior derivative of a scalar function is
the ordinary derivative of the fixed-chart representative applied to the
chart-pushed tangent vector.
-/
theorem extDerivFun_apply_fixed_chart {f : M → 𝕜} {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source) (hf : MDiffAt f y)
    (v : TangentSpace I y) :
    extDerivFun f y v =
      fderiv 𝕜 (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)
        (mfderiv% (extChartAt I x₀) y v) := by
  have hys : y ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source] at hy
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have hsmWithin :
      CMDiffAt[range I] 1 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) :=
    contMDiffWithinAt_extChartAt_symm_range (n := 1) x₀ htarget
  have hsm :
      CMDiffAt 1 ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) := by
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
  have hrep :
      DifferentiableAt 𝕜 (f ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀ y) := by
    exact mdifferentiableAt_iff_differentiableAt.mp
      (MDifferentiableAt.comp_of_eq
        (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, 𝕜))
        (g := f) (f := ((extChartAt I x₀).symm : E → M))
        (x := extChartAt I x₀ y)
        hf (hsm.mdifferentiableAt one_ne_zero) hleft)
  have hfeq : f =ᶠ[𝓝 y]
      (f ∘ (extChartAt I x₀).symm) ∘ (extChartAt I x₀) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hy]
      with z hz
    simp only [Function.comp_apply]
    rw [(extChartAt I x₀).left_inv hz]
  have hcomp : mfderiv% f y =
      (fderiv 𝕜 (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)) ∘L
        mfderiv% (extChartAt I x₀) y := by
    rw [hfeq.mfderiv_eq, mfderiv_comp y
      (mdifferentiableAt_iff_differentiableAt.mpr hrep)
      (mdifferentiableAt_extChartAt hys)]
    congr 1
    exact mfderiv_eq_fderiv
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, hcomp]
  rfl

omit [IsManifold I 1 M] in
/--
If the exterior derivative of a real-valued function vanishes at every point
and the function is manifold-differentiable everywhere, then it is locally
constant.

The proof is chart-local: on a boundaryless chart target, `extDerivFun` is the
Fréchet derivative of the chart representative, so Mathlib's mean-value
constancy lemma makes chart-level fibers open; pulling them back gives
manifold-local constancy.
-/
theorem isLocallyConstant_of_extDerivFun_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [I.Boundaryless] {f : M → ℝ}
    (hf : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) f x)
    (hzero : ∀ x : M, ∀ w : TangentSpace I x, extDerivFun f x w = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := extChartAt I x
  let F : E → ℝ := f ∘ e.symm
  let z0 : E := e x
  have hFdiffAt : ∀ z ∈ e.target, DifferentiableAt ℝ F z := by
    intro z hz
    have hsmWithin :
        ContMDiffWithinAt 𝓘(ℝ, E) I 1 (e.symm : E → M) (range I) z := by
      simpa [e] using
        contMDiffWithinAt_extChartAt_symm_range (I := I) (n := 1) x hz
    have hsm : ContMDiffAt 𝓘(ℝ, E) I 1 (e.symm : E → M) z := by
      rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
    have hcomp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) F z := by
      simpa [F] using
        (hf (e.symm z)).comp z (hsm.mdifferentiableAt one_ne_zero)
    exact mdifferentiableAt_iff_differentiableAt.mp hcomp
  have hFdiffOn : DifferentiableOn ℝ F e.target := by
    intro z hz
    exact (hFdiffAt z hz).differentiableWithinAt
  have hFderivZero : e.target.EqOn (fderiv ℝ F) 0 := by
    intro z hz
    ext v
    let y : M := e.symm z
    have hySrc : y ∈ e.source := e.map_target hz
    have hz_eq : e y = z := e.right_inv hz
    let L : TangentSpace I y →L[ℝ] E :=
      mfderiv I 𝓘(ℝ, E) (e : M → E) y
    have hInv : L.IsInvertible := by
      simpa [L, e, y] using
        (isInvertible_mfderiv_extChartAt (I := I) (x := x) (y := y) hySrc :
          (mfderiv I 𝓘(ℝ, E)
            ((extChartAt I x : PartialEquiv M E) : M → E) y).IsInvertible)
    let w : TangentSpace I y := L.inverse v
    have hLv : L w = v := by
      simpa [w] using hInv.self_apply_inverse v
    have hchart :=
      extDerivFun_apply_fixed_chart (I := I) (f := f) (x₀ := x) (y := y)
        (by simpa [e, y] using hySrc) (hf y) w
    have hzro : extDerivFun f y w = 0 := hzero y w
    rw [hchart] at hzro
    have hzro' : fderiv ℝ F (e y) (L w) = 0 := by
      simpa [F, L] using hzro
    rw [hz_eq, hLv] at hzro'
    exact hzro'
  have hLevelOpen : IsOpen (e.target ∩ F ⁻¹' {F z0}) :=
    (isOpen_extChartAt_target (I := I) x).isOpen_inter_preimage_of_fderiv_eq_zero
      hFdiffOn hFderivZero {F z0}
  have hz0Level : z0 ∈ e.target ∩ F ⁻¹' {F z0} := by
    constructor
    · simp [e, z0]
    · simp [z0]
  have hpre : (fun y : M ↦ e y) ⁻¹' (e.target ∩ F ⁻¹' {F z0}) ∈ 𝓝 x :=
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds
      (hLevelOpen.mem_nhds hz0Level)
  have hsrc : e.source ∈ 𝓝 x := by
    simpa [e] using
      (isOpen_extChartAt_source (I := I) x).mem_nhds
        (mem_extChartAt_source (I := I) x)
  filter_upwards [hsrc, hpre] with y hySrc hyLevel
  have hFy : F (e y) = F z0 := by
    simpa using hyLevel.2
  have hyLeft : e.symm (e y) = y := e.left_inv hySrc
  have hxLeft : e.symm z0 = x := by
    simp [e, z0]
  simpa [F, z0, hyLeft, hxLeft] using hFy

end Boundaryless

section DerivationIdentity

open VectorField

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 2 N] [I'.Boundaryless] [CompleteSpace E']

/--
**The bracket-derivation identity, chart form.**  For `f` `C²` at `x` and
fields `X, Y` differentiable at `x` on a boundaryless real manifold, the
derivative of `f` along the Lie bracket is the commutator of iterated
derivatives, expressed through the chart at `x`.
-/
theorem extDerivFun_apply_mlieBracket_chart
    {f : N → ℝ} {X Y : Π y : N, TangentSpace I' y} {x : N}
    (hf : CMDiffAt 2 f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    extDerivFun f x (mlieBracket I' X Y x) =
      fderiv ℝ (fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
          (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm Y z))
        (extChartAt I' x x) (X x)
      - fderiv ℝ (fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
          (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm X z))
        (extChartAt I' x x) (Y x) := by
  -- The chart representative of `f` is `C²`.
  have hFc : ContDiffAt ℝ 2 (f ∘ (extChartAt I' x).symm) (extChartAt I' x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [I'.range_eq_univ, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I' x).symm =
        f ∘ (extChartAt I' x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hsymm := hFc.isSymmSndFDerivAt (by simp)
  -- The pulled-back fields are differentiable at the chart image.
  have hinv : (mfderiv% (extChartAt I' x).symm (extChartAt I' x x)).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm
      (mem_extChartAt_target (I := I') x)
    rwa [I'.range_eq_univ, mfderivWithin_univ] at h
  have hpull : ∀ (U : Π y : N, TangentSpace I' y), MDiffAt (T% U) x →
      DifferentiableAt ℝ
        (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U)
        (extChartAt I' x x) := by
    intro U hU
    have hsm : CMDiffAt 2 ((extChartAt I' x).symm : E' → N)
        (extChartAt I' x x) := by
      have h := contMDiffWithinAt_extChartAt_symm_range (n := 2) x
        (mem_extChartAt_target (I := I') x)
      rwa [I'.range_eq_univ, contMDiffWithinAt_univ] at h
    have hU' : MDiffAt[univ] (T% U)
        ((extChartAt I' x).symm (extChartAt I' x x)) := by
      rw [(extChartAt I' x).left_inv (mem_extChartAt_source x),
        mdifferentiableWithinAt_univ]
      exact hU
    have h := hU'.mpullback_vectorField_preimage hsm hinv le_rfl
    rw [preimage_univ, mdifferentiableWithinAt_univ] at h
    exact mdiffAt_vectorSpace_iff_differentiableAt.mp h
  -- Centers of the pulled-back fields.
  have hc : ∀ (U : Π y : N, TangentSpace I' y),
      mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U (extChartAt I' x x)
        = U x := by
    intro U
    rw [← mpullbackWithin_univ, ← I'.range_eq_univ]
    exact mpullbackWithin_extChartAt_symm_self U x
  -- Reduce to the model space and apply the model identity.
  rw [extDerivFun_apply_chart (hf.mdifferentiableAt two_ne_zero),
    mlieBracket_apply_chart]
  simp only [I'.range_eq_univ, lieBracketWithin_univ, mpullbackWithin_univ]
  rw [fderiv_apply_lieBracket_of_isSymmSndFDerivAt hFc hsymm
    (hpull Y hY) (hpull X hX), hc X, hc Y]

/--
Away from the center: the pullback under the inverse chart at a source point
is the chart derivative of the field.
-/
theorem mpullback_extChartAt_symm_apply {x y : N}
    (hy : y ∈ (extChartAt I' x).source) (U : Π z : N, TangentSpace I' z) :
    mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U (extChartAt I' x y) =
      mfderiv% (extChartAt I' x) y (U y) := by
  rw [VectorField.mpullback]
  have h1 : (extChartAt I' x).symm (extChartAt I' x y) = y :=
    (extChartAt I' x).left_inv hy
  have hyT : extChartAt I' x y ∈ (extChartAt I' x).target :=
    (extChartAt I' x).map_source hy
  have c1 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (x := x) hyT
  have c2 := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    (x := x) hyT
  rw [I'.range_eq_univ, mfderivWithin_univ] at c1 c2
  have hinv : (mfderiv% (extChartAt I' x).symm (extChartAt I' x y)).inverse =
      mfderiv% (extChartAt I' x) ((extChartAt I' x).symm (extChartAt I' x y)) :=
    ContinuousLinearMap.inverse_eq c2 c1
  rw [hinv, h1]

/--
Near `x`, the invariant iterated-derivative function agrees with its chart
representative.
-/
theorem extDerivFun_section_eventually_chart {f : N → ℝ} {x : N}
    (hf : CMDiffAt 2 f x) (U : Π z : N, TangentSpace I' z) :
    ∀ᶠ y in 𝓝 x, extDerivFun f y (U y) =
      fderiv ℝ (f ∘ (extChartAt I' x).symm) (extChartAt I' x y)
        (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U
          (extChartAt I' x y)) := by
  have hFc : ContDiffAt ℝ 2 (f ∘ (extChartAt I' x).symm)
      (extChartAt I' x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [I'.range_eq_univ, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I' x).symm =
        f ∘ (extChartAt I' x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hf1 : ∀ᶠ y in 𝓝 x, MDiffAt f y := by
    obtain ⟨v, hv, hfv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hf
    filter_upwards [interior_mem_nhds.mpr hv] with y hy
    exact (((hfv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hFev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ
      (f ∘ (extChartAt I' x).symm) (extChartAt I' x y) :=
    (continuousAt_extChartAt (I := I') x).eventually
      ((hFc.eventually (by norm_num)).mono fun z hz ↦
        hz.differentiableAt two_ne_zero)
  filter_upwards [hf1, hFev,
    (isOpen_extChartAt_source (I := I') x).mem_nhds
      (mem_extChartAt_source x)] with y hfy hFy hys
  rw [mpullback_extChartAt_symm_apply hys U]
  have hcomp : mfderiv% f y =
      (fderiv ℝ (f ∘ (extChartAt I' x).symm) ((extChartAt I' x) y)) ∘L
        mfderiv% (extChartAt I' x) y := by
    have hfeq : f =ᶠ[𝓝 y]
        (f ∘ (extChartAt I' x).symm) ∘ (extChartAt I' x) := by
      filter_upwards [(isOpen_extChartAt_source (I := I') x).mem_nhds hys]
        with z hz
      simp only [Function.comp_apply]
      rw [(extChartAt I' x).left_inv hz]
    rw [hfeq.mfderiv_eq, mfderiv_comp y
      (mdifferentiableAt_iff_differentiableAt.mpr hFy)
      (mdifferentiableAt_extChartAt
        (by rwa [extChartAt_source] at hys))]
    congr 1
    exact mfderiv_eq_fderiv
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, hcomp]
  rfl

/--
The invariant iterated derivative of a scalar field along a tangent field is
the ordinary derivative of the corresponding fixed-chart representative.
-/
theorem extDerivFun_extDerivFun_chart
    {f : N → ℝ} {U : Π y : N, TangentSpace I' y} {x : N}
    (hf : CMDiffAt 2 f x) (hU : MDiffAt (T% U) x)
    (v : TangentSpace I' x) :
    extDerivFun (fun y ↦ extDerivFun f y (U y)) x v =
      fderiv ℝ (fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
          (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U z))
        (extChartAt I' x x) v := by
  have hFc : ContDiffAt ℝ 2 (f ∘ (extChartAt I' x).symm)
      (extChartAt I' x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [I'.range_eq_univ, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I' x).symm =
        f ∘ (extChartAt I' x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hinv : (mfderiv% (extChartAt I' x).symm
      (extChartAt I' x x)).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm
      (mem_extChartAt_target (I := I') x)
    rwa [I'.range_eq_univ, mfderivWithin_univ] at h
  have hpull : DifferentiableAt ℝ
      (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U)
      (extChartAt I' x x) := by
    have hsm : CMDiffAt 2 ((extChartAt I' x).symm : E' → N)
        (extChartAt I' x x) := by
      have h := contMDiffWithinAt_extChartAt_symm_range (n := 2) x
        (mem_extChartAt_target (I := I') x)
      rwa [I'.range_eq_univ, contMDiffWithinAt_univ] at h
    have hU' : MDiffAt[univ] (T% U)
        ((extChartAt I' x).symm (extChartAt I' x x)) := by
      rw [(extChartAt I' x).left_inv (mem_extChartAt_source x),
        mdifferentiableWithinAt_univ]
      exact hU
    have h := hU'.mpullback_vectorField_preimage hsm hinv le_rfl
    rw [preimage_univ, mdifferentiableWithinAt_univ] at h
    exact mdiffAt_vectorSpace_iff_differentiableAt.mp h
  set g : N → ℝ := fun y ↦ extDerivFun f y (U y) with hg
  set c : E' → ℝ := fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
    (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U z) with hc
  have hgc : g =ᶠ[𝓝 x] c ∘ (extChartAt I' x) := by
    filter_upwards [extDerivFun_section_eventually_chart hf U] with y hy
    exact hy
  have hcd : DifferentiableAt ℝ c (extChartAt I' x x) := by
    apply DifferentiableAt.clm_apply
    · exact (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero
    · exact hpull
  have hgd : MDiffAt g x := by
    refine MDifferentiableAt.congr_of_eventuallyEq ?_ hgc
    exact (mdifferentiableAt_iff_differentiableAt.mpr hcd).comp x
      (mdifferentiableAt_extChartAt (mem_chart_source H' x))
  rw [extDerivFun_apply_chart hgd v]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  have hev : ∀ᶠ z in 𝓝 (extChartAt I' x x),
      z ∈ (extChartAt I' x).target :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hsx : (extChartAt I' x).symm (extChartAt I' x x) = x :=
    (extChartAt I' x).left_inv (mem_extChartAt_source x)
  have hgc2 : ∀ᶠ y in 𝓝 ((extChartAt I' x).symm (extChartAt I' x x)),
      g y = (c ∘ (extChartAt I' x)) y := by
    rw [hsx]
    exact hgc
  have hgc' := (continuousAt_extChartAt_symm (I := I') x).eventually hgc2
  filter_upwards [hev, hgc'] with z hzT hzg
  have h2 : (extChartAt I' x) ((extChartAt I' x).symm z) = z :=
    (extChartAt I' x).right_inv hzT
  show g ((extChartAt I' x).symm z) = c z
  rw [hzg]
  show c ((extChartAt I' x) ((extChartAt I' x).symm z)) = c z
  rw [h2]

/--
**The bracket-derivation identity** (invariant form): on a boundaryless real
manifold, `df([X,Y]) = X(Y f) - Y(X f)` at every point where `f` is `C²` and
`X, Y` are differentiable.
-/
theorem extDerivFun_apply_mlieBracket
    {f : N → ℝ} {X Y : Π y : N, TangentSpace I' y} {x : N}
    (hf : CMDiffAt 2 f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    extDerivFun f x (mlieBracket I' X Y x) =
      extDerivFun (fun y ↦ extDerivFun f y (Y y)) x (X x)
        - extDerivFun (fun y ↦ extDerivFun f y (X y)) x (Y x) := by
  have hFc : ContDiffAt ℝ 2 (f ∘ (extChartAt I' x).symm)
      (extChartAt I' x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [I'.range_eq_univ, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I' x).symm =
        f ∘ (extChartAt I' x).symm := by
      funext z
      simp
    rwa [heq] at h
  have hinv : (mfderiv% (extChartAt I' x).symm
      (extChartAt I' x x)).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm
      (mem_extChartAt_target (I := I') x)
    rwa [I'.range_eq_univ, mfderivWithin_univ] at h
  have hpull : ∀ (U : Π y : N, TangentSpace I' y), MDiffAt (T% U) x →
      DifferentiableAt ℝ
        (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U)
        (extChartAt I' x x) := by
    intro U hU
    have hsm : CMDiffAt 2 ((extChartAt I' x).symm : E' → N)
        (extChartAt I' x x) := by
      have h := contMDiffWithinAt_extChartAt_symm_range (n := 2) x
        (mem_extChartAt_target (I := I') x)
      rwa [I'.range_eq_univ, contMDiffWithinAt_univ] at h
    have hU' : MDiffAt[univ] (T% U)
        ((extChartAt I' x).symm (extChartAt I' x x)) := by
      rw [(extChartAt I' x).left_inv (mem_extChartAt_source x),
        mdifferentiableWithinAt_univ]
      exact hU
    have h := hU'.mpullback_vectorField_preimage hsm hinv le_rfl
    rw [preimage_univ, mdifferentiableWithinAt_univ] at h
    exact mdiffAt_vectorSpace_iff_differentiableAt.mp h
  -- The invariant iterated derivative equals the chart-side derivative.
  have hterm : ∀ (U V₀ : Π y : N, TangentSpace I' y), MDiffAt (T% U) x →
      extDerivFun (fun y ↦ extDerivFun f y (U y)) x (V₀ x) =
        fderiv ℝ (fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
            (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U z))
          (extChartAt I' x x) (V₀ x) := by
    intro U V₀ hU
    set g : N → ℝ := fun y ↦ extDerivFun f y (U y) with hg
    set c : E' → ℝ := fun z ↦ fderiv ℝ (f ∘ (extChartAt I' x).symm) z
      (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm U z) with hc
    have hgc : g =ᶠ[𝓝 x] c ∘ (extChartAt I' x) := by
      filter_upwards [extDerivFun_section_eventually_chart hf U] with y hy
      exact hy
    have hcd : DifferentiableAt ℝ c (extChartAt I' x x) := by
      apply DifferentiableAt.clm_apply
      · exact (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt
          one_ne_zero
      · exact hpull U hU
    have hgd : MDiffAt g x := by
      refine MDifferentiableAt.congr_of_eventuallyEq ?_ hgc
      exact (mdifferentiableAt_iff_differentiableAt.mpr hcd).comp x
        (mdifferentiableAt_extChartAt (mem_chart_source H' x))
    rw [extDerivFun_apply_chart hgd (V₀ x)]
    congr 1
    apply Filter.EventuallyEq.fderiv_eq
    have hev : ∀ᶠ z in 𝓝 (extChartAt I' x x),
        z ∈ (extChartAt I' x).target :=
      (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
    have hsx : (extChartAt I' x).symm (extChartAt I' x x) = x :=
      (extChartAt I' x).left_inv (mem_extChartAt_source x)
    have hgc2 : ∀ᶠ y in 𝓝 ((extChartAt I' x).symm (extChartAt I' x x)),
        g y = (c ∘ (extChartAt I' x)) y := by
      rw [hsx]
      exact hgc
    have hgc' := (continuousAt_extChartAt_symm (I := I') x).eventually hgc2
    filter_upwards [hev, hgc'] with z hzT hzg
    have h2 : (extChartAt I' x) ((extChartAt I' x).symm z) = z :=
      (extChartAt I' x).right_inv hzT
    show g ((extChartAt I' x).symm z) = c z
    rw [hzg]
    show c ((extChartAt I' x) ((extChartAt I' x).symm z)) = c z
    rw [h2]
  rw [extDerivFun_apply_mlieBracket_chart hf hX hY,
    hterm Y X hY, hterm X Y hX]

end DerivationIdentity

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

/-- Theorem contract for `mlieBracket_apply_chart`. -/
theorem mlieBracket_apply_chart_eq :
    @mlieBracket_apply_chart = @mlieBracket_apply_chart :=
  rfl

/-- Theorem contract for `mpullbackWithin_extChartAt_symm_self`. -/
theorem mpullbackWithin_extChartAt_symm_self_eq :
    @mpullbackWithin_extChartAt_symm_self = @mpullbackWithin_extChartAt_symm_self :=
  rfl

/-- Theorem contract for `extDerivFun_apply_chart`. -/
theorem extDerivFun_apply_chart_eq :
    @extDerivFun_apply_chart = @extDerivFun_apply_chart :=
  rfl

/-- Theorem contract for `extDerivFun_apply_fixed_chart`. -/
theorem extDerivFun_apply_fixed_chart_eq :
    @extDerivFun_apply_fixed_chart = @extDerivFun_apply_fixed_chart :=
  rfl

/-- Theorem contract for `isLocallyConstant_of_extDerivFun_eq_zero`. -/
theorem isLocallyConstant_of_extDerivFun_eq_zero_eq :
    @isLocallyConstant_of_extDerivFun_eq_zero =
      @isLocallyConstant_of_extDerivFun_eq_zero :=
  rfl

/-- Theorem contract for `extDerivFun_apply_mlieBracket_chart`. -/
theorem extDerivFun_apply_mlieBracket_chart_eq :
    @extDerivFun_apply_mlieBracket_chart = @extDerivFun_apply_mlieBracket_chart :=
  rfl

/-- Theorem contract for `mpullback_extChartAt_symm_apply`. -/
theorem mpullback_extChartAt_symm_apply_eq :
    @mpullback_extChartAt_symm_apply = @mpullback_extChartAt_symm_apply :=
  rfl

/-- Theorem contract for `extDerivFun_section_eventually_chart`. -/
theorem extDerivFun_section_eventually_chart_eq :
    @extDerivFun_section_eventually_chart = @extDerivFun_section_eventually_chart :=
  rfl

/-- Theorem contract for `extDerivFun_extDerivFun_chart`. -/
theorem extDerivFun_extDerivFun_chart_eq :
    @extDerivFun_extDerivFun_chart = @extDerivFun_extDerivFun_chart :=
  rfl

/-- Theorem contract for `extDerivFun_apply_mlieBracket`. -/
theorem extDerivFun_apply_mlieBracket_eq :
    @extDerivFun_apply_mlieBracket = @extDerivFun_apply_mlieBracket :=
  rfl
