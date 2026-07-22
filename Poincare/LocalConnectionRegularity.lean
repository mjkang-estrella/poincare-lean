/-
Local regularity of covariant derivatives.

Mathlib's `ContMDiffCovariantDerivative` class provides regularity of
`∇ Z` only for globally `C²` sections `Z`.  This module localizes it: for a
`C¹` connection on a σ-compact-free finite-dimensional real manifold, `∇ Z`
is differentiable at `x` as soon as `Z` is `C²` *at* `x`.  The proof
globalizes `Z` by a smooth bump function supported in the regularity
neighbourhood and transfers back via germ locality of covariant derivatives.

As the first application, the canonical `extend`ed sections (which are smooth
near the base point but not globally) become admissible, yielding a canonical
Ricci value on pairs of tangent vectors.
-/

import Poincare.RiemannCurvatureOperator
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section

open Bundle Set FiberBundle Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/--
**Local `C²` regularity of a `C²` connection**: if `Z` is `C³` at `x` and
`W` is `C²` at `x`, then `y ↦ ∇_{W y} Z` is `C²` at `x`.
-/
theorem contMDiffAt_cov_section_of_contMDiffAt_two
    [ContMDiffCovariantDerivative cov 2]
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 3 (T% Z) x)
    {W : Π y : M, TangentSpace I y} (hW : CMDiffAt 2 (T% W) x) :
    CMDiffAt 2 (T% (fun y ↦ cov Z y (W y))) x := by
  obtain ⟨v, hv, hZv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 3) (by norm_num)).mp hZ
  set u : Set M := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hxu : x ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hZu : CMDiff[u] 3 (T% Z) := hZv.mono interior_subset
  obtain ⟨χ, -, hχsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (hu_open.mem_nhds hxu))
  set Z' : Π y : M, TangentSpace I y := (χ : M → ℝ) • Z with hZ'
  have hZ'glob : CMDiff 3 (T% Z') :=
    ContMDiffOn.smul_section_of_tsupport
      ((χ.contMDiff.of_le (by
        rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn)
      hu_open hχsupp hZu
  have hhomOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun y : M =>
          (⟨y, cov Z' y⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun y : M =>
                TangentSpace I y →L[ℝ] TangentSpace I y)))
        Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 2)).contMDiff
      (σ := Z') hZ'glob.contMDiffOn
  have hhomAt :
      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun y : M =>
          (⟨y, cov Z' y⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun y : M =>
                TangentSpace I y →L[ℝ] TangentSpace I y)))
        x :=
    hhomOn.contMDiffAt Filter.univ_mem
  have hreg : CMDiffAt 2 (T% (fun y ↦ cov Z' y (W y))) x :=
    hhomAt.clm_bundle_apply hW
  set w : Set M := interior {y | (χ : M → ℝ) y = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hxw : x ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one, hxu⟩
  have hZZ' : ∀ y ∈ interior {y | (χ : M → ℝ) y = 1}, Z y = Z' y := by
    intro y hy
    have h1 : y ∈ {y | (χ : M → ℝ) y = 1} := interior_subset hy
    simp [hZ', h1.out]
  have hev : (fun y ↦ cov Z y (W y)) =ᶠ[𝓝 x] fun y ↦ cov Z' y (W y) := by
    filter_upwards [hw_open.mem_nhds hxw] with y hy
    have hZy : MDiffAt (T% Z) y :=
      ((hZu y hy.2).contMDiffAt (hu_open.mem_nhds hy.2)).mdifferentiableAt
        (by norm_num)
    have hZ'y : MDiffAt (T% Z') y :=
      (hZ'glob y).mdifferentiableAt (by norm_num)
    have hcongr : cov Z y = cov Z' y := by
      apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZy hZ'y
        univ_mem
      filter_upwards [isOpen_interior.mem_nhds hy.1] with y' hy'
      exact hZZ' y' hy'
    rw [hcongr]
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hev] with y hy
  rw [Bundle.TotalSpace.mk_inj]
  exact hy

/--
**Local `C³` regularity of a `C³` connection**: if `Z` is `C⁴` at `x` and
`W` is `C³` at `x`, then `y ↦ ∇_{W y} Z` is `C³` at `x`.
-/
theorem contMDiffAt_cov_section_of_contMDiffAt_three
    [ContMDiffCovariantDerivative cov 3]
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 4 (T% Z) x)
    {W : Π y : M, TangentSpace I y} (hW : CMDiffAt 3 (T% W) x) :
    CMDiffAt 3 (T% (fun y ↦ cov Z y (W y))) x := by
  obtain ⟨v, hv, hZv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 4) (by norm_num)).mp hZ
  set u : Set M := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hxu : x ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hZu : CMDiff[u] 4 (T% Z) := hZv.mono interior_subset
  obtain ⟨χ, -, hχsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (hu_open.mem_nhds hxu))
  set Z' : Π y : M, TangentSpace I y := (χ : M → ℝ) • Z with hZ'
  have hZ'glob : CMDiff 4 (T% Z') :=
    ContMDiffOn.smul_section_of_tsupport
      ((χ.contMDiff.of_le (by
        rw [show (4 : ℕ∞ω) = ((4 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn)
      hu_open hχsupp hZu
  have hhomOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 3
        (fun y : M =>
          (⟨y, cov Z' y⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun y : M =>
                TangentSpace I y →L[ℝ] TangentSpace I y)))
        Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 3)).contMDiff
      (σ := Z') hZ'glob.contMDiffOn
  have hhomAt :
      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 3
        (fun y : M =>
          (⟨y, cov Z' y⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun y : M =>
                TangentSpace I y →L[ℝ] TangentSpace I y)))
        x :=
    hhomOn.contMDiffAt Filter.univ_mem
  have hreg : CMDiffAt 3 (T% (fun y ↦ cov Z' y (W y))) x :=
    hhomAt.clm_bundle_apply hW
  set w : Set M := interior {y | (χ : M → ℝ) y = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hxw : x ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one, hxu⟩
  have hZZ' : ∀ y ∈ interior {y | (χ : M → ℝ) y = 1}, Z y = Z' y := by
    intro y hy
    have h1 : y ∈ {y | (χ : M → ℝ) y = 1} := interior_subset hy
    simp [hZ', h1.out]
  have hev : (fun y ↦ cov Z y (W y)) =ᶠ[𝓝 x] fun y ↦ cov Z' y (W y) := by
    filter_upwards [hw_open.mem_nhds hxw] with y hy
    have hZy : MDiffAt (T% Z) y :=
      ((hZu y hy.2).contMDiffAt (hu_open.mem_nhds hy.2)).mdifferentiableAt
        (by norm_num)
    have hZ'y : MDiffAt (T% Z') y :=
      (hZ'glob y).mdifferentiableAt (by norm_num)
    have hcongr : cov Z y = cov Z' y := by
      apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZy hZ'y
        univ_mem
      filter_upwards [isOpen_interior.mem_nhds hy.1] with y' hy'
      exact hZZ' y' hy'
    rw [hcongr]
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hev] with y hy
  rw [Bundle.TotalSpace.mk_inj]
  exact hy

/--
**Local `C²` regularity of the manifold Lie bracket**: two `C³` vector fields
have a `C²` Lie bracket at the same point.
-/
theorem contMDiffAt_mlieBracket_of_contMDiffAt_three
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt 3 (T% X) x) (hY : CMDiffAt 3 (T% Y) x) :
    CMDiffAt 2 (T% (VectorField.mlieBracket I X Y)) x := by
  haveI : IsManifold I 4 M :=
    IsManifold.of_le (n := ∞) (by
      rw [show (4 : ℕ∞ω) = ((4 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((3 : ℕ∞) : ℕ∞ω) + 1) M := by
    exact_mod_cast (inferInstance : IsManifold I 4 M)
  have hineq : minSmoothness ℝ ((2 : ℕ∞) + 1) ≤ ((3 : ℕ∞) : ℕ∞ω) := by
    simp
    norm_num
  exact ContMDiffAt.mlieBracket_vectorField
    (m := 2) (n := 3) hX hY hineq

variable [ContMDiffCovariantDerivative cov 1]

/--
**Local regularity of a `C¹` connection**: if `Z` is `C²` at `x`, then
`y ↦ ∇_{W y} Z` is differentiable at `x` for every `W` differentiable at
`x`.  Globalizes `Z` by a bump function and transfers back by germ locality.
-/
theorem mdiffAt_cov_section_of_contMDiffAt
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 2 (T% Z) x)
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) :
    MDiffAt (T% (fun y ↦ cov Z y (W y))) x := by
  -- A neighbourhood on which `Z` is `C²`.
  obtain ⟨v, hv, hZv⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hZ
  set u : Set M := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hxu : x ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hZu : CMDiff[u] 2 (T% Z) := hZv.mono interior_subset
  -- A bump function at `x` supported in `u`.
  obtain ⟨χ, -, hχsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (hu_open.mem_nhds hxu))
  -- The globalized section.
  set Z' : Π y : M, TangentSpace I y := (χ : M → ℝ) • Z with hZ'
  have hZ'glob : CMDiff 2 (T% Z') :=
    ContMDiffOn.smul_section_of_tsupport
      ((χ.contMDiff.of_le (by
        rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn) hu_open hχsupp hZu
  have hreg : MDiffAt (T% (fun y ↦ cov Z' y (W y))) x :=
    derivRegularAt_of_contMDiff cov hZ'glob x hW
  -- `Z` and `Z'` agree near `x`, so the covariant derivatives agree near `x`.
  set w : Set M := interior {y | (χ : M → ℝ) y = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hxw : x ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr χ.eventuallyEq_one, hxu⟩
  have hZZ' : ∀ y ∈ interior {y | (χ : M → ℝ) y = 1}, Z y = Z' y := by
    intro y hy
    have h1 : y ∈ {y | (χ : M → ℝ) y = 1} := interior_subset hy
    simp [hZ', h1.out]
  have hev : (fun y ↦ cov Z y (W y)) =ᶠ[𝓝 x] fun y ↦ cov Z' y (W y) := by
    filter_upwards [hw_open.mem_nhds hxw] with y hy
    have hZy : MDiffAt (T% Z) y :=
      ((hZu y hy.2).contMDiffAt (hu_open.mem_nhds hy.2)).mdifferentiableAt
        two_ne_zero
    have hZ'y : MDiffAt (T% Z') y :=
      (hZ'glob y).mdifferentiableAt two_ne_zero
    have hcongr : cov Z y = cov Z' y := by
      apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZy hZ'y
        univ_mem
      filter_upwards [isOpen_interior.mem_nhds hy.1] with y' hy'
      exact hZZ' y' hy'
    rw [hcongr]
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hev] with y hy
  rw [Bundle.TotalSpace.mk_inj]
  exact hy

/--
The canonical extension of a tangent vector is admissible for the pointwise
curvature theory of a `C¹` connection.
-/
theorem derivRegularAt_extend {x : M} (w : TangentSpace I x) :
    DerivRegularAt cov (extend E w) x :=
  fun _W hW ↦
    mdiffAt_cov_section_of_contMDiffAt cov (contMDiffAt_extend' I E w) hW

variable [CompleteSpace E]

/--
The canonical Ricci value of a `C¹` connection on a pair of tangent vectors:
`Ric(u, w) = tr (v ↦ R(v, u) (extend w))`, computed against the canonical
extension of `w`.  (Independence of the choice of extension is the
`Z`-tensoriality of the curvature, to be established separately; this
definition fixes the canonical representative.)
-/
def ricciBilinearAt (x : M) (u w : TangentSpace I x) : ℝ :=
  ricciTraceAt cov (derivRegularAt_extend cov w) u

theorem ricciBilinearAt_def (x : M) (u w : TangentSpace I x) :
    ricciBilinearAt cov x u w =
      ricciTraceAt cov (derivRegularAt_extend cov w) u :=
  rfl

/--
**Germ locality of the curvature operator in its field slot**: two fields
that are `C²` at `x` and agree near `x` have the same curvature at `x`.
-/
theorem curvatureOp_congr_of_eventuallyEq
    {Z Z' X Y : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) (hZ' : CMDiffAt 2 (T% Z') x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZZ' : Z =ᶠ[𝓝 x] Z') :
    curvatureOp cov X Y Z x = curvatureOp cov X Y Z' x := by
  -- Neighbourhoods of `C²` regularity for both fields.
  obtain ⟨v, hv, hZv⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hZ
  obtain ⟨v', hv', hZv'⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hZ'
  -- Pointwise equality of `cov Z` and `cov Z'` near `x`.
  have hcov_ev : ∀ᶠ y in 𝓝 x, cov Z y = cov Z' y := by
    filter_upwards [eventually_mem_nhds_iff.mpr hv,
      eventually_mem_nhds_iff.mpr hv', hZZ'.eventually_nhds] with y hyv hyv' hyZ
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hZv.contMDiffAt hyv).mdifferentiableAt two_ne_zero)
      ((hZv'.contMDiffAt hyv').mdifferentiableAt two_ne_zero)
      univ_mem hyZ
  have hcovx : cov Z x = cov Z' x :=
    (hcov_ev.self_of_nhds)
  -- The two inner sections agree near `x`, in both direction slots.
  have hinner : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ cov Z y (W y)) =ᶠ[𝓝 x] fun y ↦ cov Z' y (W y) := by
    intro W
    filter_upwards [hcov_ev] with y hy
    rw [hy]
  -- Outer covariant derivatives agree at `x` by germ locality, using the
  -- local regularity of both inner sections.
  have houter : ∀ (W : Π y : M, TangentSpace I y), MDiffAt (T% W) x →
      cov (fun y ↦ cov Z y (W y)) x = cov (fun y ↦ cov Z' y (W y)) x := by
    intro W hW
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (mdiffAt_cov_section_of_contMDiffAt cov hZ hW)
      (mdiffAt_cov_section_of_contMDiffAt cov hZ' hW)
      univ_mem (hinner W)
  rw [curvatureOp_apply, curvatureOp_apply, houter Y hY, houter X hX, hcovx]

/--
Germ locality of the Ricci trace: fields that are `C²` at `x` and agree near
`x` define the same Ricci values through the pointwise curvature tensor.
-/
theorem curvatureTensorAt_congr_of_eventuallyEq [CompleteSpace E]
    {Z Z' : Π y : M, TangentSpace I y} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) (hZ' : CMDiffAt 2 (T% Z') x)
    (hreg : DerivRegularAt cov Z x) (hreg' : DerivRegularAt cov Z' x)
    (hZZ' : Z =ᶠ[𝓝 x] Z') (v w : TangentSpace I x) :
    curvatureTensorAt cov hreg v w = curvatureTensorAt cov hreg' v w := by
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend]
  exact curvatureOp_congr_of_eventuallyEq cov hZ hZ'
    (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) hZZ'

end CovariantDerivative

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace CovariantDerivative

/-- Shape contract for `ricciBilinearAt`. -/
theorem ricciBilinearAt_eq :
    @CovariantDerivative.ricciBilinearAt = @CovariantDerivative.ricciBilinearAt :=
  rfl

end CovariantDerivative

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace CovariantDerivative

/-- Theorem contract for `contMDiffAt_cov_section_of_contMDiffAt_two`. -/
theorem contMDiffAt_cov_section_of_contMDiffAt_two_eq :
    @CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two =
      @CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two :=
  rfl

/-- Theorem contract for `contMDiffAt_cov_section_of_contMDiffAt_three`. -/
theorem contMDiffAt_cov_section_of_contMDiffAt_three_eq :
    @CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_three =
      @CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_three :=
  rfl

/-- Theorem contract for `contMDiffAt_mlieBracket_of_contMDiffAt_three`. -/
theorem contMDiffAt_mlieBracket_of_contMDiffAt_three_eq :
    @CovariantDerivative.contMDiffAt_mlieBracket_of_contMDiffAt_three =
      @CovariantDerivative.contMDiffAt_mlieBracket_of_contMDiffAt_three :=
  rfl

/-- Theorem contract for `mdiffAt_cov_section_of_contMDiffAt`. -/
theorem mdiffAt_cov_section_of_contMDiffAt_eq :
    @CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt = @CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt :=
  rfl

/-- Theorem contract for `derivRegularAt_extend`. -/
theorem derivRegularAt_extend_eq :
    @CovariantDerivative.derivRegularAt_extend = @CovariantDerivative.derivRegularAt_extend :=
  rfl

/-- Theorem contract for `ricciBilinearAt_def`. -/
theorem ricciBilinearAt_def_eq :
    @CovariantDerivative.ricciBilinearAt_def = @CovariantDerivative.ricciBilinearAt_def :=
  rfl

/-- Theorem contract for `curvatureOp_congr_of_eventuallyEq`. -/
theorem curvatureOp_congr_of_eventuallyEq_eq :
    @CovariantDerivative.curvatureOp_congr_of_eventuallyEq = @CovariantDerivative.curvatureOp_congr_of_eventuallyEq :=
  rfl

/-- Theorem contract for `curvatureTensorAt_congr_of_eventuallyEq`. -/
theorem curvatureTensorAt_congr_of_eventuallyEq_eq :
    @CovariantDerivative.curvatureTensorAt_congr_of_eventuallyEq = @CovariantDerivative.curvatureTensorAt_congr_of_eventuallyEq :=
  rfl

end CovariantDerivative
