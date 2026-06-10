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

end CovariantDerivative
