import Poincare.Global.RicciFlow

/-!
# Bump-globalized tangent extensions

This module globalizes Mathlib's locally smooth `FiberBundle.extend` sections
by multiplying them with a smooth bump function supported in a neighborhood on
which the extension is smooth.
-/

noncomputable section

open Bundle Set FiberBundle Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Germ locality of the Ricci trace in the field slot, specialized to closed
tangent fields.
-/
theorem ricciTraceAt_congr_of_eventuallyEq
    (cov : CovariantDerivative I E TM)
    {Z Z' : ∀ y : M, TM y} {x : M}
    (hZ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z) x)
    (hZ' : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% Z') x)
    (hreg : CovariantDerivative.DerivRegularAt cov Z x)
    (hreg' : CovariantDerivative.DerivRegularAt cov Z' x)
    (hZZ' : Z =ᶠ[𝓝 x] Z') (w : TM x) :
    CovariantDerivative.ricciTraceAt cov hreg w =
      CovariantDerivative.ricciTraceAt cov hreg' w := by
  unfold CovariantDerivative.ricciTraceAt
  have hend :
      CovariantDerivative.curvatureEndAt cov hreg w =
        CovariantDerivative.curvatureEndAt cov hreg' w := by
    apply LinearMap.ext
    intro u
    rw [CovariantDerivative.curvatureEndAt_apply,
      CovariantDerivative.curvatureEndAt_apply]
    exact CovariantDerivative.curvatureTensorAt_congr_of_eventuallyEq
      cov hZ hZ' hreg hreg' hZZ' u w
  rw [hend]

private abbrev tangentExtend (x : M) (v : TM x) : (y : M) → TM y :=
  @FiberBundle.extend M E TM _ _ _ _ _ _ x v

private theorem exists_bumpExtendCutoff (x : M) (v : TM x) :
    ∃ χ : SmoothBumpFunction I x, ∃ u : Set M,
      IsOpen u ∧ x ∈ u ∧ tsupport χ ⊆ u ∧
        ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% (tangentExtend (n := n) (M := M) x v)) u := by
  obtain ⟨s, hs, hsmooth⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := 2) I E v
  let u : Set M := interior s
  have hu_open : IsOpen u := isOpen_interior
  have hxu : x ∈ u := mem_interior_iff_mem_nhds.mpr hs
  obtain ⟨χ, -, hχsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport («I» := I) x).mem_iff.mp
      (hu_open.mem_nhds hxu))
  exact ⟨χ, u, hu_open, hxu, hχsupp, hsmooth.mono interior_subset⟩

private noncomputable def bumpExtendCutoff (x : M) (v : TM x) :
    SmoothBumpFunction I x :=
  Classical.choose (exists_bumpExtendCutoff (n := n) (M := M) x v)

private theorem bumpExtendCutoff_spec (x : M) (v : TM x) :
    ∃ u : Set M,
      IsOpen u ∧ x ∈ u ∧ tsupport (bumpExtendCutoff (n := n) (M := M) x v) ⊆ u ∧
        ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2
          (T% (tangentExtend (n := n) (M := M) x v)) u :=
  Classical.choose_spec (exists_bumpExtendCutoff (n := n) (M := M) x v)

/--
The canonical extension `extend E v`, cut off by a smooth bump supported inside
a neighborhood where the extension is `C²`.
-/
noncomputable def bumpExtend (x : M) (v : TM x) : (y : M) → TM y :=
  (bumpExtendCutoff (n := n) (M := M) x v : M → ℝ) •
    tangentExtend (n := n) (M := M) x v

/-- The bump-globalized extension is globally `C²`. -/
theorem bumpExtend_closedC2TangentField (x : M) (v : TM x) :
    ClosedC2TangentField (bumpExtend (n := n) (M := M) x v) := by
  rcases bumpExtendCutoff_spec (n := n) (M := M) x v with
    ⟨u, hu_open, _hxu, hχsupp, hsmooth⟩
  have hχ :
      ContMDiffOn I 𝓘(ℝ) 2
        (bumpExtendCutoff (n := n) (M := M) x v : M → ℝ) u :=
    ((bumpExtendCutoff (n := n) (M := M) x v).contMDiff.of_le (by
      rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn
  simpa [ClosedC2TangentField, bumpExtend] using
    ContMDiffOn.smul_section_of_tsupport
      (s := tangentExtend (n := n) (M := M) x v)
      (ψ := (bumpExtendCutoff (n := n) (M := M) x v : M → ℝ))
      hχ hu_open hχsupp hsmooth

/-- Near the anchor, the bump-globalized extension agrees with `extend`. -/
theorem bumpExtend_eventuallyEq_extend (x : M) (v : TM x) :
    bumpExtend (n := n) (M := M) x v =ᶠ[𝓝 x]
      (show (y : M) → TM y from extend E v) := by
  filter_upwards
    [(bumpExtendCutoff (n := n) (M := M) x v).eventuallyEq_one] with y hy
  change
    (((bumpExtendCutoff (n := n) (M := M) x v : M → ℝ) •
      tangentExtend (n := n) (M := M) x v) y) =
      tangentExtend (n := n) (M := M) x v y
  simp [hy]

/-- At the anchor, the bump-globalized extension has the prescribed value. -/
@[simp] theorem bumpExtend_apply_anchor (x : M) (v : TM x) :
    bumpExtend (n := n) (M := M) x v x = v := by
  have h := (bumpExtend_eventuallyEq_extend (n := n) (M := M) x v).eq_of_nhds
  simpa using h

/--
The covariant derivative of the bump-globalized extension agrees at the anchor
with the derivative of the canonical extension.
-/
theorem bumpExtend_covariantDerivative_eq_extend
    (cov : CovariantDerivative I E TM) (x : M) (v : TM x) :
    cov (bumpExtend (n := n) (M := M) x v) x =
      cov (show (y : M) → TM y from extend E v) x := by
  apply cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
  · exact ((bumpExtend_closedC2TangentField (n := n) (M := M) x v) x).mdifferentiableAt
      two_ne_zero
  · exact mdifferentiableAt_extend I E v
  · exact univ_mem
  · exact bumpExtend_eventuallyEq_extend (n := n) (M := M) x v

end Poincare
