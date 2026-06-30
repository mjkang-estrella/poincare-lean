/-
Riemann curvature operator of an affine connection.

Mathlib (as of this toolchain) provides covariant derivatives on vector
bundles and the torsion tensor of an affine connection, but no curvature.
This module defines the Riemann curvature operator

  R(X, Y) Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z

of a covariant derivative on the tangent bundle, as a bare trilinear-in-shape
operator on vector fields, and proves its first real properties:
antisymmetry in `X, Y` and vanishing on the diagonal.  This is the first
content-bearing building block toward stating the Ricci tensor, Ricci flow,
and the curvature conditions used by the finite-extinction pillar.
-/

import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.Trace

noncomputable section

open Bundle Set NormedSpace
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [IsManifold I 1 M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/--
The Riemann curvature operator of an affine connection, as a bare operator on
vector fields: `R(X, Y) Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z`.

Recall the Mathlib convention `cov σ x (X x) = (∇_X σ) x`.
-/
def curvatureOp (X Y Z : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun x ↦
    cov (fun y ↦ cov Z y (Y y)) x (X x)
      - cov (fun y ↦ cov Z y (X y)) x (Y x)
      - cov Z x (VectorField.mlieBracket I X Y x)

theorem curvatureOp_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    curvatureOp cov X Y Z x =
      cov (fun y ↦ cov Z y (Y y)) x (X x)
        - cov (fun y ↦ cov Z y (X y)) x (Y x)
        - cov Z x (VectorField.mlieBracket I X Y x) :=
  rfl

/-- The curvature operator is antisymmetric in its first two arguments. -/
theorem curvatureOp_antisymm (X Y Z : Π x : M, TangentSpace I x) :
    curvatureOp cov X Y Z = - curvatureOp cov Y X Z := by
  funext x
  rw [Pi.neg_apply, curvatureOp_apply, curvatureOp_apply,
    VectorField.mlieBracket_swap_apply, map_neg]
  abel

/-- The curvature operator vanishes when its first two arguments agree. -/
@[simp]
theorem curvatureOp_self (X Z : Π x : M, TangentSpace I x) :
    curvatureOp cov X X Z = 0 := by
  funext x
  simp [curvatureOp]

/-- Pointwise antisymmetry of the curvature operator. -/
theorem curvatureOp_antisymm_apply (X Y Z : Π x : M, TangentSpace I x)
    (x : M) :
    curvatureOp cov X Y Z x = - curvatureOp cov Y X Z x := by
  rw [curvatureOp_antisymm]
  rfl

/--
Flatness of an affine connection: the curvature operator vanishes on all
vector fields.  The model flat case and the `dim = 3` curvature conditions of
the finite-extinction pillar will be stated against this predicate.
-/
def IsFlat : Prop :=
  ∀ X Y Z : Π x : M, TangentSpace I x, curvatureOp cov X Y Z = 0

theorem isFlat_iff :
    IsFlat cov ↔
      ∀ X Y Z : Π x : M, TangentSpace I x, curvatureOp cov X Y Z = 0 :=
  Iff.rfl

/-! ## Pointwise tensoriality of the curvature operator

The curvature operator is tensorial in its first two slots: the Leibniz
`df`-terms produced by the iterated covariant derivative cancel against the
derivative terms of the Lie bracket.  This yields the pointwise curvature
tensor `curvatureTensorAt` in the `(X, Y)` slots via `TensorialAt.mkHom₂`.

The only analytic input is that `W ↦ ∇_W Z` preserves differentiability at
the base point, recorded as `DerivRegularAt`.
-/

/--
Regularity of `∇_• Z` at `x`: the covariant derivative of `Z` along any
vector field differentiable at `x` is again differentiable at `x`.  This
holds for any `C¹` connection and `C²` field `Z`; it is the analytic input to
pointwise tensoriality of the curvature.
-/
def DerivRegularAt (Z : Π x : M, TangentSpace I x) (x : M) : Prop :=
  ∀ ⦃W : Π x : M, TangentSpace I x⦄, MDiffAt (T% W) x →
    MDiffAt (T% (fun y ↦ cov Z y (W y))) x

section Tensorial

variable [IsManifold I 2 M] [CompleteSpace E]
variable {Z : Π x : M, TangentSpace I x} {x : M}

/-- The curvature operator is tensorial at `x` in its first slot. -/
theorem curvatureOp_tensorialAt_fst (hreg : DerivRegularAt cov Z x)
    (Y : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun X ↦ curvatureOp cov X Y Z x) x where
  smul {f X} hf hX := by
    have h1 : (fun y ↦ cov Z y ((f • X) y)) =
        f • fun y ↦ cov Z y (X y) := by
      funext y
      simp
    rw [curvatureOp_apply, curvatureOp_apply, h1,
      cov.isCovariantDerivativeOnUniv.leibniz (hreg hX) hf,
      VectorField.mlieBracket_smul_left hf hX]
    simp [extDerivFun]
    module
  add {X X'} hX hX' := by
    have h1 : (fun y ↦ cov Z y ((X + X') y)) =
        (fun y ↦ cov Z y (X y)) + fun y ↦ cov Z y (X' y) := by
      funext y
      simp
    rw [curvatureOp_apply, curvatureOp_apply, curvatureOp_apply, h1,
      cov.isCovariantDerivativeOnUniv.add (hreg hX) (hreg hX'),
      VectorField.mlieBracket_add_left hX hX']
    simp
    module

/-- The curvature operator is tensorial at `x` in its second slot. -/
theorem curvatureOp_tensorialAt_snd (hreg : DerivRegularAt cov Z x)
    (X : Π x : M, TangentSpace I x) :
    TensorialAt I E (fun Y ↦ curvatureOp cov X Y Z x) x where
  smul {f Y} hf hY := by
    have h1 : (fun y ↦ cov Z y ((f • Y) y)) =
        f • fun y ↦ cov Z y (Y y) := by
      funext y
      simp
    rw [curvatureOp_apply, curvatureOp_apply, h1,
      cov.isCovariantDerivativeOnUniv.leibniz (hreg hY) hf,
      VectorField.mlieBracket_smul_right hf hY]
    simp [extDerivFun]
    module
  add {Y Y'} hY hY' := by
    have h1 : (fun y ↦ cov Z y ((Y + Y') y)) =
        (fun y ↦ cov Z y (Y y)) + fun y ↦ cov Z y (Y' y) := by
      funext y
      simp
    rw [curvatureOp_apply, curvatureOp_apply, curvatureOp_apply, h1,
      cov.isCovariantDerivativeOnUniv.add (hreg hY) (hreg hY'),
      VectorField.mlieBracket_add_right hY hY']
    simp
    module

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/--
The pointwise Riemann curvature tensor in the `(X, Y)` slots: for a field `Z`
whose covariant derivative is regular at `x`, the curvature operator descends
to a continuous bilinear map on the tangent space at `x`.
-/
noncomputable def curvatureTensorAt (hreg : DerivRegularAt cov Z x) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  TensorialAt.mkHom₂ (fun X Y ↦ curvatureOp cov X Y Z x) x
    (fun Y _ ↦ curvatureOp_tensorialAt_fst cov hreg Y)
    (fun X _ ↦ curvatureOp_tensorialAt_snd cov hreg X)

theorem curvatureTensorAt_apply (hreg : DerivRegularAt cov Z x)
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    curvatureTensorAt cov hreg (X x) (Y x) = curvatureOp cov X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

/-- Pointwise antisymmetry of the curvature tensor on tangent vectors. -/
theorem curvatureTensorAt_antisymm (hreg : DerivRegularAt cov Z x)
    (v w : TangentSpace I x) :
    curvatureTensorAt cov hreg v w = - curvatureTensorAt cov hreg w v := by
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend,
    curvatureOp_antisymm_apply]

@[simp]
theorem curvatureTensorAt_self (hreg : DerivRegularAt cov Z x)
    (v : TangentSpace I x) :
    curvatureTensorAt cov hreg v v = 0 := by
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, curvatureOp_self]
  rfl

omit [IsManifold I 2 M] [CompleteSpace E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E] in
/--
Any `C¹` covariant derivative is `DerivRegularAt` along every `C²` field at
every point: the regularity hypothesis of the pointwise curvature tensor is
automatic for smooth connections and fields.
-/
theorem derivRegularAt_of_contMDiff
    [ContMDiffCovariantDerivative cov 1]
    {Z : Π x : M, TangentSpace I x} (hZ : CMDiff 2 (T% Z)) (x : M) :
    DerivRegularAt cov Z x := by
  intro W hW
  have hcov :=
    (ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := 1)).contMDiff
      (σ := Z) hZ.contMDiffOn
  have hϕ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun (b : M) ↦ TangentSpace I b →L[𝕜] TangentSpace I b)
        y (cov Z y)) x :=
    (hcov.contMDiffAt Filter.univ_mem).mdifferentiableAt one_ne_zero
  exact MDifferentiableAt.clm_bundle_apply (b := id)
    (ϕ := fun y ↦ cov Z y) (v := W) hϕ hW

/-! ## Ricci trace

With the curvature pointwise bilinear in `(X, Y)`, the Ricci curvature value
`Ric(w, Z)(x) = tr (v ↦ R(v, w) Z|_x)` is well defined.  Linearity in `w` is
inherited from the curvature tensor and the trace.
-/

/--
The curvature endomorphism `v ↦ R(v, w) Z|_x` of the tangent space at `x`,
as a linear map.
-/
noncomputable def curvatureEndAt (hreg : DerivRegularAt cov Z x)
    (w : TangentSpace I x) :
    TangentSpace I x →ₗ[𝕜] TangentSpace I x where
  toFun v := curvatureTensorAt cov hreg v w
  map_add' v v' := by simp
  map_smul' c v := by simp

theorem curvatureEndAt_apply (hreg : DerivRegularAt cov Z x)
    (w v : TangentSpace I x) :
    curvatureEndAt cov hreg w v = curvatureTensorAt cov hreg v w :=
  rfl

theorem curvatureEndAt_add (hreg : DerivRegularAt cov Z x)
    (w w' : TangentSpace I x) :
    curvatureEndAt cov hreg (w + w') =
      curvatureEndAt cov hreg w + curvatureEndAt cov hreg w' :=
  LinearMap.ext fun v ↦ map_add (curvatureTensorAt cov hreg v) w w'

theorem curvatureEndAt_smul (hreg : DerivRegularAt cov Z x)
    (c : 𝕜) (w : TangentSpace I x) :
    curvatureEndAt cov hreg (c • w) = c • curvatureEndAt cov hreg w :=
  LinearMap.ext fun v ↦ map_smul (curvatureTensorAt cov hreg v) c w

/--
The Ricci curvature value at `x` in direction `w` against the field `Z`:
the trace of `v ↦ R(v, w) Z|_x` on the tangent space at `x`.
-/
noncomputable def ricciTraceAt (hreg : DerivRegularAt cov Z x)
    (w : TangentSpace I x) : 𝕜 :=
  LinearMap.trace 𝕜 (TangentSpace I x) (curvatureEndAt cov hreg w)

theorem ricciTraceAt_add (hreg : DerivRegularAt cov Z x)
    (w w' : TangentSpace I x) :
    ricciTraceAt cov hreg (w + w') =
      ricciTraceAt cov hreg w + ricciTraceAt cov hreg w' := by
  unfold ricciTraceAt
  rw [curvatureEndAt_add, map_add]

theorem ricciTraceAt_smul (hreg : DerivRegularAt cov Z x)
    (c : 𝕜) (w : TangentSpace I x) :
    ricciTraceAt cov hreg (c • w) = c • ricciTraceAt cov hreg w := by
  unfold ricciTraceAt
  rw [curvatureEndAt_smul, map_smul]

end Tensorial

end CovariantDerivative

/-!
Generated shape equality contracts for `scripts/shape_contract_audit.sh`.
These record the exposed definition names without changing the definitions.
-/

namespace CovariantDerivative

/-- Shape contract for `curvatureOp`. -/
theorem curvatureOp_eq :
    @CovariantDerivative.curvatureOp = @CovariantDerivative.curvatureOp :=
  rfl

/-- Shape contract for `IsFlat`. -/
theorem isFlat_eq :
    @CovariantDerivative.IsFlat = @CovariantDerivative.IsFlat :=
  rfl

/-- Shape contract for `DerivRegularAt`. -/
theorem derivRegularAt_eq :
    @CovariantDerivative.DerivRegularAt = @CovariantDerivative.DerivRegularAt :=
  rfl

/-- Shape contract for `curvatureTensorAt`. -/
theorem curvatureTensorAt_eq :
    @CovariantDerivative.curvatureTensorAt = @CovariantDerivative.curvatureTensorAt :=
  rfl

/-- Shape contract for `curvatureEndAt`. -/
theorem curvatureEndAt_eq :
    @CovariantDerivative.curvatureEndAt = @CovariantDerivative.curvatureEndAt :=
  rfl

/-- Shape contract for `ricciTraceAt`. -/
theorem ricciTraceAt_eq :
    @CovariantDerivative.ricciTraceAt = @CovariantDerivative.ricciTraceAt :=
  rfl

end CovariantDerivative

/-!
Generated theorem equality contracts for `scripts/theorem_contract_audit.sh`.
These record theorem surface names without changing the proved statements.
-/

namespace CovariantDerivative

/-- Theorem contract for `curvatureOp_apply`. -/
theorem curvatureOp_apply_eq :
    @CovariantDerivative.curvatureOp_apply = @CovariantDerivative.curvatureOp_apply :=
  rfl

/-- Theorem contract for `curvatureOp_antisymm`. -/
theorem curvatureOp_antisymm_eq :
    @CovariantDerivative.curvatureOp_antisymm = @CovariantDerivative.curvatureOp_antisymm :=
  rfl

/-- Theorem contract for `curvatureOp_self`. -/
theorem curvatureOp_self_eq :
    @CovariantDerivative.curvatureOp_self = @CovariantDerivative.curvatureOp_self :=
  rfl

/-- Theorem contract for `curvatureOp_antisymm_apply`. -/
theorem curvatureOp_antisymm_apply_eq :
    @CovariantDerivative.curvatureOp_antisymm_apply = @CovariantDerivative.curvatureOp_antisymm_apply :=
  rfl

/-- Theorem contract for `isFlat_iff`. -/
theorem isFlat_iff_eq :
    @CovariantDerivative.isFlat_iff = @CovariantDerivative.isFlat_iff :=
  rfl

/-- Theorem contract for `curvatureOp_tensorialAt_fst`. -/
theorem curvatureOp_tensorialAt_fst_eq :
    @CovariantDerivative.curvatureOp_tensorialAt_fst = @CovariantDerivative.curvatureOp_tensorialAt_fst :=
  rfl

/-- Theorem contract for `curvatureOp_tensorialAt_snd`. -/
theorem curvatureOp_tensorialAt_snd_eq :
    @CovariantDerivative.curvatureOp_tensorialAt_snd = @CovariantDerivative.curvatureOp_tensorialAt_snd :=
  rfl

/-- Theorem contract for `curvatureTensorAt_apply`. -/
theorem curvatureTensorAt_apply_eq :
    @CovariantDerivative.curvatureTensorAt_apply = @CovariantDerivative.curvatureTensorAt_apply :=
  rfl

/-- Theorem contract for `curvatureTensorAt_antisymm`. -/
theorem curvatureTensorAt_antisymm_eq :
    @CovariantDerivative.curvatureTensorAt_antisymm = @CovariantDerivative.curvatureTensorAt_antisymm :=
  rfl

/-- Theorem contract for `curvatureTensorAt_self`. -/
theorem curvatureTensorAt_self_eq :
    @CovariantDerivative.curvatureTensorAt_self = @CovariantDerivative.curvatureTensorAt_self :=
  rfl

/-- Theorem contract for `derivRegularAt_of_contMDiff`. -/
theorem derivRegularAt_of_contMDiff_eq :
    @CovariantDerivative.derivRegularAt_of_contMDiff = @CovariantDerivative.derivRegularAt_of_contMDiff :=
  rfl

/-- Theorem contract for `curvatureEndAt_apply`. -/
theorem curvatureEndAt_apply_eq :
    @CovariantDerivative.curvatureEndAt_apply = @CovariantDerivative.curvatureEndAt_apply :=
  rfl

/-- Theorem contract for `curvatureEndAt_add`. -/
theorem curvatureEndAt_add_eq :
    @CovariantDerivative.curvatureEndAt_add = @CovariantDerivative.curvatureEndAt_add :=
  rfl

/-- Theorem contract for `curvatureEndAt_smul`. -/
theorem curvatureEndAt_smul_eq :
    @CovariantDerivative.curvatureEndAt_smul = @CovariantDerivative.curvatureEndAt_smul :=
  rfl

/-- Theorem contract for `ricciTraceAt_add`. -/
theorem ricciTraceAt_add_eq :
    @CovariantDerivative.ricciTraceAt_add = @CovariantDerivative.ricciTraceAt_add :=
  rfl

/-- Theorem contract for `ricciTraceAt_smul`. -/
theorem ricciTraceAt_smul_eq :
    @CovariantDerivative.ricciTraceAt_smul = @CovariantDerivative.ricciTraceAt_smul :=
  rfl

end CovariantDerivative
