import Poincare.Global.FiniteAtlasParabolicTensorSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Finite-atlas Jacobian cocycles

The Jacobians below are derivatives of the existing extended-chart changes.
Their identities require membership in the genuine chart sources.  These
algebraic transition identities do not assert any norm bound or reconstruction.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff

namespace Poincare.FiniteAtlasParabolicTensorSpace

open Poincare

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "E" => ClosedSmoothModel 3
local notation "𝓘" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

/-- Entries of the composite of two linear maps are the product of their
entries in the fixed Euclidean basis. -/
theorem comp_basis_entry (F G : E →L[ℝ] E) (c a : Fin 3) :
    ((G.comp F) (e a)) c = ∑ b : Fin 3, (G (e b)) c * (F (e a)) b := by
  rw [ContinuousLinearMap.comp_apply]
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (F (e a))]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

variable (A : AtlasData M)

/-- On a genuine chart overlap, the ordinary transition derivative is the
tangent-coordinate change.  The model has no boundary, so its range is all
of the Euclidean model space. -/
theorem fderiv_change_eq_tangentCoordChange
    (i j : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source) :
    fderiv ℝ (change A i j) (chart A i x) =
      tangentCoordChange 𝓘 (A.cover.anchor i) (A.cover.anchor j) x := by
  have hwithin := hasFDerivWithinAt_tangentCoordChange
    (I := 𝓘) (x := A.cover.anchor i) (y := A.cover.anchor j) (z := x)
    ⟨hi, hj⟩
  have hat : HasFDerivAt (change A i j)
      (tangentCoordChange 𝓘 (A.cover.anchor i) (A.cover.anchor j) x)
      (chart A i x) := by
    simpa [chart, change, Function.comp_def, ModelWithCorners.range_eq_univ]
      using hwithin
  exact hat.fderiv

/-- The Jacobian entries retain the genuine tangent-coordinate change on
the overlap where the chart change is defined. -/
theorem jac_eq_tangentCoordChange
    (i j : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source)
    (c a : Fin 3) :
    jac A i j x c a =
      (tangentCoordChange 𝓘 (A.cover.anchor i) (A.cover.anchor j) x (e a)) c := by
  rw [jac, fderiv_change_eq_tangentCoordChange A i j x hi hj]

/-- A chart's Jacobian to itself is the identity matrix at every point of
that chart's source. -/
theorem jac_self (i : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (c a : Fin 3) :
    jac A i i x c a = if c = a then 1 else 0 := by
  rw [jac_eq_tangentCoordChange A i i x hi hi]
  rw [tangentCoordChange_self hi]
  simp [EuclideanSpace.basisFun_apply]

/-- Transition derivatives compose on the actual triple chart overlap. -/
theorem fderiv_change_cocycle
    (i j k : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source)
    (hk : x ∈ (chart A k).source) :
    fderiv ℝ (change A i k) (chart A i x) =
      (fderiv ℝ (change A j k) (chart A j x)).comp
        (fderiv ℝ (change A i j) (chart A i x)) := by
  rw [fderiv_change_eq_tangentCoordChange A i k x hi hk,
    fderiv_change_eq_tangentCoordChange A j k x hj hk,
    fderiv_change_eq_tangentCoordChange A i j x hi hj]
  apply ContinuousLinearMap.ext
  intro v
  exact (tangentCoordChange_comp (I := 𝓘)
    (w := A.cover.anchor i) (x := A.cover.anchor j)
    (y := A.cover.anchor k) (z := x) (v := v) ⟨⟨hi, hj⟩, hk⟩).symm

/-- The actual finite-atlas Jacobians obey the matrix cocycle law on the
triple intersection of their chart sources. -/
theorem jac_cocycle
    (i j k : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source)
    (hk : x ∈ (chart A k).source) (c a : Fin 3) :
    jac A i k x c a = ∑ b : Fin 3, jac A j k x c b * jac A i j x b a := by
  simp only [jac]
  rw [fderiv_change_cocycle A i j k x hi hj hk]
  exact comp_basis_entry _ _ c a

/-- Reversing a genuine chart change gives the inverse Jacobian matrix. -/
theorem jac_left_inverse
    (i j : Fin A.cover.chartCount) (x : M)
    (hi : x ∈ (chart A i).source) (hj : x ∈ (chart A j).source)
    (c a : Fin 3) :
    (∑ b : Fin 3, jac A j i x c b * jac A i j x b a) =
      if c = a then 1 else 0 := by
  rw [← jac_cocycle A i j i x hi hj hi c a, jac_self A i x hi c a]

end Poincare.FiniteAtlasParabolicTensorSpace
