import Poincare.Global.FiniteAtlasBufferedTensorValueDefinitions

/-!
# Compatibility of the actual buffered finite tensor sum

These algebraic identities supply the tensor-submodule conditions for the
constructed Graph transport operators. They are used on the Hamilton input
route before constructing a global parametrix; no compatible source field is
assumed for the transition identity.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.FiniteAtlasBufferedTensorValue
open FiniteAtlasParabolicTensorSpace
universe u

/-- The actual destination-weighted sum transforms through any genuine
intermediate chart, without cancelling partition values. -/
theorem weighted_transition
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M)
    (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (W : Fin A.cover.chartCount → Fin 3 → Fin 3 → ClosedSmoothModel 3 → ℝ)
    (i k : Fin A.cover.chartCount) (a b : Fin 3) (x : M)
    (hi : x ∈ (chart A i).source) (hk : x ∈ (chart A k).source) :
    A.partition k x * value A ξ W i a b x =
      A.partition i x * ∑ p : Fin 3, ∑ q : Fin 3,
        (jac A i k x p a * jac A i k x q b) * value A ξ W k p q x := by
  classical
  have hsource (j : Fin A.cover.chartCount) :
      (if x ∈ (chart A j).source then
        ξ j (chart A j x) * ∑ c : Fin 3, ∑ d : Fin 3,
          (jac A i j x c a * jac A i j x d b) * W j c d (chart A j x)
        else 0) =
      ∑ p : Fin 3, ∑ q : Fin 3,
        (jac A i k x p a * jac A i k x q b) *
          (if x ∈ (chart A j).source then
            ξ j (chart A j x) * ∑ c : Fin 3, ∑ d : Fin 3,
              (jac A k j x c p * jac A k j x d q) * W j c d (chart A j x)
            else 0) := by
    by_cases hj : x ∈ (chart A j).source
    · simp only [if_pos hj]
      rw [covariant_twoTensor_cocycle A i k j x hi hk hj]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
    · simp only [if_neg hj, mul_zero, Finset.sum_const_zero]
  unfold value
  simp_rw [hsource]
  rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Symmetric source arrays yield a symmetric actual finite tensor sum. -/
theorem symmetric
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M)
    (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (W : Fin A.cover.chartCount → Fin 3 → Fin 3 → ClosedSmoothModel 3 → ℝ)
    (hW : ∀ j a b z, W j a b z = W j b a z)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (x : M) :
    value A ξ W i a b x = value A ξ W i b a x := by
  classical
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : x ∈ (chart A j).source
  · simp only [if_pos hj]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hW j d c]
    ring
  · simp only [if_neg hj]

end Poincare.FiniteAtlasBufferedTensorValue
