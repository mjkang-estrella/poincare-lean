import Poincare.Global.GlobalParametrixAssemblyDefinitions
import Poincare.Global.FiniteAtlasBufferedTensorValueCompatibility

/-!
The finite transported scalar solvers take genuine symmetric forcing into the
original tensor submodule. This supplies the range proof used to construct the
global parametrix on the Hamilton input route.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.GlobalParametrixAssembly
open FiniteAtlasParabolicTensorSpace
universe u

/-- Actual transport support and chart values give the global solver sum its
support, symmetry and partition-weighted transition law. -/
theorem ambient_mem_and_chart_value
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (α T : ℝ)
    (S : Fin A.cover.chartCount → Scalar α T →L[ℝ] Jet α T)
    (B : Transports A α T)
    (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (hsupport : ∀ i j c d (w : SourceGraphs α T) t z,
      z ∉ coordSupport A i → (B i j c d w).u (t,z) = 0)
    (hchart : ∀ i j c d (w : SourceGraphs α T) t (x : M),
      x ∈ (chart A i).source →
      (B i j c d w).u (t,chart A i x) =
        A.partition i x * (@ite ℝ (x ∈ (chart A j).source)
          (Classical.propDecidable _)
          (∑ a : Fin 3, ∑ b : Fin 3,
            ξ j (chart A j x) * jac A i j x a c * jac A i j x b d *
              (w (a,b)).u (t,chart A j x)) 0)) :
    (∀ f : Y_M A α T,
      ambient A α T S B f ∈ tensorSubmodule A (evalX α T)) ∧
    (∀ (f : Y_M A α T) i c d t (x : M), x ∈ (chart A i).source →
      ((ambient A α T S B f) (i,c,d)).u (t,chart A i x) =
        FiniteAtlasBufferedTensorValue.value A ξ
          (fun j a b z => (S j (f.val (j,a,b))).u (t,z)) i c d x) := by
  classical
  have heval (f : Y_M A α T) i c d (p : ℝ × ClosedSmoothModel 3) :
      ((ambient A α T S B f) (i,c,d)).u p =
        ∑ j : Fin A.cover.chartCount,
          (B i j c d (localGraphs A α T S j f)).u p := by
    change evalX α T p ((∑ j : Fin A.cover.chartCount,
      (B i j c d).comp (localGraphs A α T S j)) f) = _
    rw [ContinuousLinearMap.sum_apply]
    exact map_sum (evalX α T p) _ _
  have hvalue (f : Y_M A α T) i c d t (x : M)
      (hx : x ∈ (chart A i).source) :
      ((ambient A α T S B f) (i,c,d)).u (t,chart A i x) =
        FiniteAtlasBufferedTensorValue.value A ξ
          (fun j a b z => (S j (f.val (j,a,b))).u (t,z)) i c d x := by
    rw [heval]
    simp_rw [hchart _ _ _ _ _ _ _ hx]
    unfold FiniteAtlasBufferedTensorValue.value
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : x ∈ (chart A j).source
    · simp only [if_pos hj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change A.partition i x *
        (ξ j (chart A j x) * jac A i j x a c * jac A i j x b d *
          (S j (f.val (j,a,b))).u (t,chart A j x)) = _
      ring
    · simp only [if_neg hj]
  refine ⟨?_, hvalue⟩
  intro f
  apply (mem_tensorSubmodule_iff A (evalX α T) _).mpr
  have hoff i c d t z (hz : z ∉ coordSupport A i) :
      ((ambient A α T S B f) (i,c,d)).u (t,z) = 0 := by
    rw [heval]
    simp only [hsupport _ _ _ _ _ _ _ hz, Finset.sum_const_zero]
  have hsource (j : Fin A.cover.chartCount) (a b : Fin 3) :
      f.val (j,a,b) = f.val (j,b,a) := by
    apply ParabolicHolder.ext
    intro p _
    exact ((mem_tensorSubmodule_iff A (evalY α T) f.val).mp f.property).1.2
      j a b p
  have hW (t : ℝ) j a b z :
      (S j (f.val (j,a,b))).u (t,z) = (S j (f.val (j,b,a))).u (t,z) := by
    rw [hsource j a b]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i c d t z hz
    exact hoff i c d t z hz
  · intro i c d p
    change ((ambient A α T S B f) (i,c,d)).u p =
      ((ambient A α T S B f) (i,d,c)).u p
    by_cases hz : p.2 ∈ coordSupport A i
    · obtain ⟨x, hx, hcx⟩ := hz
      have hxsource := partition_support_source A i hx
      have hp : p = (p.1, chart A i x) := Prod.ext rfl hcx.symm
      rw [hp, hvalue _ _ _ _ _ _ hxsource, hvalue _ _ _ _ _ _ hxsource]
      exact FiniteAtlasBufferedTensorValue.symmetric M A ξ _ (hW p.1) i c d x
    · rw [hoff i c d p.1 p.2 hz, hoff i d c p.1 p.2 hz]
  · intro i k c d t x hx
    rw [overlap_apply]
    change A.partition k x * ((ambient A α T S B f) (i,c,d)).u (t,chart A i x) -
      A.partition i x * ∑ a : Fin 3, ∑ b : Fin 3,
        (jac A i k x a c * jac A i k x b d) *
          ((ambient A α T S B f) (k,a,b)).u (t,chart A k x) = 0
    simp_rw [hvalue _ _ _ _ _ _ hx.1, hvalue _ _ _ _ _ _ hx.2]
    exact sub_eq_zero.mpr
      (FiniteAtlasBufferedTensorValue.weighted_transition M A ξ _ i k c d x hx.1 hx.2)

end Poincare.GlobalParametrixAssembly
