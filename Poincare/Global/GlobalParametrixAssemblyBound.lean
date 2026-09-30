import Poincare.Global.GlobalParametrixAssemblyDefinitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff

namespace Poincare.GlobalParametrixAssembly
open FiniteAtlasParabolicTensorSpace
universe u

/-- The assembled solver is bounded using only its supported forcing estimates. -/
theorem ambient_norm_le (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (α T : ℝ)
    (S : Fin A.cover.chartCount → Scalar α T →L[ℝ] Jet α T)
    (B : Transports A α T)
    (CP : ℝ) (CB : Fin A.cover.chartCount → Fin A.cover.chartCount → Fin 3 → Fin 3 → ℝ)
    (hCP : 0 ≤ CP) (hCB : ∀ i j c d, 0 ≤ CB i j c d)
    (hB : ∀ i j c d, ‖B i j c d‖ ≤ CB i j c d)
    (hS : ∀ j (h : Scalar α T),
      (∀ p, p.2 ∉ coordSupport A j → h p = 0) → ‖S j h‖ ≤ CP * ‖h‖) :
    ‖ambient A α T S B‖ ≤ CP *
      (∑ i : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
        ∑ c : Fin 3, ∑ d : Fin 3, CB i j c d) := by
  classical
  have htotal : 0 ≤ ∑ i : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
      ∑ c : Fin 3, ∑ d : Fin 3, CB i j c d := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hCB i j c d
  have hrow (i : Fin A.cover.chartCount) (c d : Fin 3) :
      (∑ j : Fin A.cover.chartCount, CB i j c d) ≤
        ∑ i' : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
          ∑ c' : Fin 3, ∑ d' : Fin 3, CB i' j c' d' := by
    calc
      _ ≤ ∑ j : Fin A.cover.chartCount, ∑ c' : Fin 3, ∑ d' : Fin 3,
          CB i j c' d' := Finset.sum_le_sum fun j _ =>
        (Finset.single_le_sum (fun d' _ => hCB i j c d') (Finset.mem_univ d)).trans
          (Finset.single_le_sum (fun c' _ => Finset.sum_nonneg fun d' _ =>
            hCB i j c' d') (Finset.mem_univ c))
      _ ≤ _ := Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun c' _ => Finset.sum_nonneg fun d' _ => hCB i' j c' d')
        (Finset.mem_univ i)
  refine (ambient A α T S B).opNorm_le_bound (mul_nonneg hCP htotal) fun f => ?_
  have hlocal (j : Fin A.cover.chartCount) :
      ‖localGraphs A α T S j f‖ ≤ CP * ‖f‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCP (norm_nonneg f))).mpr fun k => ?_
    change ‖S j (f.val (j, k.1, k.2))‖ ≤ CP * ‖f‖
    apply (hS j (f.val (j, k.1, k.2)) (fun p hp =>
      supported_entry A (evalY α T) f j k.1 k.2 p.1 p.2 hp)).trans
    exact mul_le_mul_of_nonneg_left (norm_entry_le A (evalY α T) f (j, k.1, k.2)) hCP
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg hCP htotal) (norm_nonneg f))).mpr fun k => ?_
  simp only [ambient, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ∑ j : Fin A.cover.chartCount,
        ‖B k.1 j k.2.1 k.2.2 (localGraphs A α T S j f)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin A.cover.chartCount, CB k.1 j k.2.1 k.2.2 * (CP * ‖f‖) :=
      Finset.sum_le_sum fun j _ =>
        ((B k.1 j k.2.1 k.2.2).le_of_opNorm_le (hB k.1 j k.2.1 k.2.2) _).trans
          (mul_le_mul_of_nonneg_left (hlocal j) (hCB k.1 j k.2.1 k.2.2))
    _ = (∑ j : Fin A.cover.chartCount, CB k.1 j k.2.1 k.2.2) * (CP * ‖f‖) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
        ∑ c : Fin 3, ∑ d : Fin 3, CB i j c d) * (CP * ‖f‖) :=
      mul_le_mul_of_nonneg_right (hrow k.1 k.2.1 k.2.2) (mul_nonneg hCP (norm_nonneg f))
    _ = _ := by ring

end Poincare.GlobalParametrixAssembly
