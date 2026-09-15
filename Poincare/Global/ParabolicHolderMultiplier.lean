import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.RiemannianContext

noncomputable section

namespace Poincare.ParabolicHolderMultiplier

open Set ParabolicHolder ParabolicSolutionGraph

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- The first spatial derivative of the zero initial trace vanishes. -/
theorem du_zero_trace (G : Graph («E» := E) α T) (hT : 0 < T) (x : E) :
    G.du (0, x) = 0 := by
  have h := G.hasFDeriv 0 ⟨le_rfl, hT.le⟩ x
  simp only [G.zero_trace] at h
  exact h.unique (hasFDerivAt_const (0 : ℝ) x)

/-- The spatial Hessian of the zero initial trace vanishes. -/
theorem ddu_zero_trace (G : Graph («E» := E) α T) (hT : 0 < T) (x : E) :
    G.ddu (0, x) = 0 := by
  have h := G.hasFDeriv_du 0 ⟨le_rfl, hT.le⟩ x
  simp only [du_zero_trace G hT] at h
  exact h.unique (hasFDerivAt_const (0 : E →L[ℝ] ℝ) x)

/-- Comparison with time zero gives the short-time Hessian factor. -/
theorem ddu_time_bound (G : Graph («E» := E) α T) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖G.ddu (t, x)‖ ≤ ‖G.ddu‖ * t ^ (α / 2) := by
  have h := ParabolicHolder.holder_le G.ddu
    (show (t, x) ∈ cylinder T from ⟨ht, mem_univ x⟩)
    (show (0, x) ∈ cylinder T from ⟨⟨le_rfl, hT.le⟩, mem_univ x⟩)
  have he : (Real.sqrt t) ^ α = t ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1]
    congr 1
    ring
  simpa only [ddu_zero_trace G hT, sub_zero, parabolicDist, sub_self,
    norm_zero, zero_add, abs_of_nonneg ht.1, he] using h

/-- The Hessian sup norm is small on a short cylinder. -/
theorem supNorm_ddu_le (G : Graph («E» := E) α T) (hα : 0 < α) (hT : 0 < T) :
    supNorm (cylinder T) G.ddu ≤ T ^ (α / 2) * ‖G‖ := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨p, rfl⟩)
  · exact mul_nonneg (Real.rpow_nonneg hT.le _) (norm_nonneg _)
  · calc
      ‖G.ddu p‖ ≤ ‖G.ddu‖ * p.val.1 ^ (α / 2) := ddu_time_bound G hT p.property.1 p.val.2
      _ ≤ ‖G‖ * T ^ (α / 2) := mul_le_mul (norm_ddu_le G)
        (Real.rpow_le_rpow p.property.1.1 p.property.1.2 (by linarith))
        (Real.rpow_nonneg p.property.1.1 _) (norm_nonneg G)
      _ = _ := mul_comm _ _

end Poincare.ParabolicHolderMultiplier
