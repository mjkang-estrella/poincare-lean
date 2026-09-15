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

/-- Evaluation on two unit vectors does not increase the bilinear operator norm. -/
theorem eval_norm_le (A : Bilin) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖A v w‖ ≤ ‖A‖ := by
  simpa only [hv, hw, mul_one] using ContinuousLinearMap.le_opNorm₂ A v w

/-- Bounded evaluation preserves the Hölder seminorm bound. -/
theorem entry_holderBound (H : Y («E» := E) α T Bilin) {v w : E}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    HasHolderBound α (cylinder T) (fun p => H p v w)
      (holderSeminorm α (cylinder T) H) := by
  intro p hp q hq
  have h := eval_norm_le (H p - H q) hv hw
  simp only [ContinuousLinearMap.sub_apply] at h
  exact h.trans (hasHolderBound_seminorm H p hp q hq)

/-- A coordinate entry is a supported bounded Hölder function. -/
def entry (H : Y («E» := E) α T Bilin) (v w : E)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : Y («E» := E) α T ℝ :=
  ofFunction (fun p => H p v w)
    (fun p hp => by dsimp only; rw [zero_off H hp]; simp)
    ⟨supNorm (cylinder T) H, fun p _ =>
      (eval_norm_le (H p) hv hw).trans (le_supNorm H p)⟩
    ⟨_, entry_holderBound H hv hw⟩

@[simp] theorem entry_apply (H : Y («E» := E) α T Bilin) (v w : E)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (p : ℝ × E) :
    entry H v w hv hw p = H p v w := rfl

/-- The entry's sup norm is bounded by the tensor's sup norm. -/
theorem supNorm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    supNorm (cylinder T) (entry H v w hv hw) ≤ supNorm (cylinder T) H := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨p, rfl⟩)
  · exact supNorm_nonneg H
  · exact (eval_norm_le (H p) hv hw).trans (le_supNorm H p)

/-- Unit coordinate evaluation has norm at most one on the Hölder space. -/
theorem norm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖entry H v w hv hw‖ ≤ ‖H‖ := by
  rw [ParabolicHolder.norm_eq H]
  apply norm_le_of_bounds _ (supNorm_nonneg H) (holderSeminorm_nonneg H)
  · intro p _
    exact (eval_norm_le (H p) hv hw).trans (le_supNorm H p)
  · exact entry_holderBound H hv hw

/-- The split product estimate retains the small sup factor on the second term. -/
theorem norm_mul_split (b h : Y («E» := E) α T ℝ) :
    ‖b * h‖ ≤ supNorm (cylinder T) b * ‖h‖ +
      holderSeminorm α (cylinder T) b * supNorm (cylinder T) h := by
  have hb : ∀ p ∈ cylinder T,
      ‖(b * h) p‖ ≤ supNorm (cylinder T) b * supNorm (cylinder T) h := by
    intro p _
    rw [mul_apply, norm_mul]
    exact mul_le_mul (le_supNorm b p) (le_supNorm h p)
      (norm_nonneg _) (supNorm_nonneg b)
  have hh : HasHolderBound α (cylinder T) (b * h)
      (supNorm (cylinder T) b * holderSeminorm α (cylinder T) h +
        holderSeminorm α (cylinder T) b * supNorm (cylinder T) h) := by
    intro p hp q hq
    calc
      ‖(b * h) p - (b * h) q‖ =
          ‖b p * (h p - h q) + (b p - b q) * h q‖ := by
        simp only [mul_apply]
        congr 1
        ring
      _ ≤ ‖b p * (h p - h q)‖ + ‖(b p - b q) * h q‖ := norm_add_le _ _
      _ = ‖b p‖ * ‖h p - h q‖ + ‖b p - b q‖ * ‖h q‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ supNorm (cylinder T) b *
            (holderSeminorm α (cylinder T) h * parabolicDist p q ^ α) +
          (holderSeminorm α (cylinder T) b * parabolicDist p q ^ α) *
            supNorm (cylinder T) h := by
        apply add_le_add
        · exact mul_le_mul (le_supNorm b p) (hasHolderBound_seminorm h p hp q hq)
            (norm_nonneg _) (supNorm_nonneg b)
        · exact mul_le_mul (hasHolderBound_seminorm b p hp q hq) (le_supNorm h q)
            (norm_nonneg _) (mul_nonneg (holderSeminorm_nonneg b)
              (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
      _ = _ := by ring
  have hn := norm_le_of_bounds (b * h)
    (mul_nonneg (supNorm_nonneg b) (supNorm_nonneg h))
    (add_nonneg (mul_nonneg (supNorm_nonneg b) (holderSeminorm_nonneg h))
      (mul_nonneg (holderSeminorm_nonneg b) (supNorm_nonneg h))) hb hh
  rw [ParabolicHolder.norm_eq h]
  nlinarith only [hn]

end Poincare.ParabolicHolderMultiplier
