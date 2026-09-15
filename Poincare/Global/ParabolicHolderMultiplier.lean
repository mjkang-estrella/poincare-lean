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

/-- Evaluation commutes with finite sums in the Hölder carrier. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Y («E» := E) α T ℝ)
    (p : ℝ × E) : (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert a s ha ih => simp only [Finset.sum_insert ha, add_apply, ih]

/-- The nine coefficient-Hessian products, constructed as a supported Hölder function. -/
def forcing (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (G : Graph («E» := E) α T) :
    Y («E» := E) α T ℝ := by
  let y : Y («E» := E) α T ℝ := ∑ i, ∑ j,
    b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)
  have he (p : ℝ × E) : y p = ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j) := by
    simp only [y, sum_apply, mul_apply, entry_apply]
  exact ofFunction (fun p => ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j))
    (fun p hp => by dsimp only; rw [← he p]; exact zero_off y hp)
    ⟨‖y‖, fun p _ => by dsimp only; rw [← he p]; exact ParabolicHolder.norm_le y p⟩
    ⟨‖y‖, fun p hp q hq => by
      dsimp only
      rw [← he p, ← he q]
      exact ParabolicHolder.holder_le y hp hq⟩

@[simp] theorem forcing_apply (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (G : Graph («E» := E) α T) (p : ℝ × E) :
    forcing b G p = ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j) := rfl

/-- The function construction agrees with the finite sum in the Hölder space. -/
theorem forcing_eq_sum (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (G : Graph («E» := E) α T) :
    forcing b G = ∑ i, ∑ j,
      b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j) := by
  apply ParabolicHolder.ext
  intro p _
  simp only [forcing_apply, sum_apply, mul_apply, entry_apply]

/-- A coefficient times one Hessian entry has the split short-cylinder bound. -/
theorem norm_mul_ddu_entry_le (b : Y («E» := E) α T ℝ) (G : Graph («E» := E) α T)
    (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
    (hb : supNorm (cylinder T) b ≤ ε)
    (hbα : holderSeminorm α (cylinder T) b ≤ Λ)
    (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖b * entry G.ddu v w hv hw‖ ≤ ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖ := by
  have hε : 0 ≤ ε := (supNorm_nonneg b).trans hb
  have hΛ : 0 ≤ Λ := (holderSeminorm_nonneg b).trans hbα
  have hn := (norm_entry_le G.ddu v w hv hw).trans (norm_ddu_le G)
  have hs := (supNorm_entry_le G.ddu v w hv hw).trans (supNorm_ddu_le G hα hT)
  calc
    ‖b * entry G.ddu v w hv hw‖ ≤
        supNorm (cylinder T) b * ‖entry G.ddu v w hv hw‖ +
          holderSeminorm α (cylinder T) b * supNorm (cylinder T) (entry G.ddu v w hv hw) :=
      norm_mul_split b _
    _ ≤ ε * ‖G‖ + Λ * (T ^ (α / 2) * ‖G‖) :=
      add_le_add (mul_le_mul hb hn (norm_nonneg _) hε)
        (mul_le_mul hbα hs (supNorm_nonneg _) hΛ)
    _ = _ := by ring

/-- Summing the nine entries gives the frozen-coefficient multiplier estimate. -/
theorem norm_forcing_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (G : Graph («E» := E) α T) (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
    ‖forcing b G‖ ≤ 9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖) := by
  rw [forcing_eq_sum]
  calc
    _ ≤ ∑ i, ‖∑ j, b i j * entry G.ddu (e i) (e j)
        (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact norm_mul_ddu_entry_le (b i j) G hα hT (hb i j) (hbα i j)
        (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)
    _ = _ := by simp; ring

/-- Composing the multiplier with a bounded solution map gives an elementwise error bound. -/
theorem norm_error_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hα : 0 < α) (hT : 0 < T) {ε Λ C_S : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hS : ‖S‖ ≤ C_S) (f : Y («E» := E) α T ℝ) :
    ‖forcing b (S f)‖ ≤ 9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ := by
  have hε : 0 ≤ ε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ : 0 ≤ Λ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hpow : 0 ≤ T ^ (α / 2) := Real.rpow_nonneg hT.le _
  have hSf : ‖S f‖ ≤ C_S * ‖f‖ :=
    (S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg f))
  calc
    ‖forcing b (S f)‖ ≤ 9 * (ε * ‖S f‖ + Λ * T ^ (α / 2) * ‖S f‖) :=
      norm_forcing_le b (S f) hα hT hb hbα
    _ = 9 * (ε + Λ * T ^ (α / 2)) * ‖S f‖ := by ring
    _ ≤ 9 * (ε + Λ * T ^ (α / 2)) * (C_S * ‖f‖) :=
      mul_le_mul_of_nonneg_left hSf (by positivity)
    _ = _ := by ring

/-- Two quarter-size contributions give the required one-half error bound. -/
theorem error_small (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hα : 0 < α) (hT : 0 < T) {ε Λ C_S : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hS : ‖S‖ ≤ C_S) (hε : 9 * C_S * ε ≤ 1 / 4)
    (hΛ : 9 * C_S * Λ * T ^ (α / 2) ≤ 1 / 4)
    (f : Y («E» := E) α T ℝ) :
    ‖forcing b (S f)‖ ≤ (1 / 2) * ‖f‖ := by
  apply (norm_error_le b S hα hT hb hbα hS f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  nlinarith only [hε, hΛ]

end Poincare.ParabolicHolderMultiplier
