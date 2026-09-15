import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.ParametrixNeumannCorrection

noncomputable section

namespace Poincare.NearIdentityParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph ParabolicHolderMultiplier
open DuhamelSolutionOperatorCLM

variable {α T : ℝ}

/-- The coefficient forcing is additive in the derivative graph. -/
theorem forcing_add (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (G H : Graph (E := ClosedSmoothModel 3) α T) :
    forcing b (G + H) = forcing b G + forcing b H := by
  apply ParabolicHolder.ext
  intro p _
  change (∑ i, ∑ j, b i j p * (G.ddu p + H.ddu p)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  simp only [ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib,
    ParabolicHolder.add_apply, forcing_apply]

/-- The coefficient forcing respects real scalar multiplication. -/
theorem forcing_smul (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (c : ℝ)
    (G : Graph (E := ClosedSmoothModel 3) α T) :
    forcing b (c • G) = c • forcing b G := by
  apply ParabolicHolder.ext
  intro p _
  change (∑ i, ∑ j, b i j p * (c • G.ddu p)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ParabolicHolder.smul_apply,
    forcing_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A bound valid without restrictions on the cylinder or exponent. -/
theorem forcing_bound (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (G : Graph (E := ClosedSmoothModel 3) α T) :
    ‖forcing b G‖ ≤ (∑ i, ∑ j, ‖b i j‖) * ‖G‖ := by
  rw [forcing_eq_sum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (ParabolicHolder.norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left
      ((norm_entry_le G.ddu _ _ _ _).trans (norm_ddu_le G)) (norm_nonneg _))

/-- The bounded multiplier on genuine derivative graphs. -/
def multiplier (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) :
    Graph (E := ClosedSmoothModel 3) α T →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ :=
  ({ toFun := forcing b
     map_add' := forcing_add b
     map_smul' := forcing_smul b } : Graph (E := ClosedSmoothModel 3) α T →ₗ[ℝ] Y (E := ClosedSmoothModel
         3) α T ℝ).mkContinuous
    (∑ i, ∑ j, ‖b i j‖) (forcing_bound b)

@[simp] theorem multiplier_apply (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (G : Graph (E := ClosedSmoothModel 3) α T) :
    multiplier b G = forcing b G := rfl

/-- The split estimate gives the small short-cylinder operator bound. -/
theorem multiplier_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
    ‖multiplier b‖ ≤ 9 * (ε + Λ * T ^ (α / 2)) := by
  have hε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro G
  simpa only [multiplier_apply, mul_add, add_mul, mul_assoc] using
    norm_forcing_le b G hα hT hb hbα

/-- The landed choice gives a specific uniform solution-operator constant. -/
theorem duhamel_norm_le_boundConstant (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ boundConstant α hα hα1 :=
  LinearMap.mkContinuous_norm_le _ (boundConstant_spec α hα hα1).1.le _

/-- The coefficient perturbation following the constant-coefficient inverse. -/
def errorOp (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ :=
  (multiplier b).comp (duhamelOperator α T hα hα1 hT hT1)

/-- The operator error retains the short-time factor. -/
theorem errorOp_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
    ‖errorOp b hα hα1 hT hT1‖ ≤
      9 * boundConstant α hα hα1 * (ε + Λ * T ^ (α / 2)) := by
  have hε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact norm_error_le b _ hα hT hb hbα
    (duhamel_norm_le_boundConstant hα hα1 hT hT1) f

/-- Two quarter-size contributions bound the error by one half. -/
theorem errorOp_small (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4) :
    ‖errorOp b hα hα1 hT hT1‖ ≤ 1 / 2 ∧ ‖errorOp b hα hα1 hT hT1‖ < 1 := by
  have h := errorOp_norm_le b hα hα1 hT hT1 hb hbα
  constructor <;> nlinarith only [h, hε, hΛ]

/-- Identity plus the Hölder coefficient perturbation. -/
def coeff (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (i j : Fin 3) (p : ℝ ×
    ClosedSmoothModel 3) : ℝ :=
  (if i = j then 1 else 0) + b i j p

/-- Splitting the coefficient sum gives the Laplacian and perturbation forcing. -/
theorem coeff_sum (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (G : Graph (E := ClosedSmoothModel 3) α T) (p : ℝ × ClosedSmoothModel 3) :
    (∑ i, ∑ j, coeff b i j p * G.ddu p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      (∑ i, G.ddu p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)) + forcing b G p := by
  classical
  simp [coeff, add_mul, Finset.sum_add_distrib, ite_mul, forcing_apply]

/-- The inverse of one minus the error solves the corrected forcing equation. -/
theorem neumann_data_eq (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)
    (hR : ‖R‖ < 1) (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
    (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T
        ℝ) f =
      f + R ((↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E :=
          ClosedSmoothModel 3) α T ℝ) f) := by
  have he := congrArg (fun A : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T
      ℝ => A f) (Units.oneSub R hR).val_inv
  change (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel
      3) α T ℝ) f -
    R ((↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3)
        α T ℝ) f) = f at he
  exact sub_eq_iff_eq_add.mp he

/-- The geometric-series estimate gives a factor of two for half-size errors. -/
theorem neumann_norm_le_two (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
    T ℝ) (hR : ‖R‖ < 1)
    (hhalf : ‖R‖ ≤ 1 / 2) :
    ‖(↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
        T ℝ)‖ ≤ 2 := by
  change ‖∑' n : ℕ, R ^ n‖ ≤ 2
  have hs := tsum_geometric_le_of_norm_lt_one R hR
  have h1 : ‖(1 : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
  have hi : (1 - ‖R‖)⁻¹ ≤ (2 : ℝ) :=
    (inv_le_comm₀ (by linarith) (by norm_num)).2 (by norm_num; linarith)
  linarith

/-- Correct the constant-coefficient inverse by the convergent Neumann series. -/
def nearIdentityInverse (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Graph (E :=
        ClosedSmoothModel 3) α T :=
  ParametrixNeumannCorrection.correctedInverse
    (duhamelOperator α T hα hα1 hT hT1) (errorOp b hα hα1 hT hT1) hR

/-- The corrected graph solves the variable-coefficient equation at both endpoints too. -/
theorem nearIdentityInverse_solves (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1) (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : ClosedSmoothModel 3,
      (nearIdentityInverse b hα hα1 hT hT1 hR f).ut (t, x) =
        f (t, x) + ∑ i, ∑ j, coeff b i j (t, x) *
          (nearIdentityInverse b hα hα1 hT hT1 hR f).ddu (t, x)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  let R := errorOp b hα hα1 hT hT1
  let g := (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel
      3) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y (E := ClosedSmoothModel 3) α T ℝ => v (t, x)) (neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    forcing b (duhamelOperator α T hα hα1 hT hT1 g) (t, x) at hg
  change (duhamelOperator α T hα hα1 hT hT1 g).ut (t, x) =
    f (t, x) + ∑ i, ∑ j, coeff b i j (t, x) *
      (duhamelOperator α T hα hα1 hT hT1 g).ddu (t, x)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)
  rw [duhamelOperator_solves α T hα hα1 hT hT1 g t ht x, coeff_sum, hg]
  ring

/-- The corrected solution operator has uniform norm at most twice the heat constant. -/
theorem nearIdentityInverse_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1)
    (hhalf : ‖errorOp b hα hα1 hT hT1‖ ≤ 1 / 2) :
    ‖nearIdentityInverse b hα hα1 hT hT1 hR‖ ≤ 2 * boundConstant α hα hα1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ boundConstant α hα hα1 * 2 :=
      mul_le_mul (duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (neumann_norm_le_two _ hR hhalf)
        (norm_nonneg (↑((Units.oneSub (errorOp b hα hα1 hT hT1) hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T
            ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ))
        (boundConstant_spec α hα hα1).1.le
    _ = _ := mul_comm _ _

/-- Small Hölder perturbations have a zero-trace solution with a uniform graph bound. -/
theorem exists_nearIdentity_solution (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4)
    (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
    ∃ G : Graph (E := ClosedSmoothModel 3) α T,
      (∀ t ∈ Icc 0 T, ∀ x : ClosedSmoothModel 3,
        G.ut (t, x) = f (t, x) +
          ∑ i, ∑ j, coeff b i j (t, x) * G.ddu (t, x)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) ∧
      ‖G‖ ≤ 2 * boundConstant α hα hα1 * ‖f‖ := by
  obtain ⟨hhalf, hR⟩ := errorOp_small b hα hα1 hT hT1 hb hbα hε hΛ
  refine ⟨nearIdentityInverse b hα hα1 hT hT1 hR f,
    nearIdentityInverse_solves b hα hα1 hT hT1 hR f, ?_⟩
  exact ((nearIdentityInverse b hα hα1 hT hT1 hR).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (nearIdentityInverse_norm_le b hα hα1 hT hT1 hR hhalf) (norm_nonneg f))

end Poincare.NearIdentityParabolicRightInverse
