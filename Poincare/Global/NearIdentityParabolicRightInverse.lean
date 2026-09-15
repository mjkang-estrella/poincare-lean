import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.ParametrixNeumannCorrection

noncomputable section

namespace Poincare.NearIdentityParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph ParabolicHolderMultiplier
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
variable {α T : ℝ}

local notation "Y₀" => Y («E» := E) α T ℝ
local notation "X₀" => Graph («E» := E) α T

/-- The coefficient forcing is additive in the derivative graph. -/
theorem forcing_add (b : Fin 3 → Fin 3 → Y₀) (G H : X₀) :
    forcing b (G + H) = forcing b G + forcing b H := by
  apply ParabolicHolder.ext
  intro p _
  change (∑ i, ∑ j, b i j p * (G.ddu p + H.ddu p) (e i) (e j)) = _
  simp only [ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib,
    ParabolicHolder.add_apply, forcing_apply]

/-- The coefficient forcing respects real scalar multiplication. -/
theorem forcing_smul (b : Fin 3 → Fin 3 → Y₀) (c : ℝ) (G : X₀) :
    forcing b (c • G) = c • forcing b G := by
  apply ParabolicHolder.ext
  intro p _
  change (∑ i, ∑ j, b i j p * (c • G.ddu p) (e i) (e j)) = _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ParabolicHolder.smul_apply,
    forcing_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A bound valid without restrictions on the cylinder or exponent. -/
theorem forcing_bound (b : Fin 3 → Fin 3 → Y₀) (G : X₀) :
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
def multiplier (b : Fin 3 → Fin 3 → Y₀) : X₀ →L[ℝ] Y₀ :=
  ({ toFun := forcing b
     map_add' := forcing_add b
     map_smul' := forcing_smul b } : X₀ →ₗ[ℝ] Y₀).mkContinuous
    (∑ i, ∑ j, ‖b i j‖) (forcing_bound b)

@[simp] theorem multiplier_apply (b : Fin 3 → Fin 3 → Y₀) (G : X₀) :
    multiplier b G = forcing b G := rfl

/-- The split estimate gives the small short-cylinder operator bound. -/
theorem multiplier_norm_le (b : Fin 3 → Fin 3 → Y₀)
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
def errorOp (b : Fin 3 → Fin 3 → Y₀) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) : Y₀ →L[ℝ] Y₀ :=
  (multiplier b).comp (duhamelOperator α T hα hα1 hT hT1)

/-- The operator error retains the short-time factor. -/
theorem errorOp_norm_le (b : Fin 3 → Fin 3 → Y₀)
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
theorem errorOp_small (b : Fin 3 → Fin 3 → Y₀)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4) :
    ‖errorOp b hα hα1 hT hT1‖ ≤ 1 / 2 ∧ ‖errorOp b hα hα1 hT hT1‖ < 1 := by
  have h := errorOp_norm_le b hα hα1 hT hT1 hb hbα
  constructor <;> nlinarith only [h, hε, hΛ]

end Poincare.NearIdentityParabolicRightInverse
