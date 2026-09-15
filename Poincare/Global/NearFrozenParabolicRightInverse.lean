import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := (ClosedSmoothModel 3)) α T ℝ →ₗ[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
    Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3)) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  (graphPullback hα.le hT (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
    (hS : ∀ v w : (ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : (ClosedSmoothModel 3), A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
      H.ddu (t, S.symm x) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ))
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := (ClosedSmoothModel 3)) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
      (P g).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
              (S f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T,
      (∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3), G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) * G.ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse
