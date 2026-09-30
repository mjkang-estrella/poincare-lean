import Poincare.Global.DeTurckCoupledForcingDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open scoped BigOperators Manifold

universe u
namespace Poincare.DeTurckCoupledForcing
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

variable {α T : ℝ}

/-- Sum the actual scalar graph actions over every ordered input tensor slot. -/
private def coupledLinearMap (c0 : Coeff0 α T) (c1 : Coeff1 α T) :
    Inputs α T →ₗ[ℝ] ParabolicHolder.Y (E := E) α T ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (ParabolicCutoffCommutator.firstOrderLinearMap
      (fun p => c1 p a b) (c0 a b)).comp (LinearMap.proj (a,b))

private theorem coupledLinearMap_apply (c0 : Coeff0 α T) (c1 : Coeff1 α T)
    (W : Inputs α T) (q : ℝ × E) :
    coupledLinearMap c0 c1 W q = value c0 c1 W q := by
  simp only [coupledLinearMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, ParabolicHolderMultiplier.sum_apply,
    ParabolicCutoffCommutator.firstOrderLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk,
    ParabolicCutoffCommutator.firstOrderForcing_apply, value]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact add_comm _ _

/-- The original Pi maximum controls each original Graph norm. -/
private theorem coupledLinearMap_bound (c0 : Coeff0 α T) (c1 : Coeff1 α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (W : Inputs α T) :
    ‖coupledLinearMap c0 c1 W‖ ≤ timeBound c0 c1 * ‖W‖ := by
  change ‖∑ a : Fin 3, ∑ b : Fin 3,
    ParabolicCutoffCommutator.firstOrderForcing
      (fun p => c1 p a b) (c0 a b) (W (a,b))‖ ≤ _
  calc
    _ ≤ ∑ a : Fin 3, ‖∑ b : Fin 3,
        ParabolicCutoffCommutator.firstOrderForcing
          (fun p => c1 p a b) (c0 a b) (W (a,b))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        ‖ParabolicCutoffCommutator.firstOrderForcing
          (fun p => c1 p a b) (c0 a b) (W (a,b))‖ := by
      apply Finset.sum_le_sum
      intro a _
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        24 * ((∑ p : Fin 3, ‖c1 p a b‖) * T ^ ((1 - α) / 2) +
          ‖c0 a b‖ * T ^ (1 - α / 2)) * ‖W‖ := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact (ParabolicCutoffCommutator.firstOrder_time_bound
        (fun p => c1 p a b) (c0 a b) (W (a,b)) hα hα1 hT hT1).trans
          (mul_le_mul_of_nonneg_left (norm_le_pi_norm W (a,b)) (by positivity))
    _ = _ := by
      simp only [timeBound, mul_add, add_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]

open DeTurckTensorBasis

/-- Expand a genuine spatial covector without changing its operator norm. -/
private theorem smulRight_expansion (f : E →L[ℝ] ℝ) (a b : Fin 3) :
    f.smulRight (tensor a b) =
      ∑ p : Fin 3, f (basis3 p) • firstJet p a b := by
  ext r v w
  have hr : (∑ p : Fin 3, r p • basis3 p) = r :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr r
  calc
    f r * tensor a b v w =
      f (∑ p : Fin 3, r p • basis3 p) * tensor a b v w := by rw [hr]
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
        firstJet, ContinuousLinearMap.smulRight_apply]
      apply Finset.sum_congr rfl
      intro p _
      change r p * f (basis3 p) * tensor a b v w =
        f (basis3 p) * (r p * tensor a b v w)
      ring

private theorem tensorJet_expansion {α T : ℝ} (W : Inputs α T) (q : ℝ × E) :
    tensorJet W q = ∑ a : Fin 3, ∑ b : Fin 3, ∑ p : Fin 3,
      (W (a,b)).du q (basis3 p) • firstJet p a b := by
  unfold tensorJet
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact smulRight_expansion _ a b

/-- All ordered coefficient entries recover the whole zero/first-order action. -/
private theorem coefficient_action {α T : ℝ} (c0 : Coeff0 α T) (c1 : Coeff1 α T)
    (W : Inputs α T) (q : ℝ × E) (η : ℝ)
    (L0 : Bilin →L[ℝ] Bilin) (L1 : Jet1 →L[ℝ] Bilin) (c d : Fin 3)
    (h0 : ∀ a b, c0 a b q = η *
      DeTurckInverseEntryDerivative.entryCLM c d (L0 (tensor a b)))
    (h1 : ∀ p a b, c1 p a b q = η *
      DeTurckInverseEntryDerivative.entryCLM c d (L1 (firstJet p a b))) :
    value c0 c1 W q = η * DeTurckInverseEntryDerivative.entryCLM c d
      (L0 (tensorValue W q) + L1 (tensorJet W q)) := by
  rw [tensorJet_expansion]
  simp only [value, tensorValue, map_add, map_sum, map_smul, smul_eq_mul]
  simp_rw [h0, h1, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- Construct the positive lower DeTurck action from its actual compact carrier row,
with the original nine-input Graph norm and both interpolation time powers. -/
theorem exists_actual_coupled_forcing :
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
[ChartedSpace Poincare.DeTurckPrincipalSecondJet.E M]
[IsManifold (Poincare.closedSmoothModelWithCorners 3) ((⊤ : ENat) : WithTop ENat) M]
(g0 bg : Poincare.ClosedSmoothRiemannianMetric 3 M) (anchor : M)
(η : Poincare.DeTurckPrincipalSecondJet.E → ℝ) (c d : Fin 3) (α T : ℝ)
(c0 : Poincare.DeTurckCoupledForcing.Coeff0 α T) (c1 : Poincare.DeTurckCoupledForcing.Coeff1 α T),
0 < α → α < 1 → 0 < T → T ≤ 1 →
(∀ a b : Fin 3, ∀ q ∈ Poincare.ParabolicHolder.cylinder T, c0 a b q = η q.2 * Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d q.2) →
(∀ p a b : Fin 3, ∀ q ∈ Poincare.ParabolicHolder.cylinder T, c1 p a b q = η q.2 * Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d q.2) →
∃ K : Poincare.DeTurckCoupledForcing.Inputs α T →L[ℝ] (Poincare.ParabolicHolder.Y (E := Poincare.DeTurckPrincipalSecondJet.E) α T ℝ),
 (∀ W q, (K W) q = Poincare.DeTurckCoupledForcing.value c0 c1 W q) ∧
 ‖K‖ ≤ Poincare.DeTurckCoupledForcing.timeBound c0 c1 ∧
 ∀ W q, q ∈ Poincare.ParabolicHolder.cylinder T →
 (K W) q = η q.2 * Poincare.DeTurckInverseEntryDerivative.entryCLM c d
  (Poincare.DeTurckCompactCoefficients.field0 g0 bg anchor q.2 (Poincare.DeTurckCoupledForcing.tensorValue W q) +
   Poincare.DeTurckCompactCoefficients.field1 g0 bg anchor q.2 (Poincare.DeTurckCoupledForcing.tensorJet W q)) := by
  intro M _ _ _ _ g0 bg anchor η c d α T c0 c1 hα hα1 hT hT1 h0 h1
  let K := (coupledLinearMap c0 c1).mkContinuous (timeBound c0 c1)
    (coupledLinearMap_bound c0 c1 hα hα1 hT hT1)
  have hvalue : ∀ W q, K W q = value c0 c1 W q :=
    coupledLinearMap_apply c0 c1
  refine ⟨K, hvalue, ?_, ?_⟩
  · exact ContinuousLinearMap.opNorm_le_bound K (by unfold timeBound; positivity)
      (coupledLinearMap_bound c0 c1 hα hα1 hT hT1)
  · intro W q hq
    rw [hvalue]
    exact coefficient_action c0 c1 W q (η q.2)
      (DeTurckCompactCoefficients.field0 g0 bg anchor q.2)
      (DeTurckCompactCoefficients.field1 g0 bg anchor q.2) c d
      (fun a b => h0 a b q hq) (fun p a b => h1 p a b q hq)

end Poincare.DeTurckCoupledForcing
