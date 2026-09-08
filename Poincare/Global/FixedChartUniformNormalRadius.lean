import Poincare.Global.GeodesicFlowJointDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Uniform normal neighborhoods for one fixed-chart flow

The exponential here is the position endpoint of the supplied joint flow.
It makes no identification with any separately selected per-anchor exponential.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology ContDiff NNReal

namespace Poincare.FixedChartUniformNormalRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The position endpoint at the common time. -/
def expChart (α : (E × E) → ℝ → E × E) (T : ℝ) (z v : E) : E :=
  (α (z, v) T).1

/-- The joint anchor and endpoint map. -/
def F (α : (E × E) → ℝ → E × E) (T : ℝ) (p : E × E) : E × E :=
  (p.1, expChart α T p.1 p.2)

/-- The free-motion fundamental solution, including both initial directions. -/
def freeVariation (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ((ContinuousLinearMap.fst ℝ E E) + t • (ContinuousLinearMap.snd ℝ E E)).prod
    (ContinuousLinearMap.snd ℝ E E)

/-- The derivative of the joint anchor and endpoint map. -/
def endpointDerivative (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E).prod
    ((ContinuousLinearMap.fst ℝ E E) + t • (ContinuousLinearMap.snd ℝ E E))

/-- A zero-velocity trajectory is stationary on the entire common interval. -/
theorem flow_zero_velocity [FiniteDimensional ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ))
    {γ : ℝ → E × E} {z : E} {T : ℝ} (hT : 0 < T)
    (h0 : γ 0 = (z, 0))
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt γ
      (geodesicFlowField Γ (γ t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, γ t = (z, 0) := by
  have hc := HasDerivWithinAt.continuousOn hd
  obtain ⟨a, ha⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_closedBall (z, 0)
  have hm : ∀ t ∈ Icc (-T) T, γ t ∈ closedBall (z, 0) a :=
    fun t ht => ha (mem_image_of_mem γ ht)
  have hz := hm 0 (by constructor <;> linarith)
  rw [h0] at hz
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (z, 0) a) (isCompact_closedBall (z, 0) a)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicFlowField Γ)
    (s := fun _ => closedBall (z, 0) a) (fun _ _ => hK)
    (by constructor <;> linarith) hc
    (fun t ht => (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hm t (Ioo_subset_Icc_self ht)) continuousOn_const
    (fun t _ => by simpa [geodesicFlowField] using hasDerivAt_const t (z, (0 : E)))
    (fun _ _ => hz) h0

/-- At zero velocity the linearized field sends `(u,w)` to `(w,0)`. -/
theorem linearized_zero_velocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z) (p : E × E) :
    linearizedGeodesicFlowOperator Γ (z, 0) p = (p.2, 0) := by
  rw [linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator hΓ]
  simp [coordinateJacobiAcceleration]

/-- The entire fundamental solution at zero velocity is free motion. -/
theorem fundamentalSolution_zero_velocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z)
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)} {T : ℝ} (hT : 0 < T)
    (h0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator Γ (z, 0)).comp (Φ t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, Φ t = freeVariation t := by
  intro t ht
  apply ContinuousLinearMap.ext
  intro p
  let A := linearizedGeodesicFlowOperator Γ (z, 0)
  have hlin : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun u => Φ u p)
      (A (Φ s p)) (Icc (-T) T) s := by
    intro s hs
    simpa [A] using (hd s hs).clm_apply (hasDerivWithinAt_const s (Icc (-T) T) p)
  have hexpl : ∀ s : ℝ, HasDerivAt (fun u => freeVariation u p)
      (A (freeVariation s p)) s := by
    intro s
    simpa [freeVariation, A, linearized_zero_velocity hΓ] using
      ((hasDerivAt_const s p.1).add ((hasDerivAt_id s).smul_const p.2)).prodMk
        (hasDerivAt_const s p.2)
  have heq := ODE_solution_unique_of_mem_Icc
    (v := fun _ => A) (s := fun _ => univ)
    (fun _ _ => A.lipschitz.lipschitzOnWith)
    (by constructor <;> linarith : (0 : ℝ) ∈ Ioo (-T) T)
    (HasDerivWithinAt.continuousOn hlin)
    (fun s hs => (hlin s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (fun _ _ => mem_univ _) (fun s _ => (hexpl s).continuousAt.continuousWithinAt)
    (fun s _ => hexpl s) (fun _ _ => mem_univ _)
    (by simp [h0, freeVariation])
  exact heq ht

/-- The endpoint derivative is invertible at every positive common time. -/
def endpointEquiv (T : ℝ) (hT : T ≠ 0) : (E × E) ≃L[ℝ] (E × E) where
  toLinearEquiv :=
    { toLinearMap := (endpointDerivative T).toLinearMap
      invFun := fun p => (p.1, T⁻¹ • (p.2 - p.1))
      left_inv := by
        intro p
        simp [endpointDerivative, smul_smul, hT]
      right_inv := by
        intro p
        simp [endpointDerivative, smul_smul, hT] }
  continuous_toFun := (endpointDerivative T).continuous
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub continuous_fst).const_smul T⁻¹)

section Flow

variable [FiniteDimensional ℝ E]
variable {Γ : E → E →L[ℝ] E →L[ℝ] E}
variable {α : (E × E) → ℝ → E × E}
variable {Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E)}
variable {c z : E} {r T : ℝ}
variable (hΓ : ContDiff ℝ 1 Γ) (hT : 0 < T)
variable (hα : ∀ q ∈ ball (c, (0 : E)) r, α q 0 = q ∧
  ∀ t ∈ Icc (-T) T, HasDerivWithinAt (α q)
    (geodesicFlowField Γ (α q t)) (Icc (-T) T) t)
variable (hΦ0 : ∀ q ∈ ball (c, (0 : E)) r, Φ q 0 = ContinuousLinearMap.id ℝ _)
variable (hΦ : ∀ q ∈ ball (c, (0 : E)) r, ∀ t ∈ Icc (-T) T,
  HasDerivWithinAt (Φ q)
    ((linearizedGeodesicFlowOperator Γ (α q t)).comp (Φ q t)) (Icc (-T) T) t)
variable (hf : ∀ q ∈ ball (c, (0 : E)) r,
  HasFDerivAt (fun y => α y T) (Φ q T) q)

include hΓ hT hα hΦ0 hΦ

/-- The supplied joint flow has the explicit zero-velocity fundamental solution. -/
theorem flow_fundamentalSolution_zero_velocity (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    ∀ t ∈ Icc (-T) T, Φ (z, 0) t = freeVariation t := by
  have hs := flow_zero_velocity (contDiff_geodesicFlowField hΓ) hT
    (hα (z, 0) hz).1 (hα (z, 0) hz).2
  apply fundamentalSolution_zero_velocity (hΓ.differentiable one_ne_zero z) hT (hΦ0 _ hz)
  intro t ht
  simpa only [hs t ht] using hΦ (z, 0) hz t ht

include hf

/-- The full anchor/endpoint derivative is the triangular isomorphism. -/
theorem hasFDerivAt_F_at_zero_velocity (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    HasFDerivAt (F α T) (endpointDerivative T) (z, 0) := by
  have heq := flow_fundamentalSolution_zero_velocity hΓ hT hα hΦ0 hΦ hz T
    (by constructor <;> linarith)
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.prodMk (hf (z, 0) hz).fst
  rw [heq] at hd
  convert hd using 1

/-- Joint C1 regularity upgrades this derivative to a strict derivative. -/
theorem hasStrictFDerivAt_F
    (hC1 : ContDiffOn ℝ 1 (fun q => α q T) (ball (c, (0 : E)) r))
    (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    HasStrictFDerivAt (F α T) (endpointDerivative T) (z, 0) := by
  have hc := hC1.contDiffAt (isOpen_ball.mem_nhds hz)
  exact (contDiffAt_fst.prodMk hc.fst).hasStrictFDerivAt'
    (hasFDerivAt_F_at_zero_velocity hΓ hT hα hΦ0 hΦ hf hz) one_ne_zero

end Flow

end Poincare.FixedChartUniformNormalRadius
