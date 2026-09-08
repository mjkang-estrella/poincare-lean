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

end Poincare.FixedChartUniformNormalRadius
