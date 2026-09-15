import Poincare.Global.DuhamelSolutionOperatorBound

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.ParabolicSolutionGraph

/-- Values determine all derivatives, including at both time endpoints. -/
theorem Graph.ext_of_u {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α T : ℝ} (hT : 0 < T) {G H : Graph (E := E) α T} (hu : G.u = H.u) : G = H := by
  have hd : G.du = H.du := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasFDeriv p.1 hp.1 p.2
    rw [hu] at h
    exact h.unique (H.hasFDeriv p.1 hp.1 p.2)
  have hdd : G.ddu = H.ddu := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasFDeriv_du p.1 hp.1 p.2
    rw [hd] at h
    exact h.unique (H.hasFDeriv_du p.1 hp.1 p.2)
  have ht : G.ut = H.ut := by
    apply ParabolicHolder.ext
    intro p hp
    have h := G.hasDeriv_time p.1 hp.1 p.2
    rw [hu] at h
    exact (h.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)).symm.trans
      ((H.hasDeriv_time p.1 hp.1 p.2).derivWithin (uniqueDiffOn_Icc hT p.1 hp.1))
  cases G
  cases H
  cases hu
  cases ht
  cases hd
  cases hdd
  rfl

end Poincare.ParabolicSolutionGraph

namespace Poincare.DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3

open ParabolicHolder DuhamelSolutionOperatorBound

/-- A short-time bound depending only on the exponent. -/
def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
  Classical.choose (exists_solution_graph_bound α hα hα1)

/-- The chosen constant retains the complete landed existence estimate. -/
theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < boundConstant α hα hα1 ∧ ∀ T : ℝ, ∀ hT : 0 < T, ∀ hT1 : T ≤ 1,
    ∀ f : Y («E» := E) α T ℝ, ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ cylinder T, G.u p =
        ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
      ‖G‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
  Classical.choose_spec (exists_solution_graph_bound α hα hα1)

/-- The unique graph selected by the landed existence theorem. -/
def duhamelGraph (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) : ParabolicSolutionGraph.Graph («E» := E) α T :=
  Classical.choose ((boundConstant_spec α hα hα1).2 T hT hT1 f)

/-- The selected graph has the integral values and the uniform norm estimate. -/
theorem duhamelGraph_spec (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    (∀ p ∈ cylinder T, (duhamelGraph α T hα hα1 hT hT1 f).u p =
      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
    ‖duhamelGraph α T hα hα1 hT hT1 f‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
  Classical.choose_spec ((boundConstant_spec α hα hα1).2 T hT hT1 f)

/-- The Duhamel integral is additive for parabolic Hölder data. -/
theorem duhamel_integral_add {α T t : ℝ} (hα : 0 < α) (ht : t ∈ Icc 0 T)
    (f g : Y («E» := E) α T ℝ) (x : E) :
    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (f+g) (s,y)) x) =
      (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x) +
      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => g (s,y)) x := by
  have hc (v : Y («E» := E) α T ℝ) : ContinuousOn v (cylinder T) :=
    continuousOn_of_hasHolderBound hα (hasHolderBound v)
  have hi (v : Y («E» := E) α T ℝ) :=
    HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht (hc v)
      (fun s _ y => ParabolicHolder.norm_le v (s,y)) x
  rw [← intervalIntegral.integral_add (hi f) (hi g)]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have he (v : Y («E» := E) α T ℝ) :=
    heatKernel_convolutionExistsAt_of_bounded_continuous (sub_pos.mpr hs.2)
      ((hc v).comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩))
      (fun y => ParabolicHolder.norm_le v (s,y)) x
  exact (he f).distrib_add (he g)

/-- Scalar multiplication commutes with the Duhamel integral. -/
theorem duhamel_integral_smul {α T t : ℝ} (c : ℝ)
    (f : Y («E» := E) α T ℝ) (x : E) :
    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (c • f) (s,y)) x) =
      c • ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x := by
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul]
  simp_rw [mul_left_comm (heatKernel _ _) c, integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- Integral linearity and graph uniqueness give a linear solution map. -/
def duhamelLinearMap (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →ₗ[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T where
  toFun := duhamelGraph α T hα hα1 hT hT1
  map_add' f g := by
    apply ParabolicSolutionGraph.Graph.ext_of_u hT
    apply ParabolicHolder.ext
    intro p hp
    change (duhamelGraph α T hα hα1 hT hT1 (f+g)).u p =
      (duhamelGraph α T hα hα1 hT hT1 f).u p +
      (duhamelGraph α T hα hα1 hT hT1 g).u p
    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (f+g)).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 g).1 p hp]
    exact duhamel_integral_add hα hp.1 f g p.2
  map_smul' c f := by
    apply ParabolicSolutionGraph.Graph.ext_of_u hT
    apply ParabolicHolder.ext
    intro p hp
    change (duhamelGraph α T hα hα1 hT hT1 (c • f)).u p =
      c • (duhamelGraph α T hα hα1 hT hT1 f).u p
    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (c • f)).1 p hp,
      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp]
    exact duhamel_integral_smul c f p.2

/-- The bounded constant-coefficient inverse in continuous linear form. -/
def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T :=
  (duhamelLinearMap α T hα hα1 hT hT1).mkContinuous (boundConstant α hα hα1)
    (fun f => (duhamelGraph_spec α T hα hα1 hT hT1 f).2)

end Poincare.DuhamelSolutionOperatorCLM
