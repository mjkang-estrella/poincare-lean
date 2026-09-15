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
    0 < boundConstant α hα hα1 ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
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

/-- The operator's value component is the Duhamel integral on the cylinder. -/
theorem duhamelOperator_u (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    ∀ p ∈ cylinder T, (duhamelOperator α T hα hα1 hT hT1 f).u p =
      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2 :=
  (duhamelGraph_spec α T hα hα1 hT hT1 f).1

/-- The operator norms are uniformly bounded for all short positive intervals. -/
theorem duhamelOperator_norm_le :
    ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1), ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
        ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ C := by
  intro α hα hα1
  refine ⟨boundConstant α hα hα1, (boundConstant_spec α hα hα1).1, ?_⟩
  intro T hT hT1
  exact LinearMap.mkContinuous_norm_le _ (boundConstant_spec α hα hα1).1.le _

/-- The graph satisfies the inhomogeneous heat equation, including both endpoints. -/
theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (duhamelOperator α T hα hα1 hT hT1 f).ut (t,x) = f (t,x) +
        ∑ i : Fin 3, (duhamelOperator α T hα hα1 hT hT1 f).ddu (t,x)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  let G := duhamelOperator α T hα hα1 hT hT1 f
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
  have hu (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.u (t,z)) = u t := by
    funext z
    exact duhamelOperator_u α T hα hα1 hT hT1 f (t,z) ⟨ht, mem_univ z⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.du (t,z)) = fderiv ℝ (u t) := by
    funext z
    have h := (G.hasFDeriv t ht z).fderiv
    rw [hu t ht] at h
    exact h.symm
  have hdd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
      G.ddu (t,x) = fderiv ℝ (fderiv ℝ (u t)) x := by
    have h := (G.hasFDeriv_du t ht x).fderiv
    rw [hd t ht] at h
    exact h.symm
  have hf : ContinuousOn f (cylinder T) :=
    continuousOn_of_hasHolderBound hα (hasHolderBound f)
  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ ‖f‖ :=
    fun t _ x => ParabolicHolder.norm_le f (t,x)
  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E,
      |f (t,x)-f (t,y)| ≤ ‖f‖ * ‖x-y‖^α := by
    intro t ht x y
    simpa [parabolicDist, Real.norm_eq_abs] using
      hasHolderBound f (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
  intro t ht x
  change G.ut (t,x) = f (t,x) + ∑ i : Fin 3, G.ddu (t,x) _ _
  rw [hdd t ht x]
  have htime := (MovingLimitLeibniz.duhamel_solves_heat_equation α hα hα1 T hT hT1
    f ‖f‖ ‖f‖ (norm_nonneg f) (norm_nonneg f) hf hfM hfK).2 t ht x
  have htimeG := htime.congr_of_mem (fun s hs => congrFun (hu s hs) x) ht
  exact ((G.hasDeriv_time t ht x).derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (htimeG.derivWithin (uniqueDiffOn_Icc hT t ht))

end Poincare.DuhamelSolutionOperatorCLM
