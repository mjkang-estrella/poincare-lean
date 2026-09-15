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

end Poincare.DuhamelSolutionOperatorCLM
