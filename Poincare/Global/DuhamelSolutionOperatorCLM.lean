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
