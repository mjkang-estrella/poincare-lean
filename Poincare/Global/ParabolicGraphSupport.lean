import Poincare.Global.ParabolicSolutionGraph
import Mathlib.Analysis.Calculus.FDeriv.Const

/-! Spatial support of a genuine parabolic graph also supports its derivatives. -/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

universe u
namespace Poincare.ParabolicGraphSupport

/-- Value support off a closed set determines all derivative supports at every time. -/
theorem derivatives_zero_off_closed
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α T : ℝ) (G : Poincare.ParabolicSolutionGraph.Graph (E := E) α T)
    (K : Set E) (hK : IsClosed K) (hT : 0 < T)
    (hu : ∀ s ∈ Set.Icc 0 T, ∀ y : E, y ∉ K → G.u (s, y) = 0) :
    ∀ (t : ℝ) (x : E), x ∉ K →
      G.ut (t, x) = 0 ∧ G.du (t, x) = 0 ∧ G.ddu (t, x) = 0 := by
  intro t x hx
  by_cases ht : t ∈ Icc 0 T
  · have hdu (y : E) (hy : y ∉ K) : G.du (t, y) = 0 := by
      have hv : (fun z : E => G.u (t, z)) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
        exact hu t ht z hz
      exact (G.hasFDeriv t ht y).unique
        ((hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hv)
    have hut : G.ut (t, x) = 0 := by
      exact (uniqueDiffOn_Icc hT t ht).eq_deriv (Icc 0 T)
        (G.hasDeriv_time t ht x)
        ((hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)).congr_of_mem
          (fun s hs => hu s hs x hx) ht)
    have hdv : (fun z : E => G.du (t, z)) =ᶠ[𝓝 x]
        (fun _ => (0 : E →L[ℝ] ℝ)) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with z hz
      exact hdu z hz
    exact ⟨hut, hdu x hx, (G.hasFDeriv_du t ht x).unique
      ((hasFDerivAt_const (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq hdv)⟩
  · have hp : (t, x) ∉ Poincare.ParabolicHolder.cylinder T := fun hp => ht hp.1
    exact ⟨Poincare.ParabolicHolder.zero_off G.ut hp,
      Poincare.ParabolicHolder.zero_off G.du hp,
      Poincare.ParabolicHolder.zero_off G.ddu hp⟩

end Poincare.ParabolicGraphSupport
