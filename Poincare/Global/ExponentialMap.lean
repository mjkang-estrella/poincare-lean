import Poincare.Global.ExponentialDomain
import Mathlib.Analysis.ODE.Gronwall

/-!
# Endpoint-controlled Picard-Lindelöf flows

This module exposes the closed-ball endpoint control that is present in
Mathlib's Picard-Lindelöf construction, and packages the corresponding
interval uniqueness statement for solutions that stay in the Picard-Lindelöf
ball.

The fixed-time exponential map is not defined here yet: the report for
`M5-geo-6` records the remaining comparison gap between the chosen PL flow and
the already existing germ-level geodesic API.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace IsPicardLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
variable {x₀ : E} {a r L K : ℝ≥0}

/--
Picard-Lindelöf local flow with the closed-ball invariant exposed.

Mathlib's public local-flow theorem returns the initial value and the
`HasDerivWithinAt` property on `Icc`.  This strengthening rebuilds the same
chosen fixed points in `ODE.FunSpace` and also returns the invariant
`α x t ∈ closedBall x₀ a` on the whole closed interval.
-/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    [CompleteSpace E] (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r,
      α x t₀ = x ∧
        (∀ t ∈ Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
        ∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a := by
  classical
  have hfixed (x : E) (hx : x ∈ closedBall x₀ r) :
      ∃ α : ODE.FunSpace t₀ x₀ r L, IsFixedPt (ODE.FunSpace.next hf hx) α :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hfixed
  let α' : E → ℝ → E :=
    fun x ↦ if hx : x ∈ closedBall x₀ r then (α x hx).compProj else 0
  refine ⟨α', fun x hx ↦ ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show α' x = (α x hx).compProj by
      dsimp [α']
      rw [dif_pos hx]]
    rw [ODE.FunSpace.compProj_val, ← hα x hx, ODE.FunSpace.next_apply₀]
  · intro t ht
    rw [show α' x = (α x hx).compProj by
      dsimp [α']
      rw [dif_pos hx],
      ODE.FunSpace.compProj_apply]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      ((α x hx).continuous_compProj.continuousOn)
      (fun _ _ ↦ (α x hx).compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα x hx]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t ht
    rw [show α' x = (α x hx).compProj by
      dsimp [α']
      rw [dif_pos hx]]
    exact (α x hx).compProj_mem_closedBall hf.mul_max_le

/--
Interval uniqueness for two `Icc` solutions that stay in the
Picard-Lindelöf closed ball.

This is the Grönwall uniqueness theorem specialized to the PL Lipschitz ball.
The initial time may lie anywhere in the closed interval, so the proof applies
the one-sided uniqueness theorem separately to the left and right of `t₀`.
-/
theorem eqOn_Icc_of_mem_closedBall
    (hf : IsPicardLindelof f t₀ x₀ a r L K)
    {α β : ℝ → E}
    (hα : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hαmem : ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a)
    (hβ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt β (f t (β t)) (Icc tmin tmax) t)
    (hβmem : ∀ t ∈ Icc tmin tmax, β t ∈ closedBall x₀ a)
    (h₀ : α t₀ = β t₀) :
    EqOn α β (Icc tmin tmax) := by
  have hαcont : ContinuousOn α (Icc tmin tmax) :=
    HasDerivWithinAt.continuousOn hα
  have hβcont : ContinuousOn β (Icc tmin tmax) :=
    HasDerivWithinAt.continuousOn hβ
  have hright : EqOn α β (Icc (t₀ : ℝ) tmax) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := f) (s := fun _ ↦ closedBall x₀ a) (K := K)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ h₀
    · intro t ht
      exact hf.lipschitzOnWith t ⟨t₀.2.1.trans ht.1, le_of_lt ht.2⟩
    · exact hαcont.mono fun t ht ↦ ⟨t₀.2.1.trans ht.1, ht.2⟩
    · intro t ht
      have htfull : t ∈ Icc tmin tmax :=
        ⟨t₀.2.1.trans ht.1, le_of_lt ht.2⟩
      exact (hα t htfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨htfull.1, ht.2⟩)
    · intro t ht
      exact hαmem t ⟨t₀.2.1.trans ht.1, le_of_lt ht.2⟩
    · exact hβcont.mono fun t ht ↦ ⟨t₀.2.1.trans ht.1, ht.2⟩
    · intro t ht
      have htfull : t ∈ Icc tmin tmax :=
        ⟨t₀.2.1.trans ht.1, le_of_lt ht.2⟩
      exact (hβ t htfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨htfull.1, ht.2⟩)
    · intro t ht
      exact hβmem t ⟨t₀.2.1.trans ht.1, le_of_lt ht.2⟩
  have hleft : EqOn α β (Icc tmin (t₀ : ℝ)) := by
    refine ODE_solution_unique_of_mem_Icc_left
      (v := f) (s := fun _ ↦ closedBall x₀ a) (K := K)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ h₀
    · intro t ht
      exact hf.lipschitzOnWith t ⟨le_of_lt ht.1, ht.2.trans t₀.2.2⟩
    · exact hαcont.mono fun t ht ↦ ⟨ht.1, ht.2.trans t₀.2.2⟩
    · intro t ht
      have htfull : t ∈ Icc tmin tmax :=
        ⟨le_of_lt ht.1, ht.2.trans t₀.2.2⟩
      exact (hα t htfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, htfull.2⟩)
    · intro t ht
      exact hαmem t ⟨le_of_lt ht.1, ht.2.trans t₀.2.2⟩
    · exact hβcont.mono fun t ht ↦ ⟨ht.1, ht.2.trans t₀.2.2⟩
    · intro t ht
      have htfull : t ∈ Icc tmin tmax :=
        ⟨le_of_lt ht.1, ht.2.trans t₀.2.2⟩
      exact (hβ t htfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, htfull.2⟩)
    · intro t ht
      exact hβmem t ⟨le_of_lt ht.1, ht.2.trans t₀.2.2⟩
  intro t ht
  by_cases ht₀ : t ≤ (t₀ : ℝ)
  · exact hleft ⟨ht.1, ht₀⟩
  · exact hright ⟨le_of_not_ge ht₀, ht.2⟩

end IsPicardLindelof

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Uniform local geodesic chart flow with closed-ball endpoint control.

The center is the first-order chart state `(extChartAt I x₀ x₀, 0)`.  For all
sufficiently small initial chart velocities, the chosen PL flow solves the
autonomous geodesic system on `Icc (-ε) ε` and remains in one common PL closed
ball for every time in that closed interval.
-/
theorem exists_uniform_local_geodesic_chart_flow_with_mem_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E, ∀ v₀ : E, ‖v₀‖ < δ →
        α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
          (∀ t ∈ Icc (-ε) ε,
            HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
              (geodesicFlowField (chartChristoffelField g x₀)
                (α (extChartAt I x₀ x₀, v₀) t))
              (Icc (-ε) ε) t) ∧
          ∀ t ∈ Icc (-ε) ε,
            α (extChartAt I x₀ x₀, v₀) t ∈
              closedBall (extChartAt I x₀ x₀, (0 : E)) a := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  have hflow :
      ContDiffAt ℝ 1
        (geodesicFlowField (chartChristoffelField g x₀)) p₀ := by
    simpa [p₀] using
      (geodesicFlowField_chartChristoffelField_contDiffAt
        (g := g) (x₀ := x₀) (v₀ := (0 : E)))
  rcases IsPicardLindelof.of_contDiffAt_one hflow with
    ⟨ε, hε, a, r, L, K, hr, hpl⟩
  rcases
      (hpl (0 : ℝ)).exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨α, hα⟩
  refine ⟨(r : ℝ), by exact_mod_cast hr, ε, hε, a, α, fun v₀ hv₀ ↦ ?_⟩
  have hp :
      (extChartAt I x₀ x₀, v₀) ∈ closedBall p₀ r := by
    rw [Metric.mem_closedBall]
    change dist (extChartAt I x₀ x₀, v₀) (extChartAt I x₀ x₀, (0 : E)) ≤ (r : ℝ)
    rw [dist_prod_same_left]
    simpa [dist_eq_norm] using le_of_lt hv₀
  have hspec := hα (extChartAt I x₀ x₀, v₀) hp
  refine ⟨?_, ?_, ?_⟩
  · simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.1
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.2.1 t ht'
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.2.2 t ht'

end GeodesicTransport
end Poincare
