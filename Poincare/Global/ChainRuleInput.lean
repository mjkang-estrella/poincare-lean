import Poincare.Global.SideConditions

/-!
# Chain-rule input for local re-anchoring

This module supplies the analytic chain-rule input left explicit by
`SideConditions.lean`: along the shifted chart geodesic, the transported
velocity `Dσ(γ₁) γ₂` has derivative
`Dσ(γ₁) γ₂' + D(Dσ)(γ₁)[γ₁'] γ₂`.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

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
Strict local re-anchor law on the cutoff-one overlap, with the velocity
chain-rule input discharged from transition smoothness and the shifted
geodesic ODE.
-/
theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one_unconditional
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ)
    (ht₀ :
      t₀ ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀))
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hx_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        q ∈ (extChartAt I x₀).target)
    (hy_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hχx_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        cutoff (n := n) x₀ q = 1)
    (hχy_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        cutoff (n := n) y₀ (chartTransition x₀ y₀ q) = 1) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀) := by
  let γ : ℝ → E × E :=
    fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
  have hshift :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        t₀ + t ∈
          Ioo (-(geodesicGermRadius g x₀ v₀))
            (geodesicGermRadius g x₀ v₀) := by
    have hI :
        Ioo (-(geodesicGermRadius g x₀ v₀))
            (geodesicGermRadius g x₀ v₀) ∈ 𝓝 t₀ :=
      Ioo_mem_nhds ht₀.1 ht₀.2
    have htend :
        Tendsto (fun t : ℝ => t₀ + t) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
      simpa [Pi.add_apply] using
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => t₀) 0).add
          continuousAt_id).tendsto
    exact htend.eventually hI
  have hchain : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun s : ℝ =>
          chartTransitionDeriv x₀ y₀
            (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).1
            (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).2)
        (chartTransitionDeriv x₀ y₀
          (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1
          (-(chartChristoffelField g x₀
              (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2) +
          (fderiv ℝ (chartTransitionDeriv x₀ y₀)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2)
        t := by
    filter_upwards
      [hshift, by simpa [γ] using hx_chart, by simpa [γ] using hy_chart] with
      t ht hxt hyt
    have hγbase :=
      (geodesicGermChartSolution_spec g x₀ v₀).2.1 (t₀ + t) ht
    have hlin : HasDerivAt (fun s : ℝ => t₀ + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add t₀
    have hγder : HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t := by
      have hcomp := hγbase.scomp t hlin
      simpa [γ] using hcomp
    have hpos : HasDerivAt (fun s : ℝ => (γ s).1) (γ t).2 t :=
      geodesic_position_hasDerivAt hγder
    have hvel : HasDerivAt (fun s : ℝ => (γ s).2)
        (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) t :=
      geodesic_velocity_hasDerivAt hγder
    have hzN : ∀ᶠ q in 𝓝 (γ t).1, q ∈ (extChartAt I x₀).target := by
      simpa [γ, extChartAt_target] using hxt
    have hyN : ∀ᶠ q in 𝓝 (γ t).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source := by
      simpa [γ, extChartAt_source] using hyt
    have hz : (γ t).1 ∈ (extChartAt I x₀).target :=
      mem_of_mem_nhds hzN
    have hy : (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source := by
      exact mem_of_mem_nhds
        (x := (γ t).1)
        (s := {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source})
        hyN
    have hσC2 : ContDiffAt ℝ 2 (chartTransition (n := n) x₀ y₀) (γ t).1 := by
      have hy_chart' :
          (extChartAt I x₀).symm (γ t).1 ∈ (chartAt E y₀).source := by
        rwa [extChartAt_source] at hy
      have houter :
          ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I y₀)
            ((extChartAt I x₀).symm (γ t).1) :=
        contMDiffAt_extChartAt' hy_chart'
      have hinnerWithin :
          ContMDiffWithinAt 𝓘(ℝ, E) I 2 ((extChartAt I x₀).symm)
            (range I) (γ t).1 :=
        contMDiffWithinAt_extChartAt_symm_range x₀ hz
      have hinner :
          ContMDiffAt 𝓘(ℝ, E) I 2 ((extChartAt I x₀).symm) (γ t).1 := by
        simpa [ModelWithCorners.range_eq_univ] using hinnerWithin
      have hcomp :
          ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
            (fun q : E => extChartAt I y₀ ((extChartAt I x₀).symm q))
            (γ t).1 := by
        simpa [Function.comp_def] using houter.comp (γ t).1 hinner
      exact contMDiffAt_iff_contDiffAt.mp
        (by simpa [chartTransition] using hcomp)
    have hDcont : ContDiffAt ℝ 1 (chartTransitionDeriv (n := n) x₀ y₀) (γ t).1 := by
      simpa [chartTransitionDeriv] using
        (hσC2.fderiv_right (m := 1) (by norm_num))
    have hD : HasFDerivAt (chartTransitionDeriv (n := n) x₀ y₀)
        (fderiv ℝ (chartTransitionDeriv x₀ y₀) (γ t).1) (γ t).1 :=
      (hDcont.hasStrictFDerivAt (by norm_num)).hasFDerivAt
    have hDalong : HasDerivAt
        (fun s : ℝ => chartTransitionDeriv x₀ y₀ (γ s).1)
        ((fderiv ℝ (chartTransitionDeriv x₀ y₀) (γ t).1) (γ t).2) t := by
      have hcomp := hD.comp_hasDerivAt t hpos
      simpa [Function.comp_def] using hcomp
    have happly := hDalong.clm_apply hvel
    simpa [γ, add_comm] using happly
  exact
    shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one
      (g := g) (x₀ := x₀) (y₀ := y₀) (v₀ := v₀) (t₀ := t₀)
      ht₀ hy₀ hx_chart hy_chart hχx_chart hχy_chart hchain

end GeodesicTransport
end Poincare
