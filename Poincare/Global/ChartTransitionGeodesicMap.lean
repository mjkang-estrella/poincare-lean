import Poincare.Global.FTransitionGeodesicMap
import Poincare.Global.TransitionLawFires

/-!
# Chart transitions map local geodesic solutions

The signed Christoffel transition law already proved for preferred manifold
charts is exactly the hypothesis of `FTransitionGeodesicMap`.  This module
packages that observation for an arbitrary local chart-geodesic solution.
Unlike the older re-anchor lemmas, no chosen radial geodesic or shifted time is
built into the statement.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

/-- A fixed neighborhood of the limiting point is still a neighborhood of
all sufficiently close points.  This small topology lemma turns the static
cutoff/overlap germs at an initial state into the nested eventual hypotheses
used by the chart-transition theorem below. -/
theorem eventually_mem_nhds_of_tendsto
    {X : Type*} [TopologicalSpace X] {f : ℝ → X} {x : X} {s : Set X}
    (hf : Tendsto f (nhds (0 : ℝ)) (nhds x)) (hs : s ∈ nhds x) :
    ∀ᶠ t in nhds (0 : ℝ), s ∈ nhds (f t) := by
  rcases mem_nhds_iff.mp hs with ⟨u, hus, hu, hxu⟩
  filter_upwards [hf.eventually (hu.mem_nhds hxu)] with t htu
  exact mem_of_superset (hu.mem_nhds htu) hus

/-- Pointwise form of preferred-chart geodesic transport.  Neighborhood
side conditions at the current position give both the `C²` chart transition
and its signed Christoffel law, hence the transported state satisfies the
target chart-geodesic ODE at the same time. -/
theorem chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ y₀ : M)
    {gamma : ℝ → E × E} {t : ℝ}
    (hgamma : HasDerivAt gamma
      (geodesicFlowField (chartChristoffelField g x₀) (gamma t)) t)
    (hx_chart : ∀ᶠ q in nhds (gamma t).1,
      q ∈ (extChartAt I x₀).target)
    (hy_chart : ∀ᶠ q in nhds (gamma t).1,
      (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hchi_x_chart : ∀ᶠ q in nhds (gamma t).1,
      cutoff (n := 3) x₀ q = 1)
    (hchi_y_chart : ∀ᶠ q in nhds (gamma t).1,
      cutoff (n := 3) y₀ (chartTransition x₀ y₀ q) = 1) :
    HasDerivAt (chartTransitionState x₀ y₀ gamma)
      (geodesicFlowField (chartChristoffelField g y₀)
        (chartTransitionState x₀ y₀ gamma t)) t := by
  let F : E → E := chartTransition (n := 3) x₀ y₀
  have hz : (gamma t).1 ∈ (extChartAt I x₀).target :=
    mem_of_mem_nhds hx_chart
  have hy :
      (extChartAt I x₀).symm (gamma t).1 ∈ (extChartAt I y₀).source :=
    mem_of_mem_nhds
      (x := (gamma t).1)
      (s := {q : E | (extChartAt I x₀).symm q ∈
        (extChartAt I y₀).source}) hy_chart
  have hy' :
      (extChartAt I x₀).symm (gamma t).1 ∈ (chartAt E y₀).source := by
    rwa [extChartAt_source] at hy
  have houter :
      ContMDiffAt I (modelWithCornersSelf ℝ E) 2 (extChartAt I y₀)
        ((extChartAt I x₀).symm (gamma t).1) :=
    contMDiffAt_extChartAt' hy'
  have hinnerWithin :
      ContMDiffWithinAt (modelWithCornersSelf ℝ E) I 2
        ((extChartAt I x₀).symm) (range I) (gamma t).1 :=
    contMDiffWithinAt_extChartAt_symm_range x₀ hz
  have hinner :
      ContMDiffAt (modelWithCornersSelf ℝ E) I 2
        ((extChartAt I x₀).symm) (gamma t).1 := by
    simpa [ModelWithCorners.range_eq_univ] using hinnerWithin
  have hcomp :
      ContMDiffAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ E) 2
        (fun q : E => extChartAt I y₀ ((extChartAt I x₀).symm q))
        (gamma t).1 := by
    simpa [Function.comp_def] using houter.comp (gamma t).1 hinner
  have hF2 : ContDiffAt ℝ 2 F (gamma t).1 :=
    contMDiffAt_iff_contDiffAt.mp
      (by simpa [F, chartTransition] using hcomp)
  have hGamma :=
    chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
      (g := g) (x₀ := x₀) (y₀ := y₀) (z := (gamma t).1)
      hx_chart hy_chart hchi_x_chart hchi_y_chart (gamma t).2 (gamma t).2
  have htransition :
      chartChristoffelField g y₀ (F (gamma t).1)
          ((fderiv ℝ F (gamma t).1) (gamma t).2)
          ((fderiv ℝ F (gamma t).1) (gamma t).2) =
        (fderiv ℝ F (gamma t).1)
            (chartChristoffelField g x₀ (gamma t).1
              (gamma t).2 (gamma t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
            (gamma t).2) (gamma t).2 := by
    simpa [F, chartTransitionDeriv] using hGamma
  have hmapped :=
    FTransitionGeodesicMap.mappedState_hasDerivAt_of_F_transition
      F (chartChristoffelField g x₀) (chartChristoffelField g y₀)
      hgamma hF2 htransition
  simpa [F, FTransitionGeodesicMap.mappedState, chartTransitionState,
    chartTransitionDeriv] using hmapped

/--
On a cutoff-one chart overlap, applying the preferred chart transition to an
arbitrary source geodesic state produces a target-chart geodesic state.

The neighborhood-valued hypotheses are the precise local side conditions of
the already established Christoffel transition theorem.  They are convenient
for later use with openness and continuity along a solution germ.
-/
theorem chartTransitionState_eventually_solves_of_eventually_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ y₀ : M)
    {γ : ℝ → E × E}
    (hγ : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hx_chart : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᶠ q in nhds (γ t).1, q ∈ (extChartAt I x₀).target)
    (hy_chart : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᶠ q in nhds (γ t).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hχx_chart : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᶠ q in nhds (γ t).1, cutoff (n := 3) x₀ q = 1)
    (hχy_chart : ∀ᶠ t in nhds (0 : ℝ),
      ∀ᶠ q in nhds (γ t).1,
        cutoff (n := 3) y₀ (chartTransition x₀ y₀ q) = 1) :
    ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt (chartTransitionState x₀ y₀ γ)
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀ γ t)) t := by
  let F : E → E := chartTransition (n := 3) x₀ y₀
  have hF₂ : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 2 F (γ t).1 := by
    filter_upwards [hx_chart, hy_chart] with t hxt hyt
    have hz : (γ t).1 ∈ (extChartAt I x₀).target :=
      mem_of_mem_nhds hxt
    have hy :
        (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source :=
      mem_of_mem_nhds
        (x := (γ t).1)
        (s := {q : E | (extChartAt I x₀).symm q ∈
          (extChartAt I y₀).source}) hyt
    have hy' :
        (extChartAt I x₀).symm (γ t).1 ∈ (chartAt E y₀).source := by
      rwa [extChartAt_source] at hy
    have houter :
        ContMDiffAt I (modelWithCornersSelf ℝ E) 2 (extChartAt I y₀)
          ((extChartAt I x₀).symm (γ t).1) :=
      contMDiffAt_extChartAt' hy'
    have hinnerWithin :
        ContMDiffWithinAt (modelWithCornersSelf ℝ E) I 2
          ((extChartAt I x₀).symm) (range I) (γ t).1 :=
      contMDiffWithinAt_extChartAt_symm_range x₀ hz
    have hinner :
        ContMDiffAt (modelWithCornersSelf ℝ E) I 2
          ((extChartAt I x₀).symm) (γ t).1 := by
      simpa [ModelWithCorners.range_eq_univ] using hinnerWithin
    have hcomp :
        ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) 2
          (fun q : E => extChartAt I y₀ ((extChartAt I x₀).symm q))
          (γ t).1 := by
      simpa [Function.comp_def] using houter.comp (γ t).1 hinner
    exact contMDiffAt_iff_contDiffAt.mp
      (by simpa [F, chartTransition] using hcomp)
  have htransition : ∀ᶠ t in nhds (0 : ℝ),
      chartChristoffelField g y₀ (F (γ t).1)
          ((fderiv ℝ F (γ t).1) (γ t).2)
          ((fderiv ℝ F (γ t).1) (γ t).2) =
        (fderiv ℝ F (γ t).1)
            (chartChristoffelField g x₀ (γ t).1 (γ t).2 (γ t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (γ t).1)
            (γ t).2) (γ t).2 := by
    filter_upwards [hx_chart, hy_chart, hχx_chart, hχy_chart] with
      t hxt hyt hχxt hχyt
    have hΓ :=
      chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
        (g := g) (x₀ := x₀) (y₀ := y₀) (z := (γ t).1)
        hxt hyt hχxt hχyt (γ t).2 (γ t).2
    simpa [F, chartTransitionDeriv] using hΓ
  have hmapped :=
    FTransitionGeodesicMap.mappedState_eventually_solves_of_F_transition
      F (chartChristoffelField g x₀) (chartChristoffelField g y₀)
      hγ hF₂ htransition
  simpa [F, FTransitionGeodesicMap.mappedState, chartTransitionState,
    chartTransitionDeriv] using hmapped

/-- Static initial-point neighborhoods are enough to invoke the nested
eventual chart-transition theorem. -/
theorem chartTransitionState_eventually_solves_of_initial_nhds
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ y₀ : M)
    {γ : ℝ → E × E} {z : E}
    (hγ : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hpos : Tendsto (fun t : ℝ => (γ t).1) (nhds 0) (nhds z))
    (hx_chart : (extChartAt I x₀).target ∈ nhds z)
    (hy_chart :
      {q : E | (extChartAt I x₀).symm q ∈
        (extChartAt I y₀).source} ∈ nhds z)
    (hχx_chart : {q : E | cutoff (n := 3) x₀ q = 1} ∈ nhds z)
    (hχy_chart :
      {q : E | cutoff (n := 3) y₀ (chartTransition x₀ y₀ q) = 1} ∈
        nhds z) :
    ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt (chartTransitionState x₀ y₀ γ)
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀ γ t)) t := by
  apply chartTransitionState_eventually_solves_of_eventually_cutoff_eq_one
    g x₀ y₀ hγ
  · exact eventually_mem_nhds_of_tendsto hpos hx_chart
  · exact eventually_mem_nhds_of_tendsto hpos hy_chart
  · exact eventually_mem_nhds_of_tendsto hpos hχx_chart
  · exact eventually_mem_nhds_of_tendsto hpos hχy_chart

end GeodesicTransport
end Poincare
