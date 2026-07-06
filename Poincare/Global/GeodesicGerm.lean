import Poincare.Global.GeodesicTransport

/-!
# Local geodesic germs from chart geodesic solutions

This file packages the local chart solution supplied by
`Poincare.Global.GeodesicTransport` as a manifold-valued germ at the anchor,
and records same-anchor uniqueness for the chart ODE.
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

/-!
## Same-anchor uniqueness
-/

/--
Two chart geodesic-system solutions with the same anchor chart and initial
velocity agree as germs at `0`.
-/
theorem geodesicFlowField_chartChristoffelField_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E)
    {γ η : ℝ → E × E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀))
    (hη0 : η 0 = (extChartAt I x₀ x₀, v₀))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField (chartChristoffelField g x₀) (η t)) t) :
    γ =ᶠ[𝓝 (0 : ℝ)] η :=
  geodesicFlowField_eventuallyEq_of_contDiffAt
    (Γ := chartChristoffelField g x₀)
    (p₀ := (extChartAt I x₀ x₀, v₀))
    (hΓ := geodesicFlowField_chartChristoffelField_contDiffAt g x₀ v₀)
    hγ0 hη0 hγ hη

/--
The pulled-back manifold curves of two same-anchor chart solutions agree as
germs at `0`.
-/
theorem pulledback_geodesic_eventuallyEq_of_chartChristoffelField
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E)
    {γ η : ℝ → E × E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀))
    (hη0 : η 0 = (extChartAt I x₀ x₀, v₀))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField (chartChristoffelField g x₀) (η t)) t) :
    (fun t : ℝ => (extChartAt I x₀).symm (γ t).1)
      =ᶠ[𝓝 (0 : ℝ)]
    (fun t : ℝ => (extChartAt I x₀).symm (η t).1) := by
  filter_upwards
    [geodesicFlowField_chartChristoffelField_eventuallyEq
      (g := g) (x₀ := x₀) (v₀ := v₀) hγ0 hη0 hγ hη] with t ht
  simp [ht]

/-!
## The chosen geodesic germ
-/

/-- The positive radius chosen for the local chart geodesic solution. -/
noncomputable def geodesicGermRadius
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ :=
  Classical.choose (exists_local_geodesic_chart_solution g x₀ v₀)

theorem geodesicGermRadius_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    0 < geodesicGermRadius g x₀ v₀ :=
  (Classical.choose_spec (exists_local_geodesic_chart_solution g x₀ v₀)).1

/-- The chosen first-order chart geodesic solution `(position, velocity)`. -/
noncomputable def geodesicGermChartSolution
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → E × E :=
  Classical.choose
    (Classical.choose_spec
      (exists_local_geodesic_chart_solution g x₀ v₀)).2

theorem geodesicGermChartSolution_spec
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    geodesicGermChartSolution g x₀ v₀ 0 =
        (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀),
        HasDerivAt (geodesicGermChartSolution g x₀ v₀)
          (geodesicFlowField (chartChristoffelField g x₀)
            (geodesicGermChartSolution g x₀ v₀ t)) t) ∧
      (let c : ℝ → M :=
        fun t => (extChartAt I x₀).symm (geodesicGermChartSolution g x₀ v₀ t).1
       c 0 = x₀ ∧
        ∀ᶠ t in 𝓝 (0 : ℝ),
          (geodesicGermChartSolution g x₀ v₀ t).1 ∈ (extChartAt I x₀).target ∧
            c t ∈ (extChartAt I x₀).source) :=
  Classical.choose_spec
    (Classical.choose_spec
      (exists_local_geodesic_chart_solution g x₀ v₀)).2

/-- The manifold-valued geodesic germ at `x₀` with chart velocity `v₀`. -/
noncomputable def geodesicGermAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → M :=
  fun t => (extChartAt I x₀).symm (geodesicGermChartSolution g x₀ v₀ t).1

@[simp]
theorem geodesicGermAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    geodesicGermAt g x₀ v₀ 0 = x₀ := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  simp [geodesicGermAt, hspec.1]

theorem geodesicGermAt_eventually_mem_source
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), geodesicGermAt g x₀ v₀ t ∈ (extChartAt I x₀).source := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  filter_upwards [hspec.2.2.2] with t ht
  exact ht.2

/--
The defining property of the chosen germ, exposing the chosen chart solution
on a symmetric interval around `0`.
-/
theorem geodesicGermAt_spec
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ
          (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) ∧
      (∀ t ∈ Ioo (-ε) ε,
        geodesicGermAt g x₀ v₀ t = (extChartAt I x₀).symm (γ t).1) := by
  refine ⟨geodesicGermRadius g x₀ v₀, geodesicGermRadius_pos g x₀ v₀,
    geodesicGermChartSolution g x₀ v₀, ?_, ?_, ?_⟩
  · exact (geodesicGermChartSolution_spec g x₀ v₀).1
  · exact (geodesicGermChartSolution_spec g x₀ v₀).2.1
  · intro t ht
    rfl

/-!
## Initial velocity
-/

/-- The chosen chart solution has initial position derivative `v₀`. -/
theorem geodesicGermChartSolution_position_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    HasDerivAt
      (fun t : ℝ => (geodesicGermChartSolution g x₀ v₀ t).1) v₀ 0 := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have hε := geodesicGermRadius_pos g x₀ v₀
  have hzero_mem :
      (0 : ℝ) ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀) := by
    constructor <;> linarith
  have hder := hspec.2.1 0 hzero_mem
  have hpos :=
    geodesic_position_hasDerivAt
      (Γ := chartChristoffelField g x₀)
      (γ := geodesicGermChartSolution g x₀ v₀)
      hder
  simpa [hspec.1] using hpos

/-- The chosen manifold germ has chart derivative `v₀` at the anchor. -/
theorem geodesicGermAt_chart_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    HasDerivAt
      (fun t : ℝ => extChartAt I x₀ (geodesicGermAt g x₀ v₀ t)) v₀ 0 := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have htarget :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (geodesicGermChartSolution g x₀ v₀ t).1 ∈ (extChartAt I x₀).target :=
    hspec.2.2.2.mono fun t ht => ht.1
  have heq :
      (fun t : ℝ => extChartAt I x₀ (geodesicGermAt g x₀ v₀ t))
        =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (geodesicGermChartSolution g x₀ v₀ t).1) := by
    filter_upwards [htarget] with t ht
    exact (extChartAt I x₀).right_inv ht
  exact (geodesicGermChartSolution_position_hasDerivAt g x₀ v₀).congr_of_eventuallyEq heq

end GeodesicTransport
end Poincare
