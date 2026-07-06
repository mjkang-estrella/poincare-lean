import Poincare.Global.GeodesicGerm
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Exponential geodesic germs

This file records the germ-level exponential-map laws that can be proved before
global domain control: zero velocity gives the constant germ, and scalar
velocity is the same as scalar time reparametrization.
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

private theorem geodesicGermChartSolution_eventually_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (geodesicGermChartSolution g x₀ v₀)
        (geodesicFlowField (chartChristoffelField g x₀)
          (geodesicGermChartSolution g x₀ v₀ t)) t := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have hε := geodesicGermRadius_pos g x₀ v₀
  have hI :
      Ioo (-(geodesicGermRadius g x₀ v₀))
          (geodesicGermRadius g x₀ v₀) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hI] with t ht
  exact hspec.2.1 t ht

/-- The zero-velocity geodesic germ is eventually constant at its base point. -/
theorem geodesicGermAt_zero_velocity_eventually_const
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∀ᶠ t in 𝓝 (0 : ℝ), geodesicGermAt g x₀ (0 : E) t = x₀ := by
  let η : ℝ → E × E := fun _ => (extChartAt I x₀ x₀, 0)
  have hγ0 :
      geodesicGermChartSolution g x₀ (0 : E) 0 =
        (extChartAt I x₀ x₀, 0) :=
    (geodesicGermChartSolution_spec g x₀ (0 : E)).1
  have hη0 : η 0 = (extChartAt I x₀ x₀, 0) := rfl
  have hγ := geodesicGermChartSolution_eventually_hasDerivAt g x₀ (0 : E)
  have hη :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt η (geodesicFlowField (chartChristoffelField g x₀) (η t)) t := by
    refine .of_forall ?_
    intro t
    have hconst : HasDerivAt η (0 : E × E) t := by
      simpa [η] using hasDerivAt_const t (extChartAt I x₀ x₀, (0 : E))
    simpa [η, geodesicFlowField] using hconst
  have hpull :=
    pulledback_geodesic_eventuallyEq_of_chartChristoffelField
      (g := g) (x₀ := x₀) (v₀ := (0 : E))
      hγ0 hη0 hγ hη
  filter_upwards [hpull] with t ht
  simpa [geodesicGermAt, η] using ht

private theorem geodesicGermAt_smul_eventually_aux
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ (s • v₀) t =
        geodesicGermAt g x₀ v₀ (s * t) := by
  let γ : ℝ → E × E := geodesicGermChartSolution g x₀ v₀
  let η : ℝ → E × E := fun t => ((γ (s * t)).1, s • (γ (s * t)).2)
  have hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀) :=
    (geodesicGermChartSolution_spec g x₀ v₀).1
  have hγs0 :
      geodesicGermChartSolution g x₀ (s • v₀) 0 =
        (extChartAt I x₀ x₀, s • v₀) :=
    (geodesicGermChartSolution_spec g x₀ (s • v₀)).1
  have hη0 : η 0 = (extChartAt I x₀ x₀, s • v₀) := by
    simp [η, γ, hγ0]
  have hγs :=
    geodesicGermChartSolution_eventually_hasDerivAt g x₀ (s • v₀)
  have hscale_tendsto :
      Tendsto (fun t : ℝ => s * t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    by simpa using (hasDerivAt_const_mul (x := (0 : ℝ)) s).continuousAt.tendsto
  have hγ_reparam :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt γ
          (geodesicFlowField (chartChristoffelField g x₀) (γ (s * t)))
          (s * t) :=
    hscale_tendsto.eventually
      (geodesicGermChartSolution_eventually_hasDerivAt g x₀ v₀)
  have hη :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt η (geodesicFlowField (chartChristoffelField g x₀) (η t)) t := by
    filter_upwards [hγ_reparam] with t hγt
    have hpos :
        HasDerivAt (fun τ : ℝ => (γ (s * τ)).1)
          (s • (γ (s * t)).2) t := by
      have hpos_base :=
        geodesic_position_hasDerivAt
          (Γ := chartChristoffelField g x₀) hγt
      simpa [Function.comp_def] using
        hpos_base.scomp t (hasDerivAt_const_mul (x := t) s)
    have hvel :
        HasDerivAt (fun τ : ℝ => s • (γ (s * τ)).2)
          (-(chartChristoffelField g x₀ (γ (s * t)).1
              (s • (γ (s * t)).2) (s • (γ (s * t)).2))) t := by
      have hvel_base :=
        geodesic_velocity_hasDerivAt
          (Γ := chartChristoffelField g x₀) hγt
      have hvel_reparam :
          HasDerivAt (fun τ : ℝ => (γ (s * τ)).2)
            (s • (-(chartChristoffelField g x₀ (γ (s * t)).1
              (γ (s * t)).2 (γ (s * t)).2))) t := by
        simpa [Function.comp_def] using
          hvel_base.scomp t (hasDerivAt_const_mul (x := t) s)
      simpa [smul_smul] using hvel_reparam.const_smul s
    have hηder := hpos.prodMk hvel
    simpa [η, geodesicFlowField] using hηder
  have hpull :=
    pulledback_geodesic_eventuallyEq_of_chartChristoffelField
      (g := g) (x₀ := x₀) (v₀ := s • v₀)
      hγs0 hη0 hγs hη
  filter_upwards [hpull] with t ht
  simpa [geodesicGermAt, η, γ] using ht

/--
Scalar velocity is scalar time reparametrization for the geodesic germ, as a
germ at `0`.
-/
theorem geodesicGermAt_smul_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ (s • v₀) t =
        geodesicGermAt g x₀ v₀ (s * t) :=
  geodesicGermAt_smul_eventually_aux g x₀ v₀ s

/-- The honest germ-level exponential ray through `x₀` with chart velocity `v₀`. -/
def expRayAt (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → M :=
  geodesicGermAt g x₀ v₀

@[simp]
theorem expRayAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    expRayAt g x₀ v₀ 0 = x₀ := by
  simp [expRayAt]

/-- Germ-level exponential ray homogeneity. -/
theorem expRayAt_smul_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      expRayAt g x₀ (s • v₀) t = expRayAt g x₀ v₀ (s * t) := by
  simpa [expRayAt] using geodesicGermAt_smul_eventually g x₀ v₀ s

end GeodesicTransport
end Poincare
