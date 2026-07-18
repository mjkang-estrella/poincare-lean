import Poincare.Global.LinearEndpointGronwall
import Poincare.Global.UniformFlowExport

/-!
# Uniform first-variation endpoint Gronwall package

This file applies the compact-tube endpoint estimate from
`LinearEndpointGronwall` to the actual hosted uniform-flow selectors.  The
result no longer exposes any selected ODE family: it says directly that the
derivative field of the source exponential chart is Lipschitz on a small
normal ball.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformFirstVariationGronwall

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
The derivative field of the source exponential chart is Lipschitz on a
uniform small normal ball.  The endpoint selectors and their auxiliary
Picard--Lindelöf constants are entirely discharged in the proof.
-/
theorem exists_expAtChart_fderiv_lipschitzOn_smallBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∃ C : ℝ≥0,
      LipschitzOnWith C
        (fun q : E3 =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q)
        (ball (0 : E3) ρ) := by
  rcases
      UniformFlowExport.exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (g := g) (x₀ := x₀) with
    ⟨ε₀, hε₀, δ, _hδ, a, α, hα0, hαder₀, hαmem₀,
      hαtarget₀, hexp₀, hsmall⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (g := g) (x₀ := x₀) hε₀ a with
    ⟨ε, hε, hεle, aPL, r, Lip, K, hr, hpl_uniform⟩
  let T : ℝ := ε / 2
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hT_lt_ε : T < ε := by
    dsimp [T]
    linarith
  have hT_lt_ε₀ : T < ε₀ := hT_lt_ε.trans_le hεle
  rcases hsmall T hT hT_lt_ε₀ with ⟨ρ, hρ, hsource⟩
  have hsub : Icc (-ε) ε ⊆ Icc (-ε₀) ε₀ := by
    intro s hs
    exact ⟨(neg_le_neg hεle).trans hs.1, hs.2.trans hεle⟩
  have hαder : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v₀) s))
        (Icc (-ε) ε) s := by
    intro v₀ hv₀ s hs
    exact (hαder₀ v₀ hv₀ s (hsub hs)).mono hsub
  have hαmem : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      α (extChartAt I3 x₀ x₀, v₀) s ∈
        closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmem₀ v₀ hv₀ s (hsub hs)
  have hαtarget : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target := by
    intro v₀ hv₀ s hs
    exact hαtarget₀ v₀ hv₀ s (hsub hs)
  have hexp : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (0 : ℝ) ε,
      expAt g x₀ (s • v₀) =
        (extChartAt I3 x₀).symm
          (α (extChartAt I3 x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexp₀ v₀ hv₀ s ⟨hs.1, hs.2.trans hεle⟩
  rcases
      exists_uniform_linearizedEndpointCLM_gronwall_constant_of_chartFlow
        (g := g) (x₀ := x₀) (T := T) (ε := ε) (δ := δ)
        (a := a) (α := α) hε hT hT_lt_ε.le hα0 hαder hαmem with
    ⟨C, hC⟩
  use ρ
  constructor
  · exact hρ
  use C
  apply LipschitzOnWith.of_dist_le_mul
  intro q₁ hq₁ q₂ hq₂
  have hq₁norm : ‖q₁‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq₁
  have hq₂norm : ‖q₂‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq₂
  rcases hsource q₁ hq₁norm with ⟨_hq₁source, hq₁scaled, hbase₁⟩
  rcases hsource q₂ hq₂norm with ⟨_hq₂source, hq₂scaled, hbase₂⟩
  have hpl₁ := hpl_uniform (T := T) (α := α) (v := q₁) hbase₁
  have hpl₂ := hpl_uniform (T := T) (α := α) (v := q₂) hbase₂
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (T := T)
        (a := a) (α := α) (v := q₁) hε hT hT_lt_ε hq₁scaled
        hα0 hαder hαmem hαtarget hexp hr hpl₁ with
    ⟨Ψ₁, hadd₁, hsmul₁, hlin₁, hstrict₁, _hray₁⟩
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (T := T)
        (a := a) (α := α) (v := q₂) hε hT hT_lt_ε hq₂scaled
        hα0 hαder hαmem hαtarget hexp hr hpl₂ with
    ⟨Ψ₂, hadd₂, hsmul₂, hlin₂, hstrict₂, _hray₂⟩
  have hbound :=
    hC hq₂scaled hq₁scaled hlin₂ hlin₁ hadd₂ hsmul₂ hadd₁ hsmul₁
  have hD₁ :
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q₁ =
        linearizedEndpointCLM (Ψ := Ψ₁) T hadd₁ hsmul₁ :=
    hstrict₁.hasFDerivAt.fderiv
  have hD₂ :
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q₂ =
        linearizedEndpointCLM (Ψ := Ψ₂) T hadd₂ hsmul₂ :=
    hstrict₂.hasFDerivAt.fderiv
  simpa only [dist_eq_norm, hD₁, hD₂] using hbound

end UniformFirstVariationGronwall
end Poincare
