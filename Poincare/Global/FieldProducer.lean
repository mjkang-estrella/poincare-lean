import Poincare.Global.UniformFlowExport

/-!
# Exponential-chart derivative fields

This module records the non-vacuous producer part that is currently available
from the ball-uniform hosted selector: actual source and target derivative
fields can be chosen, and they are genuine derivative fields on neighborhoods
of each aligned point.  The `C1` regularity of these selected fields is not
asserted here.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace FieldProducer

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
The ball-uniform hosted selector produces actual source and target derivative
fields for the two exponential charts.  Around every sufficiently small source
normal vector `v`, `sourceD` is a derivative field for the source exponential
chart near `v`, and `targetD` is a derivative field for the round-sphere
exponential chart near `L v`.

This is the verified producer up to the remaining regularity boundary:
`ExpChartC2` still additionally asks for `ContDiffAt ℝ 1 sourceD v` and
`ContDiffAt ℝ 1 targetD (L v)`, which is not exported by the current
second-variation/dependence chain.
-/
theorem exists_source_target_expChart_derivative_fields_on_aligned_ball
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ sourceD targetD : E3 → E3 →L[ℝ] E3,
        ∀ v : E3, ‖v‖ < ρ →
          let eM := expAtChartOpenPartialHomeomorph (g := g) x₀
          let eS := expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀
          v ∈ eM.source ∧
            L v ∈ eS.source ∧
            HasFDerivAt eM (sourceD v) v ∧
            HasFDerivAt eS (targetD (L v)) (L v) ∧
            (∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q) ∧
            ∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q := by
  rcases
      UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors
        (g := g) (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, T, _hT_pos, _εs, _hεs_pos, _as, _αs,
      _εlinS, _hεlinS_pos, _hεlinS_le, _hTεlinS, _δs, _hδs_pos,
      _hα0S, _hαderS, _hαmemS, _hαtargetS, _hexpS,
      _aPLS, _rS, _LipS, _KS, _hrS, _εt, _hεt_pos, _aTgt, _αt,
      _εlinT, _hεlinT_pos, _hεlinT_le, _hTεlinT, _δt, _hδt_pos,
      _hα0T, _hαderT, _hαmemT, _hαtargetT, _hexpT,
      _aPLT, _rT, _LipT, _KT, _hrT, hcommon⟩
  let eM := expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀
  let Lclm : E3 ≃L[ℝ] E3 := L.toContinuousLinearEquiv
  have hsource_exists :
      ∀ q : E3, ‖q‖ < ρ → ∃ D : E3 →L[ℝ] E3, HasFDerivAt eM D q := by
    intro q hq
    rcases hcommon q hq with
      ⟨_hqsrc, _hqtgt, _hqscaledS, _hqscaledT, _hbaseS, _hbaseT, _hplS,
        ⟨Ψs, hadds, hsmuls, _hlinS, hstrictS, _hRayS⟩,
        _hplT, _Ψt, _haddt, _hsmult, _hlinT, _hstrictT, _hRayT⟩
    exact ⟨linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls, by
      simpa [eM] using hstrictS.hasFDerivAt⟩
  have htarget_exists :
      ∀ q : E3, ‖Lclm.symm q‖ < ρ →
        ∃ D : E3 →L[ℝ] E3, HasFDerivAt eS D q := by
    intro q hq
    rcases hcommon (Lclm.symm q) hq with
      ⟨_hqsrc, _hqtgt, _hqscaledS, _hqscaledT, _hbaseS, _hbaseT, _hplS,
        _hsourcePack, _hplT, Ψt, haddt, hsmult, _hlinT, hstrictT, _hRayT⟩
    have hLsymm : L (Lclm.symm q) = q := by
      change Lclm (Lclm.symm q) = q
      exact Lclm.apply_symm_apply q
    exact ⟨linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult, by
      simpa [eS, hLsymm] using hstrictT.hasFDerivAt⟩
  let sourceD : E3 → E3 →L[ℝ] E3 := fun q =>
    if hq : ‖q‖ < ρ then Classical.choose (hsource_exists q hq) else 0
  let targetD : E3 → E3 →L[ℝ] E3 := fun q =>
    if hq : ‖Lclm.symm q‖ < ρ then Classical.choose (htarget_exists q hq) else 0
  have hfields :
      ∀ v : E3, ‖v‖ < ρ →
        let eM := expAtChartOpenPartialHomeomorph (g := g) x₀
        let eS := expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀
        v ∈ eM.source ∧
          L v ∈ eS.source ∧
          HasFDerivAt eM (sourceD v) v ∧
          HasFDerivAt eS (targetD (L v)) (L v) ∧
          (∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q) ∧
          ∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q := by
    intro v hv
    dsimp only
    rcases hcommon v hv with
      ⟨hvsrc, hvtgt, _hvscaledS, _hvscaledT, _hbaseS, _hbaseT, _hplS,
        _hsourcePack, _hplT, _Ψt, _haddt, _hsmult, _hlinT, _hstrictT, _hRayT⟩
    have hsource_at : HasFDerivAt eM (sourceD v) v := by
      dsimp [sourceD]
      rw [dif_pos hv]
      exact Classical.choose_spec (hsource_exists v hv)
    have hLsymm_v : Lclm.symm (L v) = v := by
      change Lclm.symm (Lclm v) = v
      exact Lclm.symm_apply_apply v
    have htarget_norm : ‖Lclm.symm (L v)‖ < ρ := by
      simpa [hLsymm_v] using hv
    have htarget_at : HasFDerivAt eS (targetD (L v)) (L v) := by
      dsimp [targetD]
      rw [dif_pos htarget_norm]
      exact Classical.choose_spec (htarget_exists (L v) htarget_norm)
    have hsource_nhds : Metric.ball (0 : E3) ρ ∈ 𝓝 v := by
      have hvball : v ∈ Metric.ball (0 : E3) ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hv
      exact Metric.isOpen_ball.mem_nhds hvball
    have hsource_near :
        ∀ q ∈ Metric.ball (0 : E3) ρ, HasFDerivAt eM (sourceD q) q := by
      intro q hqball
      have hq : ‖q‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hqball
      dsimp [sourceD]
      rw [dif_pos hq]
      exact Classical.choose_spec (hsource_exists q hq)
    have htarget_preimage :
        {q : E3 | Lclm.symm q ∈ Metric.ball (0 : E3) ρ} ∈ 𝓝 (L v) := by
      have hball_at_symm : Metric.ball (0 : E3) ρ ∈ 𝓝 (Lclm.symm (L v)) := by
        simpa [hLsymm_v] using hsource_nhds
      exact Lclm.symm.continuous.continuousAt.preimage_mem_nhds hball_at_symm
    have htarget_near :
        ∀ q ∈ {q : E3 | Lclm.symm q ∈ Metric.ball (0 : E3) ρ},
          HasFDerivAt eS (targetD q) q := by
      intro q hqball
      have hq : ‖Lclm.symm q‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hqball
      dsimp [targetD]
      rw [dif_pos hq]
      exact Classical.choose_spec (htarget_exists q hq)
    exact
      ⟨by simpa [eM] using hvsrc, by simpa [eS] using hvtgt,
        by simpa [eM] using hsource_at, by simpa [eS] using htarget_at,
        ⟨Metric.ball (0 : E3) ρ, hsource_nhds, hsource_near⟩,
        ⟨{q : E3 | Lclm.symm q ∈ Metric.ball (0 : E3) ρ},
          htarget_preimage, htarget_near⟩⟩
  exact ⟨ρ, hρ_pos, sourceD, targetD, hfields⟩

end FieldProducer
end Poincare
