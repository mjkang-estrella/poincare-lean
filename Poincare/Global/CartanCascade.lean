import Poincare.Global.LinearizedAdditivity

/-!
# Cartan cascade boundary

This module records the next non-vacuous cascade step after endpoint
linearity: the hosted linearized Picard-Lindelöf data now feeds the shrunk
strict-derivative theorem on both the source and the aligned round-sphere
target.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCascade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Common shrunk source/target strict-derivative cascade.

On a sufficiently small source ball, `v` is in the source exponential chart
domain and `align v` is in the round-sphere target exponential chart domain.
For each side, Picard-Lindelöf data for the hosted linearized equation now
constructs the all-direction linearized family with endpoint additivity and
homogeneity, packages its endpoint as `linearizedEndpointCLM`, and applies the
shrunk strict-derivative theorem.
-/
theorem exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ Ts > (0 : ℝ), ∃ εs : ℝ, ∃ hεs_pos : 0 < εs,
        ∃ αs : E × E → ℝ → E × E,
        Ts ≤ εs ∧
          ∃ Tt > (0 : ℝ), ∃ εt : ℝ, ∃ hεt_pos : 0 < εt,
            ∃ αt : E × E → ℝ → E × E,
            Tt ≤ εt ∧
              ∀ v : E, ‖v‖ < ρ →
                v ∈
                    (GeodesicTransport.expAtChartOpenPartialHomeomorph
                      (g := g) x₀).source ∧
                  align v ∈
                    (GeodesicTransport.expAtChartOpenPartialHomeomorph
                      (g := roundSphereMetric3) p₀).source ∧
                  (∀ {a r Lip K : ℝ≥0}, 0 < (r : ℝ) →
                    IsPicardLindelof
                      (fun t : ℝ => fun ψ : E × E =>
                        linearizedGeodesicFlowOperator
                          (GeodesicTransport.chartChristoffelField g x₀)
                          (αs (extChartAt I x₀ x₀, Ts⁻¹ • v) t) ψ)
                      (tmin := -εs) (tmax := εs)
                      ⟨(0 : ℝ), by constructor <;> linarith [hεs_pos]⟩
                      ((0 : E), (0 : E)) a r Lip K →
                    ∃ Ψ : E → ℝ → E × E,
                      ∃ hadd : ∀ w w' : E,
                        (Ψ (w + w') Ts).1 = (Ψ w Ts).1 + (Ψ w' Ts).1,
                        ∃ hsmul : ∀ (c : ℝ) (w : E),
                          (Ψ (c • w) Ts).1 = c • (Ψ w Ts).1,
                          (∀ w : E, Ψ w 0 = ((0 : E), Ts⁻¹ • w)) ∧
                            (∀ w : E, ∀ t ∈ Icc (-εs) εs,
                              HasDerivWithinAt (Ψ w)
                                (linearizedGeodesicFlowFieldAlong
                                  (GeodesicTransport.chartChristoffelField g x₀)
                                  (αs (extChartAt I x₀ x₀, Ts⁻¹ • v))
                                  t (Ψ w t))
                                (Icc (-εs) εs) t) ∧
                            HasStrictFDerivAt
                              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                                (g := g) x₀)
                              (linearizedEndpointCLM (Ψ := Ψ) Ts hadd hsmul) v) ∧
                  (∀ {a r Lip K : ℝ≥0}, 0 < (r : ℝ) →
                    IsPicardLindelof
                      (fun t : ℝ => fun ψ : E × E =>
                        linearizedGeodesicFlowOperator
                          (GeodesicTransport.chartChristoffelField
                            roundSphereMetric3 p₀)
                          (αt (extChartAt I p₀ p₀, Tt⁻¹ • align v) t) ψ)
                      (tmin := -εt) (tmax := εt)
                      ⟨(0 : ℝ), by constructor <;> linarith [hεt_pos]⟩
                      ((0 : E), (0 : E)) a r Lip K →
                    ∃ Ψ : E → ℝ → E × E,
                      ∃ hadd : ∀ w w' : E,
                        (Ψ (w + w') Tt).1 = (Ψ w Tt).1 + (Ψ w' Tt).1,
                        ∃ hsmul : ∀ (c : ℝ) (w : E),
                          (Ψ (c • w) Tt).1 = c • (Ψ w Tt).1,
                          (∀ w : E, Ψ w 0 = ((0 : E), Tt⁻¹ • w)) ∧
                            (∀ w : E, ∀ t ∈ Icc (-εt) εt,
                              HasDerivWithinAt (Ψ w)
                                (linearizedGeodesicFlowFieldAlong
                                  (GeodesicTransport.chartChristoffelField
                                    roundSphereMetric3 p₀)
                                  (αt (extChartAt I p₀ p₀, Tt⁻¹ • align v))
                                  t (Ψ w t))
                                (Icc (-εt) εt) t) ∧
                            HasStrictFDerivAt
                              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                                (g := roundSphereMetric3) p₀)
                              (linearizedEndpointCLM (Ψ := Ψ) Tt hadd hsmul)
                              (align v)) := by
  rcases
      GeodesicTransport.exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
        (g := g) (x₀ := x₀) with
    ⟨ρs, hρs_pos, Ts, hTs_pos, _δs, _hδs_pos, εs, hεs_pos, αs, hTsεs,
      hsource⟩
  rcases
      GeodesicTransport.exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
        (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨ρt, hρt_pos, Tt, hTt_pos, _δt, _hδt_pos, εt, hεt_pos, αt, hTtεt,
      htarget⟩
  let C : ℝ := ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ + 1
  let ρ : ℝ := min ρs (ρt / C) / 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hρt_div_pos : 0 < ρt / C := div_pos hρt_pos hC_pos
  have hmin_pos : 0 < min ρs (ρt / C) := lt_min hρs_pos hρt_div_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hmin_pos
  have hρ_le_ρs : ρ ≤ ρs := by
    dsimp [ρ]
    exact (by linarith [hmin_pos.le] : min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
      (min_le_left ρs (ρt / C))
  have hρ_le_ρt_div : ρ ≤ ρt / C := by
    dsimp [ρ]
    exact (by linarith [hmin_pos.le] : min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
      (min_le_right ρs (ρt / C))
  refine ⟨ρ, hρ_pos, Ts, hTs_pos, εs, hεs_pos, αs, hTsεs,
    Tt, hTt_pos, εt, hεt_pos, αt, hTtεt, ?_⟩
  intro v hv
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hρ_le_ρs
  have halign_norm : ‖align v‖ < ρt := by
    have hnorm_bound :
        ‖align v‖ ≤ ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (align.toContinuousLinearEquiv : E →L[ℝ] E) v
    have hCnorm :
        ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hρ_le_ρt_div
    have hCmul : C * ‖v‖ < ρt := by
      calc
        C * ‖v‖ < C * (ρt / C) := mul_lt_mul_of_pos_left hv_div hC_pos
        _ = ρt := by field_simp [ne_of_gt hC_pos]
    exact lt_of_le_of_lt (hnorm_bound.trans hCnorm) hCmul
  rcases hsource v hv_source_norm with ⟨hvsrc, hsourceDeriv⟩
  rcases htarget (align v) halign_norm with ⟨hvtgt, htargetDeriv⟩
  have hTs_mem : Ts ∈ Icc (-εs) εs := ⟨by linarith, hTsεs⟩
  have hTt_mem : Tt ∈ Icc (-εt) εt := ⟨by linarith, hTtεt⟩
  refine ⟨hvsrc, hvtgt, ?_, ?_⟩
  · intro a r Lip K hr hpl
    rcases
        _root_.Poincare.LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
          (g := g) (x₀ := x₀)
          (γ := αs (extChartAt I x₀ x₀, Ts⁻¹ • v))
          (ε := εs) (T := Ts) hεs_pos hTs_mem hr hpl with
      ⟨Ψ, hΨ0, hΨder, hadd, hsmul⟩
    exact ⟨Ψ, hadd, hsmul, hΨ0, hΨder,
      hsourceDeriv hΨ0 hΨder hadd hsmul⟩
  · intro a r Lip K hr hpl
    rcases
        _root_.Poincare.LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
          (g := roundSphereMetric3) (x₀ := p₀)
          (γ := αt (extChartAt I p₀ p₀, Tt⁻¹ • align v))
          (ε := εt) (T := Tt) hεt_pos hTt_mem hr hpl with
      ⟨Ψ, hΨ0, hΨder, hadd, hsmul⟩
    exact ⟨Ψ, hadd, hsmul, hΨ0, hΨder,
      htargetDeriv hΨ0 hΨder hadd hsmul⟩

end CartanCascade
end Poincare
