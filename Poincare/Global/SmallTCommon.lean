import Poincare.Global.IntervalAlign

/-!
# Small common time and linearized PL shrink boundary

This module packages the current common-time hosted datum together with the
concrete zero-centered source and target linearized Picard-Lindelof witnesses
obtained by shrinking each exported base package.

The exported PL intervals are deliberately the intervals provided by
`PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage`.
Their quantifier order is the current boundary: the shrink is produced after
the common `T` and the endpoint direction have already selected a base curve.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SmallTCommon

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Current common-time export with the concrete source and target linearized
Picard-Lindelof shrinks threaded from the two base packages.

This is the strongest theorem obtainable directly from the present public
exports: each `εlin` is produced from the already selected base curve.  No
relation `T < εlin` is included here.
-/
theorem exists_common_time_enriched_source_target_with_linearized_pl_shrinks
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ T > (0 : ℝ),
        ∃ εs : ℝ, ∃ _hεs_pos : 0 < εs,
          ∃ as : ℝ≥0, ∃ αs : E3 × E3 → ℝ → E3 × E3,
            T < εs ∧
              ∃ εt : ℝ, ∃ _hεt_pos : 0 < εt,
                ∃ aTgt : ℝ≥0, ∃ αt : E3 × E3 → ℝ → E3 × E3,
                  T < εt ∧
                    ∀ v : E3, ‖v‖ < ρ →
                      v ∈
                          (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                        align v ∈
                          (expAtChartOpenPartialHomeomorph
                            (g := roundSphereMetric3) p₀).source ∧
                        EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v ∧
                        EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀
                          T εt aTgt αt (align v) ∧
                        (∃ εlin_source : ℝ, ∃ hεlin_source_pos : 0 < εlin_source,
                          εlin_source ≤ εs ∧
                            ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
                              IsPicardLindelof
                                (fun s : ℝ => fun ψ : E3 × E3 =>
                                  linearizedGeodesicFlowOperator
                                    (chartChristoffelField g x₀)
                                    (αs
                                      (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
                                (tmin := -εlin_source) (tmax := εlin_source)
                                ⟨(0 : ℝ), by
                                  constructor <;> linarith [hεlin_source_pos]⟩
                                ((0 : E3), (0 : E3)) aPL r Lip K) ∧
                        (∃ εlin_target : ℝ, ∃ hεlin_target_pos : 0 < εlin_target,
                          εlin_target ≤ εt ∧
                            ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
                              IsPicardLindelof
                                (fun s : ℝ => fun ψ : E3 × E3 =>
                                  linearizedGeodesicFlowOperator
                                    (chartChristoffelField roundSphereMetric3 p₀)
                                    (αt
                                      (extChartAt I3 p₀ p₀, T⁻¹ • align v) s) ψ)
                                (tmin := -εlin_target) (tmax := εlin_target)
                                ⟨(0 : ℝ), by
                                  constructor <;> linarith [hεlin_target_pos]⟩
                                ((0 : E3), (0 : E3)) aPL r Lip K) := by
  rcases
      CommonTime.exists_common_time_enriched_source_target_cascade
        (g := g) (x₀ := x₀) (p₀ := p₀) align with
    ⟨ρ, hρ_pos, T, hT_pos, εs, hεs_pos, as, αs, hTεs,
      εt, hεt_pos, aTgt, αt, hTεt, hcommon⟩
  refine ⟨ρ, hρ_pos, T, hT_pos, εs, hεs_pos, as, αs, hTεs,
    εt, hεt_pos, aTgt, αt, hTεt, ?_⟩
  intro v hv
  rcases hcommon v hv with
    ⟨hvsrc, hvtgt, hbaseS, hbaseT, _hlinS_cond, _hlinT_cond⟩
  rcases
      PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage
        (g := g) (x₀ := x₀) hεs_pos hbaseS with
    ⟨εlinS, hεlinS_pos, hεlinS_le, aPLS, rS, LipS, KS, hrS, hplS⟩
  rcases
      PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage
        (g := roundSphereMetric3) (x₀ := p₀) hεt_pos hbaseT with
    ⟨εlinT, hεlinT_pos, hεlinT_le, aPLT, rT, LipT, KT, hrT, hplT⟩
  exact
    ⟨hvsrc, hvtgt, hbaseS, hbaseT,
      ⟨εlinS, hεlinS_pos, hεlinS_le, aPLS, rS, LipS, KS, hrS, hplS⟩,
      ⟨εlinT, hεlinT_pos, hεlinT_le, aPLT, rT, LipT, KT, hrT, hplT⟩⟩

end SmallTCommon
end Poincare
