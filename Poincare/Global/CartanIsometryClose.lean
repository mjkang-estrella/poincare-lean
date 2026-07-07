import Poincare.Global.CartanScaleGeneric
import Poincare.Global.ExponentialStrictClose

/-!
# Cartan isometry closure boundary

This module records the verified strict-derivative side-condition discharge
available from the shifted Gronwall theorem.  The remaining Cartan
local-isometry instantiation still needs the hosted endpoint differential
action equations and the source endpoint metric blocks.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Shrunk-ball strict derivative side-condition discharge for the charted
exponential.

The theorem chooses one fixed positive time `T` inside the exported PL-flow
interval, shrinks the normal-coordinate source ball so that `T⁻¹ • v` stays in
the PL velocity ball, and then applies the shifted Gronwall strict-derivative
theorem.  The linearized family hypotheses are kept explicit: they are the
remaining data needed to identify the derivative as a concrete endpoint CLM and
to feed the Cartan differential-action equations.
-/
theorem exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × E → ℝ → E × E,
        T ≤ ε ∧
          ∀ v : E, ‖v‖ < ρ →
            v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
              ∀ {Ψ : E → ℝ → E × E}
                (_ : ∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w))
                (_ : ∀ w : E, ∀ t ∈ Icc (-ε) ε,
                  HasDerivWithinAt (Ψ w)
                    (linearizedGeodesicFlowFieldAlong
                      (chartChristoffelField g x₀)
                      (α (extChartAt I x₀ x₀, T⁻¹ • v)) t (Ψ w t))
                    (Icc (-ε) ε) t)
                (hadd : ∀ w w' : E,
                  (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
                (hsmul : ∀ (c : ℝ) (w : E),
                  (Ψ (c • w) T).1 = c • (Ψ w T).1),
                  HasStrictFDerivAt
                    (expAtChartOpenPartialHomeomorph (g := g) x₀)
                    (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0source : (0 : E) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0source) with
    ⟨r, hr_pos, hr_source⟩
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ_pos, δ, hδ_pos, ε, hε_pos, a, α, hα, hexp⟩
  let T : ℝ := min τ ε / 2
  have hT_pos : 0 < T := by
    dsimp [T]
    exact half_pos (lt_min hτ_pos hε_pos)
  have hTτ : T ≤ τ := by
    dsimp [T]
    have hmin : min τ ε ≤ τ := min_le_left τ ε
    linarith
  have hTε : T ≤ ε := by
    dsimp [T]
    have hmin : min τ ε ≤ ε := min_le_right τ ε
    linarith
  have hTmemτ : T ∈ Icc (0 : ℝ) τ := ⟨hT_pos.le, hTτ⟩
  let ρ : ℝ := min r (T * δ / 2) / 2
  have hTδ_pos : 0 < T * δ / 2 := by positivity
  have hmin_pos : 0 < min r (T * δ / 2) :=
    lt_min hr_pos hTδ_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hmin_pos
  have hρ_le_min : ρ ≤ min r (T * δ / 2) := by
    dsimp [ρ]
    linarith [hmin_pos.le]
  have hρ_le_r : ρ ≤ r :=
    hρ_le_min.trans (min_le_left r (T * δ / 2))
  have hρ_le_Tδ : ρ ≤ T * δ / 2 :=
    hρ_le_min.trans (min_le_right r (T * δ / 2))
  refine ⟨ρ, hρ_pos, T, hT_pos, δ, hδ_pos, ε, hε_pos, α, hTε, ?_⟩
  intro v hv
  have hvsrc : v ∈ e.source := by
    apply hr_source
    have hvdist : dist v (0 : E) < r := by
      simpa [dist_eq_norm] using hv.trans_le hρ_le_r
    exact Metric.mem_ball.mpr hvdist
  refine ⟨by simpa [e] using hvsrc, ?_⟩
  intro Ψ hΨ0 hΨder hadd hsmul
  have hT_inv_pos : 0 < T⁻¹ := inv_pos.mpr hT_pos
  have hv_scaled : ‖T⁻¹ • v‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT_inv_pos]
    have hvTδ : ‖v‖ < T * δ / 2 := hv.trans_le hρ_le_Tδ
    have hmul :
        T⁻¹ * (T * δ / 2) = δ / 2 := by
      field_simp [ne_of_gt hT_pos]
    calc
      T⁻¹ * ‖v‖ < T⁻¹ * (T * δ / 2) :=
        mul_lt_mul_of_pos_left hvTδ hT_inv_pos
      _ = δ / 2 := hmul
      _ < δ := by linarith
  have hαside : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) t))
            (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) t ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
        ∀ t ∈ Icc (-ε) ε,
          (α (extChartAt I x₀ x₀, v₀) t).1 ∈
            (extChartAt I x₀).target := by
    intro v₀ hv₀
    rcases hα v₀ hv₀ with ⟨hα0, hαder, hαmem, hαtarget, _hhom⟩
    exact ⟨hα0, hαder, hαmem, hαtarget⟩
  have hexpT : ∀ v₀ : E, ‖v₀‖ < δ →
      expAt g x₀ (T • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) T).1 := by
    intro v₀ hv₀
    exact hexp v₀ hv₀ T hTmemτ
  exact
    expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
      (g := g) (x₀ := x₀) (τ := T) (δ := δ) (ε := ε)
      (a := a) (α := α) (Ψ := Ψ) (v := v)
      hT_pos hε_pos hTε hv_scaled hαside hexpT
      hΨ0 hΨder hadd hsmul

end GeodesicTransport
end Poincare
