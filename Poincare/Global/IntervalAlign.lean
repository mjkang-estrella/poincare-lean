import Poincare.Global.PLPackages
import Poincare.Global.RayIdentification

/-!
# Interval alignment for hosted linearized families

This module records the reusable part of the interval-shrink bridge: base and
linearized packages restrict along `Icc` inclusions, and a zero-centered PL
package on the already-shrunk interval selects the enriched linearized family on
that same interval.  The selector also threads the hosted uniform-flow facts
needed to identify the radial linearized endpoint.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace IntervalAlign

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/-- The hosted base-curve package restricts to any smaller symmetric interval. -/
theorem baseCurvePackage_restrict_interval
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε ε' : ℝ} {a : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    (hε'ε : ε' ≤ ε)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε a α v) :
    EnrichedCascade.BaseCurvePackage g x₀ T ε' a α v := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase ⊢
  rcases hbase with
    ⟨hγ0, hγder, hγder0T, hγAt, hγmem, hγtarget, hγtarget0T,
      hγcut, hγχ0T, hspeed, hendpoint⟩
  have hsub : Icc (-ε') ε' ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨(neg_le_neg hε'ε).trans hs.1, hs.2.trans hε'ε⟩
  exact
    ⟨hγ0, (fun s hs => (hγder s (hsub hs)).mono hsub), hγder0T, hγAt,
      (fun s hs => hγmem s (hsub hs)),
      (fun s hs => hγtarget s (hsub hs)), hγtarget0T,
      (fun s hs => hγcut s (hsub hs)), hγχ0T, hspeed, hendpoint⟩

omit [T2Space M] in
/-- The hosted linearized-family package restricts to any smaller symmetric interval. -/
theorem linearizedFamilyPackage_restrict_interval
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε ε' : ℝ} {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    {Ψ : E3 → ℝ → E3 × E3}
    (hε'ε : ε' ≤ ε)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ) :
    EnrichedCascade.LinearizedFamilyPackage g x₀ T ε' α v Ψ := by
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin ⊢
  rcases hlin with ⟨hΨ0, hΨder, hΨder0T, hΨAt, hflow, hspeedConst⟩
  have hsub : Icc (-ε') ε' ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨(neg_le_neg hε'ε).trans hs.1, hs.2.trans hε'ε⟩
  exact
    ⟨hΨ0, (fun w s hs => (hΨder w s (hsub hs)).mono hsub),
      hΨder0T, hΨAt, hflow, hspeedConst⟩

/--
Select the enriched hosted linearized family from a zero-centered PL package on
the aligned interval `[-ε, ε]`, with `T < ε`.

The hypotheses `δ, hα0, hαder, hαmem, hαtarget, hexp` are exactly the hosted
uniform-flow facts used inside the common-time construction.  They are consumed
here to export the enriched `LinearizedFamilyPackage`, the strict endpoint
derivative, and the radial ray identity on the same smaller interval as the PL
package.
-/
theorem exists_linearized_family_on_aligned_interval_of_uniform_flow
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ ε T : ℝ} {a : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    (hε_pos : 0 < ε) (hT_pos : 0 < T) (hT_lt_ε : T < ε)
    (hv_scaled : ‖T⁻¹ • v‖ < δ)
    (hα0 : ∀ v₀ : E3, ‖v₀‖ < δ →
      α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀))
    (hαder : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v₀) s))
        (Icc (-ε) ε) s)
    (hαmem : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      α (extChartAt I3 x₀ x₀, v₀) s ∈
        closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ))
    (hαtarget : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target)
    (hexp : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (0 : ℝ) ε,
      expAt g x₀ (s • v₀) =
        (extChartAt I3 x₀).symm (α (extChartAt I3 x₀ x₀, v₀) s).1)
    {aPL r Lip K : ℝ≥0} (hr : 0 < (r : ℝ))
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith [hε_pos]⟩
      ((0 : E3), (0 : E3)) aPL r Lip K) :
    ∃ Ψ : E3 → ℝ → E3 × E3,
      ∃ hadd : ∀ w w' : E3,
        (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1,
        ∃ hsmul : ∀ (c : ℝ) (w : E3),
          (Ψ (c • w) T).1 = c • (Ψ w T).1,
          EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ ∧
            HasStrictFDerivAt
              (expAtChartOpenPartialHomeomorph (g := g) x₀)
              (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v ∧
            (Ψ v T).1 =
              T • (α (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2 := by
  let γ : ℝ → E3 × E3 := α (extChartAt I3 x₀ x₀, T⁻¹ • v)
  have hTε : T ≤ ε := le_of_lt hT_lt_ε
  have hTmemε : T ∈ Icc (-ε) ε := ⟨by linarith [hε_pos, hT_pos], hTε⟩
  have hTmem0ε : T ∈ Icc (0 : ℝ) ε := ⟨hT_pos.le, hTε⟩
  have hTioo : T ∈ Ioo (0 : ℝ) ε := ⟨hT_pos, hT_lt_ε⟩
  have hsub0T : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hε_pos, hs.1], hs.2.trans hTε⟩
  have hαside : ∀ v₀ : E3, ‖v₀‖ < δ →
      α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀) ∧
        (∀ s ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I3 x₀ x₀, v₀) s))
            (Icc (-ε) ε) s) ∧
        (∀ s ∈ Icc (-ε) ε,
          α (extChartAt I3 x₀ x₀, v₀) s ∈
            closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ)) ∧
        ∀ s ∈ Icc (-ε) ε,
          (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈
            (extChartAt I3 x₀).target := by
    intro v₀ hv₀
    exact ⟨hα0 v₀ hv₀, hαder v₀ hv₀, hαmem v₀ hv₀, hαtarget v₀ hv₀⟩
  rcases
      LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
        (g := g) (x₀ := x₀) (γ := γ)
        (ε := ε) (T := T) hε_pos hTmemε hr hpl with
    ⟨Ψ, hΨ0, hΨder, hadd, hsmul⟩
  have hΨder0T : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc (0 : ℝ) T) s := by
    intro w s hs
    exact (hΨder w s (hsub0T hs)).mono hsub0T
  have hΨAt : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s :=
    IsometryInstantiate.linearizedFlow_hasDerivAt_on_shrunk_Icc
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (a := -ε) (b := ε) (c := 0) (d := T)
      (by linarith [hε_pos]) hT_lt_ε hΨder
  have hflow : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r0 : ℝ =>
          α (extChartAt I3 x₀ x₀, T⁻¹ • v + r0 • (T⁻¹ • w)) s)
        (Ψ w s) 0 := by
    intro w s hs
    exact
      chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
        (α := α) (v := T⁻¹ • v) (w := T⁻¹ • w)
        (Ψ := Ψ w) (t := s) hε_pos hv_scaled
        (by
          intro v₀ hv₀
          exact ⟨hα0 v₀ hv₀, hαder v₀ hv₀, hαmem v₀ hv₀⟩)
        (hΨ0 w) (hΨder w) ⟨hs.1, hs.2.trans hTε⟩
  have hodeAt : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (α (extChartAt I3 x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v₀) s)) s := by
    intro v₀ hv₀ s hs
    exact
      IsometryInstantiate.hasDerivAt_of_hasDerivWithinAt_larger_Icc
        (hαder v₀ hv₀ s ⟨hs.1.le, hs.2.le⟩) hs.1 hs.2
  have hspeedConst : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      (fun r0 : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I3 x₀ x₀, T⁻¹ • v + r0 • (T⁻¹ • w)) s).1
          (α (extChartAt I3 x₀ x₀, T⁻¹ • v + r0 • (T⁻¹ • w)) s).2
          (α (extChartAt I3 x₀ x₀, T⁻¹ • v + r0 • (T⁻¹ • w)) s).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r0 : ℝ =>
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • v + r0 • (T⁻¹ • w))
          (T⁻¹ • v + r0 • (T⁻¹ • w))) := by
    intro w s hs
    have hsIoo : s ∈ Ioo (-ε) ε :=
      ⟨by linarith [hε_pos, hs.1], lt_of_le_of_lt hs.2 hT_lt_ε⟩
    exact
      chart_initialVelocity_speed_eventuallyEq_initialSpeed_of_constantSpeed
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε)
        (α := α) (z₀ := extChartAt I3 x₀ x₀)
        (v := T⁻¹ • v) (w := T⁻¹ • w) (t := s)
        hε_pos hv_scaled hα0 hodeAt hsIoo
  have hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ := by
    dsimp [EnrichedCascade.LinearizedFamilyPackage, γ]
    exact ⟨hΨ0, hΨder, hΨder0T, hΨAt, hflow, hspeedConst⟩
  have hstrict :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v :=
    expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
      (g := g) (x₀ := x₀) (τ := T) (δ := δ) (ε := ε)
      (a := a) (α := α) (Ψ := Ψ) (v := v)
      hT_pos hε_pos hTε hv_scaled hαside
      (by
        intro v₀ hv₀
        exact hexp v₀ hv₀ T hTmem0ε)
      hΨ0 hΨder hadd hsmul
  have hRay :
      (Ψ v T).1 = T • (α (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2 :=
    RayIdentification.radial_linearized_endpoint_eq_time_smul_velocity_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (τ := ε) (a := a)
      (α := α) (v := T⁻¹ • v) (Ψ := Ψ v) (T := T)
      hε_pos hv_scaled hα0 hαder hαmem hαtarget hexp (hΨ0 v)
      (hΨder v) hTioo
  exact ⟨Ψ, hadd, hsmul, hlin, hstrict, hRay⟩

end IntervalAlign
end Poincare
