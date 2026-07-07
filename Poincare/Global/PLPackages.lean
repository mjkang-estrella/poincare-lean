import Poincare.Global.CommonTime

/-!
# Picard-Lindelof packages for hosted linearized flows

This module exports the concrete zero-centered Picard-Lindelof package for a
hosted linearized geodesic equation, after shrinking the time interval to the
operator-norm bound of the exported base curve.  The package is non-vacuous:
the Lipschitz and norm bounds come from the compact-time bound on the
continuous family of linearized operators.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace PLPackages

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
A continuous time-dependent linear ODE has a zero-centered
Picard-Lindelof package on a smaller symmetric interval.

The interval is chosen after bounding the operator norm on the original
compact interval.  The center is exactly zero and the closed-ball radius is
literal (`a = 1`, `r = 1 / 2`).
-/
theorem exists_shrunk_zero_centered_pl_package_of_continuousOn_linearODE
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : ℝ → X →L[ℝ] X) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hA : ContinuousOn A (Icc (-ε₀) ε₀)) :
    ∃ ε : ℝ, ∃ hε_pos : 0 < ε, ε ≤ ε₀ ∧
      ∃ a r L K : ℝ≥0, 0 < (r : ℝ) ∧
        IsPicardLindelof
          (fun t : ℝ => fun x : X => A t x)
          (tmin := -ε) (tmax := ε)
          ⟨(0 : ℝ), by constructor <;> linarith [hε_pos]⟩
          (0 : X) a r L K := by
  rcases isCompact_Icc.exists_bound_of_continuousOn hA with ⟨C, hC⟩
  let K : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  let a : ℝ≥0 := 1
  let r : ℝ≥0 := (1 / 2 : ℝ≥0)
  let L : ℝ≥0 := K
  let ε : ℝ := min ε₀ (1 / (4 * ((L : ℝ) + 1)))
  have hε_bound_pos : 0 < 1 / (4 * ((L : ℝ) + 1)) := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₀ hε_bound_pos
  have hε_le_ε₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_bound : ε ≤ 1 / (4 * ((L : ℝ) + 1)) := by
    dsimp [ε]
    exact min_le_right _ _
  refine ⟨ε, hε, hε_le_ε₀, a, r, L, K, ?_, ?_⟩
  · dsimp [r]
    norm_num
  · refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      have ht₀ : t ∈ Icc (-ε₀) ε₀ := by
        exact ⟨(neg_le_neg hε_le_ε₀).trans ht.1, ht.2.trans hε_le_ε₀⟩
      have hnorm : ‖A t‖ ≤ (K : ℝ) :=
        (hC t ht₀).trans (le_max_left C 0)
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le hnorm).lipschitzOnWith
    · intro x _hx
      have hsub : Icc (-ε) ε ⊆ Icc (-ε₀) ε₀ := by
        intro t ht
        exact ⟨(neg_le_neg hε_le_ε₀).trans ht.1, ht.2.trans hε_le_ε₀⟩
      exact (hA.mono hsub).clm_apply continuousOn_const
    · intro t ht x hx
      have ht₀ : t ∈ Icc (-ε₀) ε₀ := by
        exact ⟨(neg_le_neg hε_le_ε₀).trans ht.1, ht.2.trans hε_le_ε₀⟩
      have hnormA : ‖A t‖ ≤ (K : ℝ) :=
        (hC t ht₀).trans (le_max_left C 0)
      have hxnorm : ‖x‖ ≤ (1 : ℝ) := by
        simpa [a, Metric.mem_closedBall, dist_eq_norm] using hx
      calc
        ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A t) x
        _ ≤ (K : ℝ) * 1 := by
          gcongr
        _ = (L : ℝ) := by
          simp [L]
    · dsimp [a, r]
      rw [sub_zero, zero_sub, neg_neg, max_eq_left (le_of_eq rfl)]
      have hLnonneg : 0 ≤ (L : ℝ) := by positivity
      calc
        (L : ℝ) * ε ≤ (L : ℝ) * (1 / (4 * ((L : ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_left hε_le_bound hLnonneg
        _ = (L : ℝ) / (4 * ((L : ℝ) + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
          nlinarith
        _ ≤ (1 : ℝ) - 1 / 2 := by norm_num

omit [T2Space M] in
/-- The full-interval derivative field in a base package makes its hosted curve continuous. -/
theorem baseCurvePackage_continuousOn
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} {a : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε a α v) :
    ContinuousOn (fun s : ℝ => α (extChartAt I3 x₀ x₀, T⁻¹ • v) s)
      (Icc (-ε) ε) := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  exact HasDerivWithinAt.continuousOn hbase.2.1

omit [T2Space M] in
/--
The zero-centered PL package for the linearized geodesic equation along an
exported base curve, on a shrunk interval.
-/
theorem exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {aBase : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε₀ aBase α v) :
    ∃ ε : ℝ, ∃ hε_pos : 0 < ε, ε ≤ ε₀ ∧
      ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
        IsPicardLindelof
          (fun s : ℝ => fun ψ : E3 × E3 =>
            linearizedGeodesicFlowOperator
              (chartChristoffelField g x₀)
              (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
          (tmin := -ε) (tmax := ε)
          ⟨(0 : ℝ), by constructor <;> linarith [hε_pos]⟩
          ((0 : E3), (0 : E3)) aPL r Lip K := by
  let γ : ℝ → E3 × E3 := fun s => α (extChartAt I3 x₀ x₀, T⁻¹ • v) s
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := chartChristoffelField g x₀
  let A : ℝ → (E3 × E3) →L[ℝ] (E3 × E3) :=
    fun s => linearizedGeodesicFlowOperator Γ (γ s)
  have hγ : ContinuousOn γ (Icc (-ε₀) ε₀) := by
    simpa [γ] using
      baseCurvePackage_continuousOn (g := g) (x₀ := x₀) hbase
  have hD :
      Continuous (fun q : E3 × E3 => linearizedGeodesicFlowOperator Γ q) := by
    simpa [linearizedGeodesicFlowOperator, Γ] using
      (geodesicFlowField_chartChristoffelField_contDiff
        (g := g) (x₀ := x₀)).continuous_fderiv (by norm_num)
  have hA : ContinuousOn A (Icc (-ε₀) ε₀) := by
    simpa [A, γ] using hD.comp_continuousOn hγ
  simpa [A, Γ, γ] using
    exists_shrunk_zero_centered_pl_package_of_continuousOn_linearODE
      (A := A) hε₀ hA

omit [T2Space M] in
/--
Select the all-direction hosted linearized family from a zero-centered PL
package on the same interval.
-/
theorem exists_selected_linearized_family_of_zero_centered_pl_package
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E3 × E3} {ε T : ℝ} (hε : 0 < ε)
    (hT : T ∈ Icc (-ε) ε)
    {aPL r Lip K : ℝ≥0} (hr : 0 < (r : ℝ))
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀) (γ s) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E3), (0 : E3)) aPL r Lip K) :
    ∃ Ψ : E3 → ℝ → E3 × E3,
      (∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w)) ∧
        (∀ w : E3, ∀ s ∈ Icc (-ε) ε,
          HasDerivWithinAt (Ψ w)
            (linearizedGeodesicFlowFieldAlong
              (chartChristoffelField g x₀) γ s (Ψ w s))
            (Icc (-ε) ε) s) ∧
        (∀ w w' : E3,
          (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1) ∧
        ∀ (c : ℝ) (w : E3),
          (Ψ (c • w) T).1 = c • (Ψ w T).1 := by
  exact
    LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
      (g := g) (x₀ := x₀) (γ := γ) (ε := ε) (T := T)
      hε hT hr hpl

omit [T2Space M] in
/--
Package construction plus selection for every endpoint time lying in the
shrunk PL interval of an exported hosted base curve.
-/
theorem exists_shrunk_pl_package_and_selected_linearized_family
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Tbase ε₀ : ℝ} (hε₀ : 0 < ε₀)
    {aBase : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ Tbase ε₀ aBase α v) :
    ∃ ε : ℝ, ∃ hε_pos : 0 < ε, ε ≤ ε₀ ∧
      ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
        IsPicardLindelof
          (fun s : ℝ => fun ψ : E3 × E3 =>
            linearizedGeodesicFlowOperator
              (chartChristoffelField g x₀)
              (α (extChartAt I3 x₀ x₀, Tbase⁻¹ • v) s) ψ)
          (tmin := -ε) (tmax := ε)
          ⟨(0 : ℝ), by constructor <;> linarith [hε_pos]⟩
          ((0 : E3), (0 : E3)) aPL r Lip K ∧
        ∀ Tsel : ℝ, Tsel ∈ Icc (-ε) ε →
          ∃ Ψ : E3 → ℝ → E3 × E3,
            (∀ w : E3, Ψ w 0 = ((0 : E3), Tsel⁻¹ • w)) ∧
              (∀ w : E3, ∀ s ∈ Icc (-ε) ε,
                HasDerivWithinAt (Ψ w)
                  (linearizedGeodesicFlowFieldAlong
                    (chartChristoffelField g x₀)
                    (fun τ : ℝ =>
                      α (extChartAt I3 x₀ x₀, Tbase⁻¹ • v) τ)
                    s (Ψ w s))
                  (Icc (-ε) ε) s) ∧
              (∀ w w' : E3,
                (Ψ (w + w') Tsel).1 = (Ψ w Tsel).1 + (Ψ w' Tsel).1) ∧
              ∀ (c : ℝ) (w : E3),
                (Ψ (c • w) Tsel).1 = c • (Ψ w Tsel).1 := by
  rcases
    exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage
      (g := g) (x₀ := x₀) hε₀ hbase with
    ⟨ε, hε, hε_le, aPL, r, Lip, K, hr, hpl⟩
  refine ⟨ε, hε, hε_le, aPL, r, Lip, K, hr, hpl, ?_⟩
  intro Tsel hTsel
  exact
    exists_selected_linearized_family_of_zero_centered_pl_package
      (g := g) (x₀ := x₀)
      (γ := fun τ : ℝ => α (extChartAt I3 x₀ x₀, Tbase⁻¹ • v) τ)
      (ε := ε) (T := Tsel) hε hTsel hr hpl

end PLPackages
end Poincare
