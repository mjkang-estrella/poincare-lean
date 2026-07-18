import Poincare.Global.PointwiseBUCBilinear
import Poincare.Global.QuadraticSemilinearHeatBUC
import Poincare.Global.SemilinearHeatBUCFixedPointRegularity
import Poincare.Global.HeatSemigroupBUCGeneratorCore

/-!
# Pointwise quadratic semilinear heat solutions on `BUC`

This specializes the corrected quadratic heat theory to a bounded bilinear
operation on the finite-dimensional value space.  The nonlinearity in the
mild formula is therefore the literal pointwise contraction
`x ↦ B (u x) (u x)`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- The diagonal of the lifted bilinear operation is exactly the pointwise
quadratic contraction. -/
@[simp]
theorem quadraticOfCLM_pointwiseBUCBilinear_apply
    (B : F →L[ℝ] F →L[ℝ] F) (u : BUC) (x : E) :
    ((quadraticOfCLM (pointwiseBUCBilinear (E := E) B) u : BUC) : E →ᵇ F) x =
      B ((u : E →ᵇ F) x) ((u : E →ᵇ F) x) := by
  exact pointwiseBUCBilinear_apply B u u x

/-- A pointwise bounded quadratic nonlinearity has a unique mild solution in
an explicit positive-time orbit ball.  The displayed formula is the corrected
semilinear heat formula with homogeneous term `H_t u₀`. -/
theorem exists_positive_time_pointwiseQuadraticSemilinearHeatBUC_mildSolution
    (B : F →L[ℝ] F →L[ℝ] F) (u₀ : BUC) :
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        (∀ t : Set.Icc (0 : ℝ) (T : ℝ),
          u t =
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
              ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
                vectorHeatSemigroupBUCExtended (E := E) (F := F)
                  ((t : ℝ) - s)
                  (quadraticOfCLM (pointwiseBUCBilinear (E := E) B)
                    (u (Set.projIcc 0 (T : ℝ) T.property s)))) ∧
        ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
          (∀ t : Set.Icc (0 : ℝ) (T : ℝ),
            v t =
              vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
                ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
                  vectorHeatSemigroupBUCExtended (E := E) (F := F)
                    ((t : ℝ) - s)
                    (quadraticOfCLM (pointwiseBUCBilinear (E := E) B)
                      (v (Set.projIcc 0 (T : ℝ) T.property s)))) →
            v = u := by
  let β : ℝ≥0 := ⟨‖B‖, norm_nonneg B⟩
  let BBUC := pointwiseBUCBilinear (E := E) B
  have hBBUC : ∀ f : BUC, ‖BBUC f‖ ≤ (β : ℝ) * ‖f‖ := by
    intro f
    simpa [BBUC, β] using norm_pointwiseBUCBilinear_apply_le (E := E) B f
  rcases exists_positive_time_semilinearHeatBUC_quadratic_fixedPoint
      BBUC β hBBUC u₀ with ⟨T, hT, u, huBall, hu, huniq⟩
  refine ⟨T, hT, u, huBall, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun w : DuhamelPath T BUC ↦ w t) hu
    simpa [BBUC] using ht.symm
  · intro v hvBall hv
    apply huniq v hvBall
    apply ContinuousMap.ext
    intro t
    rw [semilinearHeatBUCPicard_apply]
    simpa [BBUC] using (hv t).symm

/-- The local pointwise-quadratic mild solution has the expected initial
right derivative whenever the datum is in the strong heat-generator domain. -/
theorem exists_positive_time_pointwiseQuadraticSemilinearHeatBUC_with_initial_derivative
    (B : F →L[ℝ] F →L[ℝ] F) (u₀ Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) u₀ Au₀) :
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        (∀ t : Set.Icc (0 : ℝ) (T : ℝ),
          u t =
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
              ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
                vectorHeatSemigroupBUCExtended (E := E) (F := F)
                  ((t : ℝ) - s)
                  (quadraticOfCLM (pointwiseBUCBilinear (E := E) B)
                    (u (Set.projIcc 0 (T : ℝ) T.property s)))) ∧
        HasDerivWithinAt
          (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
          (Au₀ + quadraticOfCLM (pointwiseBUCBilinear (E := E) B) u₀)
          (Set.Icc 0 (T : ℝ)) 0 := by
  let β : ℝ≥0 := ⟨‖B‖, norm_nonneg B⟩
  let BBUC := pointwiseBUCBilinear (E := E) B
  have hBBUC : ∀ f : BUC, ‖BBUC f‖ ≤ (β : ℝ) * ‖f‖ := by
    intro f
    simpa [BBUC, β] using norm_pointwiseBUCBilinear_apply_le (E := E) B f
  rcases exists_positive_time_semilinearHeatBUC_quadratic_fixedPoint
      BBUC β hBBUC u₀ with ⟨T, hT, u, huBall, hu, _huniq⟩
  refine ⟨T, hT, u, huBall, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun w : DuhamelPath T BUC ↦ w t) hu
    simpa [BBUC] using ht.symm
  · exact semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
      (E := E) (F := F) T u₀ Au₀ (quadraticOfCLM BBUC)
      (continuous_quadraticOfCLM BBUC) u hu hu₀

/-- Integrated heat-orbit initial data satisfy the generator hypothesis
automatically, giving a pointwise-quadratic local solution with a completely
explicit initial derivative. -/
theorem exists_pointwiseQuadraticSemilinearHeatBUC_of_integratedHeatOrbit
    (ε : ℝ≥0) (f : BUC) (B : F →L[ℝ] F →L[ℝ] F) :
    let u₀ := integratedHeatOrbitBUC ε f
    let A₀ :=
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        semilinearHeatBUCPicard T u₀
            (quadraticOfCLM (pointwiseBUCBilinear (E := E) B))
            (continuous_quadraticOfCLM (pointwiseBUCBilinear (E := E) B)) u = u ∧
        HasDerivWithinAt
          (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
          (A₀ + quadraticOfCLM (pointwiseBUCBilinear (E := E) B) u₀)
          (Set.Icc 0 (T : ℝ)) 0 := by
  dsimp only
  let u₀ := integratedHeatOrbitBUC ε f
  let A₀ := vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f
  let β : ℝ≥0 := ⟨‖B‖, norm_nonneg B⟩
  let BBUC := pointwiseBUCBilinear (E := E) B
  have hBBUC : ∀ z : BUC, ‖BBUC z‖ ≤ (β : ℝ) * ‖z‖ := by
    intro z
    simpa [BBUC, β] using norm_pointwiseBUCBilinear_apply_le (E := E) B z
  rcases exists_positive_time_semilinearHeatBUC_quadratic_fixedPoint
      BBUC β hBBUC u₀ with ⟨T, hT, u, huBall, hu, _huniq⟩
  refine ⟨T, hT, u, huBall, hu, ?_⟩
  apply semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (E := E) (F := F) T u₀ A₀ (quadraticOfCLM BBUC)
    (continuous_quadraticOfCLM BBUC) u hu
  exact integratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε f

/-- The same explicit classical initial derivative for the normalized orbit
averages.  These initial data form the dense generator core proved in
`HeatSemigroupBUCGeneratorCore`. -/
theorem exists_pointwiseQuadraticSemilinearHeatBUC_of_normalizedIntegratedHeatOrbit
    (ε : ℝ≥0) (f : BUC) (B : F →L[ℝ] F →L[ℝ] F) :
    let u₀ := normalizedIntegratedHeatOrbitBUC ε f
    let A₀ := ((ε : ℝ)⁻¹) •
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f)
    ∃ T : ℝ≥0, 0 < T ∧
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        semilinearHeatBUCPicard T u₀
            (quadraticOfCLM (pointwiseBUCBilinear (E := E) B))
            (continuous_quadraticOfCLM (pointwiseBUCBilinear (E := E) B)) u = u ∧
        HasDerivWithinAt
          (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
          (A₀ + quadraticOfCLM (pointwiseBUCBilinear (E := E) B) u₀)
          (Set.Icc 0 (T : ℝ)) 0 := by
  dsimp only
  let u₀ := normalizedIntegratedHeatOrbitBUC ε f
  let A₀ := ((ε : ℝ)⁻¹) •
    (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f)
  let β : ℝ≥0 := ⟨‖B‖, norm_nonneg B⟩
  let BBUC := pointwiseBUCBilinear (E := E) B
  have hBBUC : ∀ z : BUC, ‖BBUC z‖ ≤ (β : ℝ) * ‖z‖ := by
    intro z
    simpa [BBUC, β] using norm_pointwiseBUCBilinear_apply_le (E := E) B z
  rcases exists_positive_time_semilinearHeatBUC_quadratic_fixedPoint
      BBUC β hBBUC u₀ with ⟨T, hT, u, huBall, hu, _huniq⟩
  refine ⟨T, hT, u, huBall, hu, ?_⟩
  apply semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (E := E) (F := F) T u₀ A₀ (quadraticOfCLM BBUC)
    (continuous_quadraticOfCLM BBUC) u hu
  exact normalizedIntegratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε f

end Poincare
