import Poincare.Global.HamiltonScalarGradientEstimate
import Poincare.Global.HamiltonScalarGradientMixedBound
import Poincare.Global.HamiltonScalarGradientHessianBound

noncomputable section
set_option autoImplicit false

namespace Poincare.HamiltonScalarGradientQuotientBound

/-- The algebraic core of Hamilton's quotient-eight estimate.

`hWeighted` is the expansion of
`|2 R ∇Ric - ∇R ⊗ Ric|² ≥ 0`, while `hHessian` is the expansion of
`|R Hess R - ∇R ⊗ ∇R|² ≥ 0`.  Keeping these two geometric inputs
separate makes explicit exactly what remains to be connected to the intrinsic
tensor definitions.  The variable normalized-flow term is retained on both
sides rather than discarded.
-/
theorem quotient_reaction_le_eight_of_square_completions
    {R S H P N A G r Q : ℝ}
    (hR : 0 < R)
    (hWeighted : 2 * R * P ≤ 4 * R ^ 2 * A + S * N)
    (hHessian : 0 ≤ R ^ 2 * H - R * G + S ^ 2) :
    -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 - (4 / 3 : ℝ) * r * Q ≤
      8 * A - (4 / 3 : ℝ) * r * Q := by
  have hWeighted' := mul_le_mul_of_nonneg_left hWeighted (show 0 ≤ 2 * R by positivity)
  have hCore :
      -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 ≤ 8 * A := by
    rw [show -2 * H / R + 4 * P / R - 2 * S * N / R ^ 2 +
          2 * G / R ^ 2 - 2 * S ^ 2 / R ^ 3 =
        (-2 * R ^ 2 * H + 4 * R ^ 2 * P - 2 * R * S * N +
          2 * R * G - 2 * S ^ 2) / R ^ 3 by
      field_simp]
    apply (div_le_iff₀ (pow_pos hR 3)).2
    nlinarith
  linarith

end Poincare.HamiltonScalarGradientQuotientBound

open scoped Manifold ContDiff Topology
universe u

namespace Poincare.HamiltonScalarGradientQuotientBound

/-- The pointwise quotient-eight estimate along a supplied normalized flow.
The mean-scalar normalization term remains explicit. -/
theorem quotient_evolution_le_eight_covRicci
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint5 : ∀ s y, MetricEntriesJointContDiffAt gt s y 5)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hRpos : ∀ y, 0 < (gt t).scalarAt y) :
    deriv (fun s ↦ (gt s).scalarGradNormSqAt x / (gt s).scalarAt x) t -
      (gt t).laplacianAt
        (fun y ↦ (gt t).scalarGradNormSqAt y / (gt t).scalarAt y) x ≤
      8 * covRicciNormSqAt (gt t) x -
        (4 / 3 : ℝ) * meanScalar (gt t) *
          ((gt t).scalarGradNormSqAt x / (gt t).scalarAt x) := by
  let g := gt t
  let R := fun y ↦ g.scalarAt y
  let H := ∑ i, g.inner x
    (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
    (g.leviCivita (g.gradient R) x
      (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
  have hRreg : ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 R x :=
    ((IntrinsicBochnerScalarGradient.scalar_contMDiff_three_of_metricEntries_five
      hJoint5 t).contMDiffAt).of_le (by norm_num)
  have hH := HamiltonScalarGradientHessianBound.hessian_gradient_square_completion
    g x hRreg (g.scalarAt x)
  change 0 ≤ g.scalarAt x ^ 2 * H - g.scalarAt x * g.inner x
    (g.gradientAt R x) (g.gradientAt (fun y ↦ g.scalarGradNormSqAt y) x) +
      g.scalarGradNormSqAt x ^ 2 at hH
  have hM := HamiltonScalarGradientMixedBound.mixed_gradient_square_completion g x
  have hcore := quotient_reaction_le_eight_of_square_completions
    (R := g.scalarAt x) (S := g.scalarGradNormSqAt x) (H := H)
    (P := g.inner x (g.gradientAt R x)
      (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x))
    (N := g.ricciNormSqAt x) (A := covRicciNormSqAt g x)
    (G := g.inner x (g.gradientAt R x)
      (g.gradientAt (fun y ↦ g.scalarGradNormSqAt y) x))
    (r := meanScalar g) (Q := g.scalarGradNormSqAt x / g.scalarAt x)
    (hRpos x) hM hH
  rw [HamiltonScalarGradientEstimate.scalarGradientQuotient_evolution_of_normalizedFlow
    x hJoint5 hFlow hRpos]
  change -2 * H / g.scalarAt x +
    4 * g.inner x (g.gradientAt R x)
      (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) / g.scalarAt x -
    2 * g.scalarGradNormSqAt x * g.ricciNormSqAt x / g.scalarAt x ^ 2 -
    (4 / 3 : ℝ) * meanScalar g * (g.scalarGradNormSqAt x / g.scalarAt x) +
    2 * g.inner x (g.gradientAt R x)
      (g.gradientAt (fun y ↦ g.scalarGradNormSqAt y) x) / g.scalarAt x ^ 2 -
    2 * g.scalarGradNormSqAt x ^ 2 / g.scalarAt x ^ 3 ≤ _
  convert hcore using 1
  ring

end Poincare.HamiltonScalarGradientQuotientBound
