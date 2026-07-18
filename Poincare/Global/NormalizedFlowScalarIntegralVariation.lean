import Poincare.Global.RicciEnergyRegularity

/-!
# Scalar-integral and mean-scalar first variation for normalized Ricci flow

This module continues the normalized-flow volume calculation.  It proves the
closed total-scalar first variation of the actual normalized metric speed and
then applies the quotient rule to mean scalar curvature.

The general normalized-flow identity is

`r' = (1 / Vol) * (2 ∫ |Ric°|² - ((n - 2) / n) ∫ (R - r)²)`.

Thus in dimension three there is a genuine negative scalar-variance term.  The
frequently quoted pure formula `(2 / Vol) ∫ |Ric°|²` follows when scalar
curvature is spatially constant (and also in dimension two).

As in `NormalizedFlowVolumeVariation`, the actual derivative statements keep
the Hausdorff-measure differentiation boundary explicit.  We separately
record the pointwise Lichnerowicz/Stokes route supplied by `ScalarVariation`:
the scalar derivative has a divergence-minus-Laplacian boundary, whose closed
integral must vanish, and differentiation must be interchanged with the moving
Riemannian integral.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

section CurvatureEnergyRegularity

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The squared Ricci norm is manifold-differentiable.  This closes the
regularity step needed to integrate the curvature energies below. -/
theorem ricciNormSqAt_mdifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ g.ricciNormSqAt y) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let term :
      Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) → M → ℝ :=
    fun a b' c d y ↦
      (gramMatrix g x y)⁻¹ a c *
        (gramMatrix g x y)⁻¹ b' d *
        g.ricciAt y (gramFrame x y a) (gramFrame x y b') *
        g.ricciAt y (gramFrame x y c) (gramFrame x y d)
  have hRicDiff : ∀ a b',
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          g.ricciAt y (gramFrame x y a) (gramFrame x y b')) x := by
    intro a b'
    have h :=
      covTensor2ExtDifferentiableAt_ricciVariationField_canonical
        (g := g) x (b a) (b b')
    simpa [ricciVariationField, gramFrame, b] using h
  have hterm : ∀ a b' c d,
      MDifferentiableAt I 𝓘(ℝ) (term a b' c d) x := by
    intro a b' c d
    have hA : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (gramMatrix g x y)⁻¹ a c) x :=
      gramMatrix_inv_entry_mdiffAt (g := g) x a c
    have hB : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (gramMatrix g x y)⁻¹ b' d) x :=
      gramMatrix_inv_entry_mdiffAt (g := g) x b' d
    exact (((hA.mul hB).mul (hRicDiff a b')).mul (hRicDiff c d)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp [term])
  have hd : ∀ a b' c,
      MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ ∑ d, term a b' c d y) x := by
    intro a b' c
    exact (MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
      (fun d _ ↦ hterm a b' c d)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ by simp)
  have hc : ∀ a b',
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ ∑ c, ∑ d, term a b' c d y) x := by
    intro a b'
    exact (MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
      (fun c _ ↦ hd a b' c)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ by simp)
  have hb : ∀ a,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ ∑ b', ∑ c, ∑ d, term a b' c d y) x := by
    intro a
    exact (MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
      (fun b' _ ↦ hc a b')).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ by simp)
  have hsum : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ ∑ a, ∑ b', ∑ c, ∑ d, term a b' c d y) x := by
    exact (MDifferentiableAt.sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
      (fun a _ ↦ hb a)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ by simp)
  have hRhs : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ ricciPairingGramRHS g x y) x := by
    simpa [ricciPairingGramRHS, term] using hsum
  have heq :
      (fun y : M ↦ g.ricciNormSqAt y) =ᶠ[nhds x]
        fun y : M ↦ ricciPairingGramRHS g x y := by
    filter_upwards [gramMatrix_eventually_isUnit (g := g) x] with y hG
    calc
      g.ricciNormSqAt y =
          metricVariationRicciPairingAt g (ricciVariationField g) y :=
        (metricVariationRicciPairingAt_ricci g y).symm
      _ = ricciPairingGramRHS g x y := by
        simpa [ricciPairingGramRHS] using
          metricVariationRicciPairingAt_ricci_eq_sum_gram_inv
            (g := g) x y hG
  exact hRhs.congr_of_eventuallyEq heq

/-- The scalar variance density `(R - meanScalar)²` is integrable. -/
theorem centeredScalarSq_integrable
    (g : ClosedSmoothRiemannianMetric n M) :
    Integrable (fun x : M ↦ (g.scalarAt x - meanScalar g) ^ 2)
      (volumeMeasure g) := by
  letI : IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  have hcont : Continuous
      (fun x : M ↦ (g.scalarAt x - meanScalar g) ^ 2) :=
    ((scalarAt_continuous g).sub continuous_const).pow 2
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace
      (fun x : M ↦ (g.scalarAt x - meanScalar g) ^ 2))

end CurvatureEnergyRegularity

section FirstVariationFunctionals

/-- The divergence-minus-Laplacian boundary in closed scalar variation. -/
noncomputable def scalarVariationStokesBoundaryAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : ℝ :=
  tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x -
    (gt t₀).laplacianAt
      (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x

/-- First variation of total scalar curvature before applying the closed
Stokes cancellation. -/
noncomputable def rawTotalScalarFirstVariation
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) : ℝ :=
  ∫ x,
    (deriv (fun t ↦ (gt t).scalarAt x) t₀ +
      (1 / 2 : ℝ) * (gt t₀).scalarAt x *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
    ∂(volumeMeasure (gt t₀))

/-- Closed Einstein-Hilbert first variation after the spatial
divergence/Laplacian terms have been cancelled by Stokes. -/
noncomputable def closedTotalScalarFirstVariation
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ x : M, TM x → TM x → ℝ) : ℝ :=
  ∫ x,
    ((1 / 2 : ℝ) * g.scalarAt x * traceMetricVariationAt g h x -
      metricVariationRicciPairingAt g h x)
    ∂(volumeMeasure g)

/-- The numerator in the normalized mean-scalar evolution identity. -/
noncomputable def normalizedMeanScalarEnergyNumerator
    (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  2 * (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) -
    (((n : ℝ) - 2) / (n : ℝ)) *
      (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g))

end FirstVariationFunctionals

section IntegralAlgebra

/-- The real Riemannian volume of a nonempty closed manifold is positive. -/
theorem totalVolume_pos [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M) :
    0 < totalVolume g := by
  unfold totalVolume
  letI : IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  exact ENNReal.toReal_pos
    (GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g)
    (measure_ne_top (volumeMeasure g) Set.univ)

/-- The real Riemannian volume of a nonempty closed manifold is nonzero. -/
theorem totalVolume_ne_zero [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M) :
    totalVolume g ≠ 0 :=
  (totalVolume_pos g).ne'

/-- Mean scalar curvature times total volume recovers total scalar curvature. -/
theorem meanScalar_mul_totalVolume_eq_totalScalar [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M) :
    meanScalar g * totalVolume g = totalScalar g := by
  unfold meanScalar totalVolume
  exact div_mul_cancel₀ (totalScalar g) (totalVolume_ne_zero g)

/-- The oppositely oriented centered scalar curvature also has zero integral. -/
theorem integral_scalarAt_sub_meanScalar_eq_zero [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M) :
    (∫ x, (g.scalarAt x - meanScalar g) ∂(volumeMeasure g)) = 0 := by
  have h := integral_meanScalar_sub_scalarAt_eq_zero g
  have hfun :
      (fun x : M ↦ g.scalarAt x - meanScalar g) =
        fun x : M ↦ -(meanScalar g - g.scalarAt x) := by
    funext x
    ring
  rw [hfun, integral_neg, h, neg_zero]

/-- The scalar-curvature square is integrable on a closed manifold. -/
theorem scalarAt_sq_integrable
    (g : ClosedSmoothRiemannianMetric n M) :
    Integrable (fun x : M ↦ (g.scalarAt x) ^ 2) (volumeMeasure g) := by
  letI : IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  exact ((scalarAt_continuous g).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace (fun x : M ↦ (g.scalarAt x) ^ 2))

/-- Integrated traceless-Ricci energy is the Ricci energy minus the
dimension-normalized scalar energy. -/
theorem integral_tracelessRicciNormSqAt_eq
    (g : ClosedSmoothRiemannianMetric n M) :
    (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) =
      (∫ x, g.ricciNormSqAt x ∂(volumeMeasure g)) -
        (∫ x, (g.scalarAt x) ^ 2 ∂(volumeMeasure g)) / (n : ℝ) := by
  unfold ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt
  rw [integral_sub (ricciNormSqAt_integrable g)
    ((scalarAt_sq_integrable g).div_const (n : ℝ)), integral_div]

/-- The integrated scalar variance is the scalar second moment minus the
square of its mean times total volume. -/
theorem integral_centeredScalar_sq_eq
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) :
    (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) =
      (∫ x, (g.scalarAt x) ^ 2 ∂(volumeMeasure g)) -
        (meanScalar g) ^ 2 * totalVolume g := by
  let μ := volumeMeasure g
  letI : IsFiniteMeasure μ := volumeMeasure_isFiniteMeasure g
  have hR : Integrable (fun x : M ↦ g.scalarAt x) μ := by
    simpa [μ] using scalarAt_integrable g
  have hR2 : Integrable (fun x : M ↦ (g.scalarAt x) ^ 2) μ := by
    simpa [μ] using scalarAt_sq_integrable g
  have hconst : Integrable (fun _ : M ↦ (meanScalar g) ^ 2) μ :=
    integrable_const ((meanScalar g) ^ 2)
  have hcross : Integrable
      (fun x : M ↦ (2 * meanScalar g) * g.scalarAt x) μ :=
    hR.const_mul (2 * meanScalar g)
  have hadd :
      (∫ x, ((g.scalarAt x) ^ 2 -
          (2 * meanScalar g) * g.scalarAt x + (meanScalar g) ^ 2) ∂μ) =
        (∫ x, ((g.scalarAt x) ^ 2 -
          (2 * meanScalar g) * g.scalarAt x) ∂μ) +
          ∫ _ : M, (meanScalar g) ^ 2 ∂μ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add (hR2.sub hcross) hconst
  have hsub :
      (∫ x, ((g.scalarAt x) ^ 2 -
          (2 * meanScalar g) * g.scalarAt x) ∂μ) =
        (∫ x, (g.scalarAt x) ^ 2 ∂μ) -
          ∫ x, (2 * meanScalar g) * g.scalarAt x ∂μ := by
    simpa only [Pi.sub_apply] using integral_sub hR2 hcross
  calc
    (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂μ) =
        ∫ x, ((g.scalarAt x) ^ 2 -
          (2 * meanScalar g) * g.scalarAt x + (meanScalar g) ^ 2) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = (∫ x, (g.scalarAt x) ^ 2 ∂μ) -
          (2 * meanScalar g) * (∫ x, g.scalarAt x ∂μ) +
          (meanScalar g) ^ 2 * (μ Set.univ).toReal := by
      rw [hadd, hsub, integral_const_mul, integral_const]
      simp [Measure.real]
      ring
    _ = (∫ x, (g.scalarAt x) ^ 2 ∂μ) -
          (meanScalar g) ^ 2 * totalVolume g := by
      change (∫ x, (g.scalarAt x) ^ 2 ∂μ) -
          (2 * meanScalar g) * totalScalar g +
          (meanScalar g) ^ 2 * totalVolume g =
        (∫ x, (g.scalarAt x) ^ 2 ∂μ) -
          (meanScalar g) ^ 2 * totalVolume g
      rw [← meanScalar_mul_totalVolume_eq_totalScalar g]
      ring

end IntegralAlgebra

section NormalizedFlowClosedVariation

/-- The closed Einstein-Hilbert first-variation density of the actual
normalized Ricci speed, in reaction form. -/
theorem closedTotalScalarFirstVariation_integrand_timeDeriv_eq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) (x : M) :
    (1 / 2 : ℝ) * (gt t₀).scalarAt x *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
        metricVariationRicciPairingAt
          (gt t₀) (timeDerivAt gt t₀) x =
      2 * (gt t₀).ricciNormSqAt x - (gt t₀).scalarAt x ^ 2 +
        (((n : ℝ) - 2) / (n : ℝ)) * meanScalar (gt t₀) *
          (gt t₀).scalarAt x := by
  rw [
    traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hFlow x) hn,
    metricVariationRicciPairingAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hFlow x)]
  field_simp [hn]
  ring

/-- The closed total-scalar first variation of normalized Ricci flow is the
integral of the scalar-reaction density. -/
theorem closedTotalScalarFirstVariation_timeDeriv_eq_reaction_integral
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    closedTotalScalarFirstVariation (gt t₀) (timeDerivAt gt t₀) =
      ∫ x, (2 * (gt t₀).ricciNormSqAt x - (gt t₀).scalarAt x ^ 2 +
        (((n : ℝ) - 2) / (n : ℝ)) * meanScalar (gt t₀) *
          (gt t₀).scalarAt x) ∂(volumeMeasure (gt t₀)) := by
  unfold closedTotalScalarFirstVariation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    closedTotalScalarFirstVariation_integrand_timeDeriv_eq hFlow hn x

/-- The integrated normalized scalar-reaction density is exactly the
traceless-Ricci energy minus the dimension-weighted scalar variance. -/
theorem integral_normalizedScalarReaction_eq_energyNumerator
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M)
    (hn : (n : ℝ) ≠ 0) :
    (∫ x, (2 * g.ricciNormSqAt x - g.scalarAt x ^ 2 +
      (((n : ℝ) - 2) / (n : ℝ)) * meanScalar g * g.scalarAt x)
      ∂(volumeMeasure g)) = normalizedMeanScalarEnergyNumerator g := by
  let μ := volumeMeasure g
  let c : ℝ := (((n : ℝ) - 2) / (n : ℝ)) * meanScalar g
  have hRic : Integrable (fun x : M ↦ g.ricciNormSqAt x) μ := by
    simpa [μ] using ricciNormSqAt_integrable g
  have hR2 : Integrable (fun x : M ↦ (g.scalarAt x) ^ 2) μ := by
    simpa [μ] using scalarAt_sq_integrable g
  have hR : Integrable (fun x : M ↦ g.scalarAt x) μ := by
    simpa [μ] using scalarAt_integrable g
  have hRicScaled :
      (∫ x, 2 * g.ricciNormSqAt x ∂μ) =
        2 * ∫ x, g.ricciNormSqAt x ∂μ := by
    exact integral_const_mul 2 (fun x : M ↦ g.ricciNormSqAt x)
  have hReaction :
      (∫ x, (2 * g.ricciNormSqAt x - g.scalarAt x ^ 2 +
          c * g.scalarAt x) ∂μ) =
        (∫ x, 2 * g.ricciNormSqAt x ∂μ) -
          (∫ x, g.scalarAt x ^ 2 ∂μ) +
          ∫ x, c * g.scalarAt x ∂μ := by
    have hsub := integral_sub (hRic.const_mul 2) hR2
    have hadd := integral_add ((hRic.const_mul 2).sub hR2) (hR.const_mul c)
    simpa only [Pi.add_apply, Pi.sub_apply] using hadd.trans
      (congrArg (fun z : ℝ ↦ z + ∫ x, c * g.scalarAt x ∂μ) hsub)
  rw [show (((n : ℝ) - 2) / (n : ℝ)) * meanScalar g = c by rfl]
  rw [hReaction, hRicScaled, integral_const_mul]
  rw [show (∫ x, g.scalarAt x ∂μ) = totalScalar g by rfl]
  unfold normalizedMeanScalarEnergyNumerator
  rw [integral_tracelessRicciNormSqAt_eq,
    integral_centeredScalar_sq_eq]
  rw [← meanScalar_mul_totalVolume_eq_totalScalar]
  change
    2 * (∫ x, g.ricciNormSqAt x ∂μ) -
          (∫ x, g.scalarAt x ^ 2 ∂μ) +
          c * (meanScalar g * totalVolume g) =
      2 * ((∫ x, g.ricciNormSqAt x ∂μ) -
          (∫ x, g.scalarAt x ^ 2 ∂μ) / (n : ℝ)) -
        (((n : ℝ) - 2) / (n : ℝ)) *
          ((∫ x, g.scalarAt x ^ 2 ∂μ) -
            meanScalar g ^ 2 * totalVolume g)
  dsimp [c]
  field_simp [hn]
  ring

/-- The closed normalized-flow total-scalar variation has the intrinsic
energy form. -/
theorem closedTotalScalarFirstVariation_timeDeriv_eq_energyNumerator
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    closedTotalScalarFirstVariation (gt t₀) (timeDerivAt gt t₀) =
      normalizedMeanScalarEnergyNumerator (gt t₀) := by
  rw [closedTotalScalarFirstVariation_timeDeriv_eq_reaction_integral hFlow hn,
    integral_normalizedScalarReaction_eq_energyNumerator (gt t₀) hn]

end NormalizedFlowClosedVariation

section ScalarVariationAndStokesBridge

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Pointwise packaging of the repository's Lichnerowicz scalar-variation
theorem into the boundary notation used by the total-scalar variation. -/
theorem scalarVariation_eq_stokesBoundary_sub_pairing_of_lichnerowicz
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt
      (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x) :
    deriv (fun t ↦ (gt t).scalarAt x) t₀ =
      scalarVariationStokesBoundaryAt gt t₀ x -
        metricVariationRicciPairingAt
          (gt t₀) (timeDerivAt gt t₀) x := by
  unfold scalarVariationStokesBoundaryAt
  exact scalarVariation_lichnerowicz hreg hgt hRaise hDiv hCon

/-- Under normalized flow, the closed first-variation density is integrable.
This makes the Stokes splitting below independent of any extra curvature
regularity parameters. -/
theorem closedTotalScalarFirstVariation_integrand_integrable
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    Integrable
      (fun x : M ↦
        (1 / 2 : ℝ) * (gt t₀).scalarAt x *
            traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
      (volumeMeasure (gt t₀)) := by
  let g := gt t₀
  let c : ℝ := (((n : ℝ) - 2) / (n : ℝ)) * meanScalar g
  have hRic : Integrable (fun x : M ↦ g.ricciNormSqAt x)
      (volumeMeasure g) := ricciNormSqAt_integrable g
  have hR2 : Integrable (fun x : M ↦ g.scalarAt x ^ 2)
      (volumeMeasure g) := scalarAt_sq_integrable g
  have hR : Integrable (fun x : M ↦ g.scalarAt x)
      (volumeMeasure g) := scalarAt_integrable g
  have hReaction : Integrable
      (fun x : M ↦ 2 * g.ricciNormSqAt x - g.scalarAt x ^ 2 +
        c * g.scalarAt x) (volumeMeasure g) :=
    ((hRic.const_mul 2).sub hR2).add (hR.const_mul c)
  apply hReaction.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change
      2 * (gt t₀).ricciNormSqAt x - (gt t₀).scalarAt x ^ 2 +
          (((n : ℝ) - 2) / (n : ℝ)) * meanScalar (gt t₀) *
            (gt t₀).scalarAt x =
        (1 / 2 : ℝ) * (gt t₀).scalarAt x *
            traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x
    exact
      (closedTotalScalarFirstVariation_integrand_timeDeriv_eq
        hFlow hn x).symm

/-- Stokes cancellation identifies the raw moving-integrand expression with
the closed Einstein-Hilbert first variation.  The pointwise scalar variation
can be supplied directly by
`scalarVariation_eq_stokesBoundary_sub_pairing_of_lichnerowicz`.

The vanishing boundary integral is intentionally explicit: it is the closed
manifold divergence/Laplacian theorem, distinct from differentiation of the
moving Hausdorff measure. -/
theorem rawTotalScalarFirstVariation_eq_closed_of_scalarVariation_stokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hBoundaryIntegrable :
      Integrable (scalarVariationStokesBoundaryAt gt t₀)
        (volumeMeasure (gt t₀)))
    (hBoundaryIntegral :
      (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
        ∂(volumeMeasure (gt t₀))) = 0) :
    rawTotalScalarFirstVariation gt t₀ =
      closedTotalScalarFirstVariation (gt t₀) (timeDerivAt gt t₀) := by
  have hClosed :=
    closedTotalScalarFirstVariation_integrand_integrable hFlow hn
  unfold rawTotalScalarFirstVariation closedTotalScalarFirstVariation
  calc
    (∫ x,
      (deriv (fun t ↦ (gt t).scalarAt x) t₀ +
        (1 / 2 : ℝ) * (gt t₀).scalarAt x *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
      ∂(volumeMeasure (gt t₀))) =
        ∫ x, (scalarVariationStokesBoundaryAt gt t₀ x +
          ((1 / 2 : ℝ) * (gt t₀).scalarAt x *
              traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
            metricVariationRicciPairingAt
              (gt t₀) (timeDerivAt gt t₀) x))
          ∂(volumeMeasure (gt t₀)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        dsimp only
        rw [hScalarVariation x]
        ring
    _ = (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
          ∂(volumeMeasure (gt t₀))) +
        ∫ x, ((1 / 2 : ℝ) * (gt t₀).scalarAt x *
              traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
            metricVariationRicciPairingAt
              (gt t₀) (timeDerivAt gt t₀) x)
          ∂(volumeMeasure (gt t₀)) := by
      simpa only [Pi.add_apply] using
        integral_add hBoundaryIntegrable hClosed
    _ = ∫ x, ((1 / 2 : ℝ) * (gt t₀).scalarAt x *
              traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x -
            metricVariationRicciPairingAt
              (gt t₀) (timeDerivAt gt t₀) x)
          ∂(volumeMeasure (gt t₀)) := by
      rw [hBoundaryIntegral, zero_add]

/-- Exact total-scalar derivative handoff.

`hDifferentiateMovingIntegral` is precisely the remaining analytic boundary:
differentiate the Hausdorff-defined Riemannian integral and identify its
derivative with the raw scalar-plus-volume-density expression. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hBoundaryIntegrable :
      Integrable (scalarVariationStokesBoundaryAt gt t₀)
        (volumeMeasure (gt t₀)))
    (hBoundaryIntegral :
      (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
        ∂(volumeMeasure (gt t₀))) = 0)
    (hDifferentiateMovingIntegral :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀) :
    HasDerivAt (fun t ↦ totalScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀ := by
  have hRawClosed :=
    rawTotalScalarFirstVariation_eq_closed_of_scalarVariation_stokes
      hFlow hn hScalarVariation hBoundaryIntegrable hBoundaryIntegral
  have hClosedEnergy :=
    closedTotalScalarFirstVariation_timeDeriv_eq_energyNumerator hFlow hn
  rw [hRawClosed, hClosedEnergy] at hDifferentiateMovingIntegral
  exact hDifferentiateMovingIntegral

end ScalarVariationAndStokesBridge

section MeanScalarDerivative

/-- Quotient-rule endpoint for mean scalar curvature.  The total-volume
identification remains explicit through `hVolumeVariation`; normalized flow
then makes that derivative zero automatically. -/
theorem hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀)
    (hVolumeVariation :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀) /
        totalVolume (gt t₀)) t₀ := by
  have hVolumeZero : HasDerivAt (fun t ↦ totalVolume (gt t)) 0 t₀ :=
    hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow
      hFlow hn hVolumeVariation
  have hVne : totalVolume (gt t₀) ≠ 0 := totalVolume_ne_zero (gt t₀)
  have hQuot := hTotalScalar.div hVolumeZero hVne
  have hValue :
      (normalizedMeanScalarEnergyNumerator (gt t₀) * totalVolume (gt t₀) -
          totalScalar (gt t₀) * 0) / totalVolume (gt t₀) ^ 2 =
        normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀) := by
    field_simp [hVne]
    ring
  rw [hValue] at hQuot
  simpa [meanScalar, totalVolume] using hQuot

/-- Fully combined mean-scalar derivative handoff.  Its two analytic inputs
are exactly the moving total-scalar and moving total-volume differentiation
identifications; scalar variation and Stokes cancellation are separated into
their pointwise and spatial components. -/
theorem hasDerivAt_meanScalar_of_normalizedFlow_scalarVariation_stokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hBoundaryIntegrable :
      Integrable (scalarVariationStokesBoundaryAt gt t₀)
        (volumeMeasure (gt t₀)))
    (hBoundaryIntegral :
      (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
        ∂(volumeMeasure (gt t₀))) = 0)
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀) /
        totalVolume (gt t₀)) t₀ := by
  apply hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    hFlow hn
  · exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow
      hFlow hn hScalarVariation hBoundaryIntegrable hBoundaryIntegral
        hDifferentiateMovingTotalScalar
  · exact hDifferentiateMovingVolume

end MeanScalarDerivative

section ConstantScalarConsequences

/-- When scalar curvature is spatially constant at its mean, the variance
term vanishes and the numerator is the pure traceless-Ricci energy. -/
theorem normalizedMeanScalarEnergyNumerator_eq_two_traceless_energy_of_scalarAt_eq_mean
    (g : ClosedSmoothRiemannianMetric n M)
    (hScalar : ∀ x : M, g.scalarAt x = meanScalar g) :
    normalizedMeanScalarEnergyNumerator g =
      2 * (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) := by
  have hVariance :
      (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) = 0 := by
    calc
      (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) =
          ∫ _ : M, (0 : ℝ) ∂(volumeMeasure g) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by simp [hScalar x]
      _ = 0 := by simp
  unfold normalizedMeanScalarEnergyNumerator
  rw [hVariance, mul_zero, sub_zero]

/-- The frequently quoted pure mean-scalar derivative formula is valid once
the scalar curvature is spatially constant. -/
theorem hasDerivAt_meanScalar_eq_two_traceless_energy_div_volume_of_scalarAt_eq_mean
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar : ∀ x : M,
      (gt t₀).scalarAt x = meanScalar (gt t₀))
    (hTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀)
    (hVolumeVariation :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      ((2 * (∫ x, (gt t₀).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t₀)))) / totalVolume (gt t₀)) t₀ := by
  have h := hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    hFlow hn hTotalScalar hVolumeVariation
  rw [
    normalizedMeanScalarEnergyNumerator_eq_two_traceless_energy_of_scalarAt_eq_mean
      (gt t₀) hScalar] at h
  exact h

/-- Under spatially constant scalar curvature, vanishing of the normalized
mean-scalar numerator is equivalent to the pointwise Einstein identity. -/
theorem normalizedMeanScalarEnergyNumerator_eq_zero_iff_einstein_of_scalarAt_eq_mean
    (g : ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    (hScalar : ∀ x : M, g.scalarAt x = meanScalar g) :
    normalizedMeanScalarEnergyNumerator g = 0 ↔
      ∀ x : M, g.ricciEndoAt x =
        (g.scalarAt x / (n : ℝ)) • LinearMap.id := by
  rw [
    normalizedMeanScalarEnergyNumerator_eq_two_traceless_energy_of_scalarAt_eq_mean
      g hScalar]
  have hEnergy :=
    integral_tracelessRicciNormSqAt_eq_zero_iff_forall_ricciEndoAt_eq
      g hn (tracelessRicciNormSqAt_continuous g)
        (tracelessRicciNormSqAt_integrable g)
  constructor
  · intro hzero
    apply hEnergy.1
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  · intro hEin
    rw [hEnergy.2 hEin, mul_zero]

end ConstantScalarConsequences

section DimensionThree

variable {N : Type u}
variable [TopologicalSpace N] [T2Space N] [CompactSpace N]
variable [ConnectedSpace N]
variable [MeasurableSpace N] [BorelSpace N]
variable [ChartedSpace (ClosedSmoothModel 3) N]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

/-- In dimension three, normalized mean scalar curvature has a negative
one-third scalar-variance correction. -/
theorem normalizedMeanScalarEnergyNumerator_three
    (g : ClosedSmoothRiemannianMetric 3 N) :
    normalizedMeanScalarEnergyNumerator g =
      2 * (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) -
        (1 / 3 : ℝ) *
          (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) := by
  unfold normalizedMeanScalarEnergyNumerator
  norm_num

/-- Exact three-dimensional normalized mean-scalar derivative.  This records
the correction term that is absent from the pure formula. -/
theorem hasDerivAt_meanScalar_three_of_normalizedFlow
    [Nonempty N]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ}
    (hFlow : ∀ x : N, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀)
    (hVolumeVariation :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      ((2 * (∫ x, (gt t₀).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t₀))) -
        (1 / 3 : ℝ) *
          (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
            ∂(volumeMeasure (gt t₀)))) / totalVolume (gt t₀)) t₀ := by
  have h := hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    hFlow (by norm_num) hTotalScalar hVolumeVariation
  rw [normalizedMeanScalarEnergyNumerator_three] at h
  exact h

end DimensionThree

end Poincare
