import Poincare.Global.NormalizedFlowPointwiseConvergence
import Poincare.Global.ScalarVariation

/-!
# Volume first variation of normalized closed Ricci flow

For a metric variation `h`, the infinitesimal change of Riemannian volume is
`(1 / 2) ∫ tr_g h dμ_g`.  This file proves the part of volume preservation
which follows from the normalized Ricci-flow equation itself:

* the metric trace of the normalized speed is `2 * (meanScalar g - R)`;
* the centered scalar curvature has integral zero;
* consequently the total-volume first variation vanishes.

The global measure in this repository is defined as a Hausdorff measure.  A
separate metric-to-Hausdorff-measure differentiation theorem is still needed
to identify this first variation with `deriv (fun t ↦ volumeMeasure (gt t)
Set.univ)`.  The final theorem below records the exact, honest handoff: once
that analytic identification is available, the actual total-volume derivative
is automatically zero.
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

/-- The real total volume associated to the repository's Riemannian volume
measure. -/
noncomputable def totalVolume
    (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  (volumeMeasure g Set.univ).toReal

/-- The standard total-volume first variation `(1 / 2) ∫ tr_g h dμ_g`.

This definition is deliberately a first-variation functional, rather than a
claim that the Hausdorff-defined `volumeMeasure` has already been
differentiated with respect to `g`. -/
noncomputable def totalVolumeFirstVariation
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ x : M, TM x → TM x → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ x, traceMetricVariationAt g h x ∂(volumeMeasure g)

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Tracing the metric itself gives the dimension of the tangent fiber. -/
theorem traceMetricVariationAt_inner_eq_dimension
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    traceMetricVariationAt g (fun y v w ↦ g.inner y v w) x = (n : ℝ) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  have hdim : (Module.finrank ℝ (TM x) : ℝ) = (n : ℝ) := by
    exact_mod_cast
      ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq
        (n := n) (M := M) x
  change (∑ i, g.inner x (b i) (sharp i)) = (n : ℝ)
  calc
    (∑ i, g.inner x (b i) (sharp i)) =
        ∑ _i : Fin (Module.finrank ℝ (TM x)), (1 : ℝ) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcoord :
          b.coord i (b i) = g.inner x (b i) (sharp i) :=
        coord_eq_inner_metricDualVectorAt_of_basis
          (g := g) (x := x) (b := b) i (b i)
      rw [← hcoord]
      simp [b]
    _ = (Module.finrank ℝ (TM x) : ℝ) := by simp
    _ = (n : ℝ) := hdim

/-- The normalized Ricci-flow right-hand side has trace
`-2 R + (2/n) meanScalar * n` before cancelling the nonzero dimension. -/
theorem traceMetricVariationAt_normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    traceMetricVariationAt g
        (fun y v w ↦ normalizedRicciFlowRHSAt g y v w) x =
      -2 * g.scalarAt x +
        (2 / (n : ℝ)) * meanScalar g * (n : ℝ) := by
  rw [show (fun y v w ↦ normalizedRicciFlowRHSAt g y v w) =
      (fun y v w ↦
        (-2 * g.ricciAt y v w) +
          ((2 / (n : ℝ)) * meanScalar g) * g.inner y v w) by
    funext y v w
    rfl]
  rw [traceMetricVariationAt_add]
  have hRic :
      traceMetricVariationAt g
          (fun y v w ↦ -2 * g.ricciAt y v w) x =
        -2 * g.scalarAt x := by
    change
      traceMetricVariationAt g (negTwoRicciVariationField g) x =
        -2 * g.scalarAt x
    exact traceMetricVariationAt_negTwoRicci g x
  rw [hRic, traceMetricVariationAt_smul,
    traceMetricVariationAt_inner_eq_dimension]

/-- In nonzero dimension, the normalized Ricci speed has the expected
pointwise trace `2 (meanScalar - scalar)`. -/
theorem traceMetricVariationAt_normalizedRicciFlowRHSAt_eq_two_mul_centeredScalar
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (hn : (n : ℝ) ≠ 0) :
    traceMetricVariationAt g
        (fun y v w ↦ normalizedRicciFlowRHSAt g y v w) x =
      2 * (meanScalar g - g.scalarAt x) := by
  rw [traceMetricVariationAt_normalizedRicciFlowRHSAt]
  field_simp [hn]
  ring

/-- The section-tested normalized flow equation forces the pointwise metric
speed trace to be `2 (meanScalar - scalar)`. -/
theorem traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x =
      2 * (meanScalar (gt t₀) - (gt t₀).scalarAt x) := by
  calc
    traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x =
        traceMetricVariationAt (gt t₀)
          (fun y v w ↦ normalizedRicciFlowRHSAt (gt t₀) y v w) x := by
      apply traceMetricVariationAt_congr_at
      intro v w
      exact
        isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
          hflow v w
    _ = 2 * (meanScalar (gt t₀) - (gt t₀).scalarAt x) :=
      traceMetricVariationAt_normalizedRicciFlowRHSAt_eq_two_mul_centeredScalar
        (gt t₀) x hn

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Pairing the metric variation `g` itself with Ricci recovers scalar
curvature. -/
theorem metricVariationRicciPairingAt_inner_eq_scalarAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    metricVariationRicciPairingAt g (fun y v w ↦ g.inner y v w) x =
      g.scalarAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
  calc
    metricVariationRicciPairingAt g (fun y v w ↦ g.inner y v w) x =
        metricRicciPairingTraceInBasisAt g x (g.metricBilinAt x) b := by
      exact metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt
        (g := g) (h := fun y v w ↦ g.inner y v w) (x := x)
        (B := g.metricBilinAt x)
        (fun p q ↦ g.metricBilinAt_apply x p q)
        (fun p q ↦ g.inner_symm x p q) b
    _ = ∑ i, g.inner x (g.ricciEndoAt x (b i)) (sharp i) := by
      rfl
    _ = ∑ i, b.coord i (g.ricciEndoAt x (b i)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact
        (coord_eq_inner_metricDualVectorAt_of_basis
          (g := g) (x := x) (b := b) i (g.ricciEndoAt x (b i))).symm
    _ = LinearMap.trace ℝ (TM x) (g.ricciEndoAt x) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
      rfl
    _ = g.scalarAt x :=
      (g.scalarAt_eq_trace_ricciEndoAt x).symm

/-- Pairing the normalized Ricci-flow right-hand side with Ricci gives the
pointwise reaction quantity `-2 |Ric|² + (2/n) meanScalar * R`. -/
theorem metricVariationRicciPairingAt_normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    metricVariationRicciPairingAt g
        (fun y v w ↦ normalizedRicciFlowRHSAt g y v w) x =
      -2 * g.ricciNormSqAt x +
        (2 / (n : ℝ)) * meanScalar g * g.scalarAt x := by
  rw [show (fun y v w ↦ normalizedRicciFlowRHSAt g y v w) =
      (fun y v w ↦
        (-2 * g.ricciAt y v w) +
          ((2 / (n : ℝ)) * meanScalar g) * g.inner y v w) by
    funext y v w
    rfl]
  rw [metricVariationRicciPairingAt_add]
  have hRic :
      metricVariationRicciPairingAt g
          (fun y v w ↦ -2 * g.ricciAt y v w) x =
        -2 * g.ricciNormSqAt x := by
    change
      metricVariationRicciPairingAt g (negTwoRicciVariationField g) x =
        -2 * g.ricciNormSqAt x
    exact metricVariationRicciPairingAt_negTwoRicci g x
  rw [hRic, metricVariationRicciPairingAt_smul,
    metricVariationRicciPairingAt_inner_eq_scalarAt]

/-- The normalized flow equation determines the Ricci pairing of its actual
metric speed. -/
theorem metricVariationRicciPairingAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) :
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
      -2 * (gt t₀).ricciNormSqAt x +
        (2 / (n : ℝ)) * meanScalar (gt t₀) * (gt t₀).scalarAt x := by
  calc
    metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        metricVariationRicciPairingAt (gt t₀)
          (fun y v w ↦ normalizedRicciFlowRHSAt (gt t₀) y v w) x := by
      apply metricVariationRicciPairingAt_congr_at
      intro v w
      exact
        isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
          hflow v w
    _ = -2 * (gt t₀).ricciNormSqAt x +
          (2 / (n : ℝ)) * meanScalar (gt t₀) * (gt t₀).scalarAt x :=
      metricVariationRicciPairingAt_normalizedRicciFlowRHSAt (gt t₀) x

/-- Contraction of a metric variation against the traceless Ricci tensor,
written using only the repository's trace and Ricci-pairing primitives. -/
noncomputable def metricVariationTracelessRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M)
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M) : ℝ :=
  metricVariationRicciPairingAt g h x -
    (g.scalarAt x / (n : ℝ)) * traceMetricVariationAt g h x

/-- The trace-free Ricci contraction of normalized Ricci-flow speed is exactly
`-2 |Ric°|²`.  In particular, the mean-scalar normalization term cancels. -/
theorem metricVariationTracelessRicciPairingAt_timeDeriv_eq_negTwo_tracelessRicciNormSqAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    metricVariationTracelessRicciPairingAt
        (gt t₀) (timeDerivAt gt t₀) x =
      -2 * (gt t₀).tracelessRicciNormSqAt x := by
  rw [metricVariationTracelessRicciPairingAt,
    metricVariationRicciPairingAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      hflow,
    traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      hflow hn]
  unfold ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt
  field_simp [hn]
  ring

/-- The normalized flow speed has nonpositive contraction against traceless
Ricci in positive dimension. -/
theorem metricVariationTracelessRicciPairingAt_timeDeriv_nonpos
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : 0 < (n : ℝ)) :
    metricVariationTracelessRicciPairingAt
        (gt t₀) (timeDerivAt gt t₀) x ≤ 0 := by
  rw [
    metricVariationTracelessRicciPairingAt_timeDeriv_eq_negTwo_tracelessRicciNormSqAt
      hflow hn.ne']
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    ((gt t₀).tracelessRicciNormSqAt_nonneg x hn)

/-- Equality in the traceless-Ricci dissipation identity occurs exactly at an
Einstein point. -/
theorem metricVariationTracelessRicciPairingAt_timeDeriv_eq_zero_iff
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : 0 < (n : ℝ)) :
    metricVariationTracelessRicciPairingAt
        (gt t₀) (timeDerivAt gt t₀) x = 0 ↔
      (gt t₀).ricciEndoAt x =
        ((gt t₀).scalarAt x / (n : ℝ)) • LinearMap.id := by
  rw [
    metricVariationTracelessRicciPairingAt_timeDeriv_eq_negTwo_tracelessRicciNormSqAt
      hflow hn.ne']
  constructor
  · intro hzero
    have htr : (gt t₀).tracelessRicciNormSqAt x = 0 := by
      linarith
    exact
      ((gt t₀).tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id
        x hn).1 htr
  · intro hEin
    have htr : (gt t₀).tracelessRicciNormSqAt x = 0 :=
      ((gt t₀).tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id
        x hn).2 hEin
    rw [htr, mul_zero]

/-- The centered scalar curvature has zero Riemannian-volume integral. -/
theorem integral_meanScalar_sub_scalarAt_eq_zero
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) :
    (∫ x, (meanScalar g - g.scalarAt x) ∂(volumeMeasure g)) = 0 := by
  let μ := volumeMeasure g
  letI : IsFiniteMeasure μ := volumeMeasure_isFiniteMeasure g
  have hvolne : μ Set.univ ≠ 0 := by
    simpa [μ] using
      (GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g)
  have hvoltop : μ Set.univ ≠ (⊤ : ℝ≥0∞) :=
    measure_ne_top μ Set.univ
  have hvolreal : (μ Set.univ).toReal ≠ 0 := by
    exact (ENNReal.toReal_ne_zero).2 ⟨hvolne, hvoltop⟩
  have hconst : Integrable (fun _ : M ↦ meanScalar g) μ :=
    integrable_const (meanScalar g)
  have hscalar : Integrable (fun x : M ↦ g.scalarAt x) μ := by
    simpa [μ] using scalarAt_integrable g
  have hmean_mul :
      meanScalar g * (μ Set.univ).toReal = totalScalar g := by
    unfold meanScalar
    exact div_mul_cancel₀ (totalScalar g) hvolreal
  rw [integral_sub hconst hscalar]
  have hconstIntegral :
      (∫ _ : M, meanScalar g ∂μ) =
        meanScalar g * (μ Set.univ).toReal := by
    rw [integral_const]
    simp [Measure.real]
    ring
  rw [hconstIntegral]
  change meanScalar g * (μ Set.univ).toReal - totalScalar g = 0
  rw [hmean_mul, sub_self]

/-- The pointwise trace supplied by a global normalized flow is integrable. -/
theorem integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    Integrable
      (fun x ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x)
      (volumeMeasure (gt t₀)) := by
  letI : IsFiniteMeasure (volumeMeasure (gt t₀)) :=
    volumeMeasure_isFiniteMeasure (gt t₀)
  have hcentered : Integrable
      (fun x : M ↦ meanScalar (gt t₀) - (gt t₀).scalarAt x)
      (volumeMeasure (gt t₀)) :=
    (integrable_const (meanScalar (gt t₀))).sub
      (scalarAt_integrable (gt t₀))
  have hscaled := hcentered.const_mul 2
  apply hscaled.congr
  exact Filter.Eventually.of_forall fun x ↦
    (traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
      (hFlow x) hn).symm

/-- The global normalized Ricci-flow equation makes the integrated metric
speed trace vanish. -/
theorem integral_traceMetricVariationAt_timeDeriv_eq_zero_of_closedNormalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    (∫ x, traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x
        ∂(volumeMeasure (gt t₀))) = 0 := by
  have hfun :
      (fun x : M ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x) =
        fun x : M ↦ 2 *
          (meanScalar (gt t₀) - (gt t₀).scalarAt x) := by
    funext x
    exact
      traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
        (hFlow x) hn
  rw [hfun, integral_const_mul,
    integral_meanScalar_sub_scalarAt_eq_zero, mul_zero]

/-- The intrinsic total-volume first variation of a normalized closed Ricci
flow vanishes at every time at which the global flow equation holds. -/
theorem totalVolumeFirstVariation_timeDeriv_eq_zero_of_closedNormalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0) :
    totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀) = 0 := by
  rw [totalVolumeFirstVariation,
    integral_traceMetricVariationAt_timeDeriv_eq_zero_of_closedNormalizedRicciFlow
      hFlow hn, mul_zero]

/-- Exact handoff to actual volume preservation.

Once a metric-family differentiation theorem identifies the derivative of
the Hausdorff-defined total volume with the intrinsic first variation proved
above, the normalized flow equation changes that derivative value to zero. -/
theorem hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hVolumeVariation :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ totalVolume (gt t)) 0 t₀ := by
  simpa [
    totalVolumeFirstVariation_timeDeriv_eq_zero_of_closedNormalizedRicciFlow
      hFlow hn] using hVolumeVariation

/-- A normalized closed Ricci flow has constant total volume once the global
Hausdorff-measure first-variation identification is available at every time. -/
theorem totalVolume_eq_of_closedNormalizedRicciFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hn : (n : ℝ) ≠ 0)
    (hVolumeVariation : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (s t : ℝ) :
    totalVolume (gt s) = totalVolume (gt t) := by
  let V : ℝ → ℝ := fun r ↦ totalVolume (gt r)
  have hzero : ∀ r : ℝ, HasDerivAt V 0 r := by
    intro r
    exact hasDerivAt_totalVolume_zero_of_closedNormalizedRicciFlow
      (hFlow r) hn (hVolumeVariation r)
  exact is_const_of_deriv_eq_zero
    (fun r ↦ (hzero r).differentiableAt)
    (fun r ↦ (hzero r).deriv) s t

end Poincare
