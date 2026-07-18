import Poincare.Global.NormalizedFlowStokesBoundaryReduction
import Poincare.Global.NormalizedFlowStationaryLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Energy-critical slices of normalized Ricci flow

The three-dimensional normalized mean-scalar identity contains both the
traceless-Ricci energy and the scalar-variance correction.  At a critical
mean-scalar slice whose scalar variance vanishes, uniqueness of the derivative
therefore forces the full traceless-Ricci energy to vanish.  The metric at that
slice is not merely an abstract limit candidate: it is stationary for the
normalized equation and is positive Einstein when its mean scalar is positive.

For the fully expanded flow theorem below, zero scalar variance also closes the
remaining spatial Stokes boundary.  Indeed it makes scalar curvature equal to
its mean everywhere, so its intrinsic Laplacian is identically zero.  Thus the
only analytic handoffs left explicit are differentiation of the moving total
scalar and total volume, together with the pointwise scalar-variation identity.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/-- Zero scalar variance is pointwise scalar homogeneity.  Continuity and full
support of Riemannian volume upgrade the integral equality to every point. -/
theorem scalarAt_eq_meanScalar_of_centeredScalarSq_integral_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hVariance :
      (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) = 0) :
    ∀ x : M, g.scalarAt x = meanScalar g := by
  have hzero : ∀ x : M, (g.scalarAt x - meanScalar g) ^ 2 = 0 :=
    (integral_volumeMeasure_eq_zero_iff_of_continuous_nonneg
      g
      (((scalarAt_continuous g).sub continuous_const).pow 2)
      (centeredScalarSq_integrable g)
      (fun x ↦ sq_nonneg (g.scalarAt x - meanScalar g))).1 hVariance
  intro x
  have hx : g.scalarAt x - meanScalar g = 0 := by
    nlinarith [hzero x]
  exact sub_eq_zero.mp hx

/-- On a zero-variance slice the primary closed-Laplacian Stokes statement for
scalar curvature is automatic, because scalar curvature is constant. -/
theorem closedLaplacianStokes_scalarAt_of_centeredScalarSq_integral_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hVariance :
      (∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g)) = 0) :
    ClosedLaplacianStokes g (fun x : M ↦ g.scalarAt x) := by
  have hScalar :=
    scalarAt_eq_meanScalar_of_centeredScalarSq_integral_eq_zero g hVariance
  have hfun : (fun x : M ↦ g.scalarAt x) = fun _ : M ↦ meanScalar g :=
    funext hScalar
  rw [hfun]
  constructor
  · have hzero :
        (fun x : M ↦ g.laplacianAt (fun _ : M ↦ meanScalar g) x) =
          fun _ : M ↦ (0 : ℝ) := by
      funext x
      exact g.laplacianAt_const (meanScalar g) x
    rw [hzero]
    exact integrable_zero M ℝ (volumeMeasure g)
  · simp_rw [g.laplacianAt_const (meanScalar g)]
    exact integral_zero M ℝ

/-- If the normalized mean-scalar energy formula supplies the derivative and
the actual derivative is zero, then its energy numerator vanishes. -/
theorem normalizedMeanScalarEnergyNumerator_eq_zero_of_meanScalar_deriv_eq_zero
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0) :
    normalizedMeanScalarEnergyNumerator (gt t₀) = 0 := by
  have hquot :
      normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀) = 0 := by
    rw [← hMeanEnergy.deriv, hCritical]
  rcases (div_eq_zero_iff.mp hquot) with hzero | hvol
  · exact hzero
  · exact (totalVolume_ne_zero (gt t₀) hvol).elim

/-- A critical normalized mean-scalar slice with zero scalar variance has zero
total traceless-Ricci energy. -/
theorem integral_tracelessRicciNormSqAt_eq_zero_of_meanScalar_energy_critical
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0) :
    (∫ x, (gt t₀).tracelessRicciNormSqAt x
      ∂(volumeMeasure (gt t₀))) = 0 := by
  have hNumerator : normalizedMeanScalarEnergyNumerator (gt t₀) = 0 :=
    normalizedMeanScalarEnergyNumerator_eq_zero_of_meanScalar_deriv_eq_zero
      hMeanEnergy hCritical
  rw [normalizedMeanScalarEnergyNumerator_three, hVariance, mul_zero, sub_zero]
    at hNumerator
  linarith

/-- The metric at an energy-critical, zero-scalar-variance slice is stationary
for the normalized Ricci-flow equation. -/
theorem normalizedRicciStationary_of_meanScalar_energy_critical
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0) :
    IsClosedNormalizedRicciStationary (gt t₀) := by
  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
  have hScalar : ∀ x : M, g.scalarAt x = meanScalar g :=
    scalarAt_eq_meanScalar_of_centeredScalarSq_integral_eq_zero g
      (by simpa [g] using hVariance)
  have hNumerator : normalizedMeanScalarEnergyNumerator g = 0 := by
    simpa [g] using
      normalizedMeanScalarEnergyNumerator_eq_zero_of_meanScalar_deriv_eq_zero
        hMeanEnergy hCritical
  have hEin : ∀ x : M, g.ricciEndoAt x =
      (g.scalarAt x / (3 : ℝ)) • LinearMap.id :=
    (normalizedMeanScalarEnergyNumerator_eq_zero_iff_einstein_of_scalarAt_eq_mean
      g (by norm_num) hScalar).1 hNumerator
  intro x u w
  have hRic :
      g.ricciAt x u w = (g.scalarAt x / 3) * g.inner x u w := by
    rw [← g.inner_ricciEndoAt x u w, hEin x]
    simp [smul_eq_mul]
  unfold normalizedRicciFlowRHSAt
  rw [hRic, hScalar x]
  ring

/-- A positive energy-critical homogeneous slice is itself a positive Einstein
metric, rather than merely supplying an abstract limiting witness. -/
theorem positiveEinsteinMetric3_of_meanScalar_energy_critical
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0)
    (hMeanPos : 0 < meanScalar (gt t₀)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_normalizedRicciStationary (gt t₀)
    (normalizedRicciStationary_of_meanScalar_energy_critical
      hMeanEnergy hCritical hVariance)
    hMeanPos

/-- The same hypotheses give Hamilton's reduced pinched-limit payload through
the automatic zero-traceless-energy endpoint.  No componentwise metric/Ricci
convergence or decay of the metric speed is assumed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_meanScalar_energy_critical
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    (hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0)
    (hMeanPos : 0 < meanScalar (gt t₀)) :
    HamiltonConvergencePinchedLimit3Core M := by
  have hEnergy :=
    integral_tracelessRicciNormSqAt_eq_zero_of_meanScalar_energy_critical
      hMeanEnergy hCritical hVariance
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    (gt t₀) hEnergy hMeanPos

/-- Fully expanded normalized-flow endpoint.  Zero scalar variance supplies
both scalar `C²` regularity and the closed-Laplacian Stokes cancellation.  A
critical mean scalar then forces the actual time slice to be stationary. -/
theorem normalizedRicciStationary_of_normalizedFlow_meanScalar_critical
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0) :
    IsClosedNormalizedRicciStationary (gt t₀) := by
  have hScalar : ∀ x : M,
      (gt t₀).scalarAt x = meanScalar (gt t₀) :=
    scalarAt_eq_meanScalar_of_centeredScalarSq_integral_eq_zero
      (gt t₀) hVariance
  have hScalar₂ : ∀ y : M,
      ContMDiffAt I3 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y := by
    intro y
    have hfun : (fun z : M ↦ (gt t₀).scalarAt z) =
        fun _ : M ↦ meanScalar (gt t₀) := funext hScalar
    rw [hfun]
    exact contMDiffAt_const
  have hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y : M ↦ (gt t₀).scalarAt y) :=
    closedLaplacianStokes_scalarAt_of_centeredScalarSq_integral_eq_zero
      (gt t₀) hVariance
  have hMeanEnergy :
      HasDerivAt (fun t ↦ meanScalar (gt t))
        (normalizedMeanScalarEnergyNumerator (gt t₀) /
          totalVolume (gt t₀)) t₀ :=
    hasDerivAt_meanScalar_of_normalizedFlow_closedLaplacianStokes
      hFlow (by norm_num) hScalar₂ hScalarVariation hStokes
        hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
  exact normalizedRicciStationary_of_meanScalar_energy_critical
    hMeanEnergy hCritical hVariance

/-- Positive mean scalar upgrades the fully expanded critical-slice theorem to
a positive Einstein metric. -/
theorem positiveEinsteinMetric3_of_normalizedFlow_meanScalar_critical
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0)
    (hMeanPos : 0 < meanScalar (gt t₀)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_normalizedRicciStationary (gt t₀)
    (normalizedRicciStationary_of_normalizedFlow_meanScalar_critical
      hFlow hScalarVariation hDifferentiateMovingTotalScalar
        hDifferentiateMovingVolume hCritical hVariance)
    hMeanPos

/-- Hamilton-convergence consequence of the fully reduced normalized energy
endpoint.  Compared with the component-convergence theorem, the metric,
Ricci, mean-scalar, and speed convergence hypotheses are all absent. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_meanScalar_critical
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀)
    (hCritical : deriv (fun t ↦ meanScalar (gt t)) t₀ = 0)
    (hVariance :
      (∫ x, ((gt t₀).scalarAt x - meanScalar (gt t₀)) ^ 2
        ∂(volumeMeasure (gt t₀))) = 0)
    (hMeanPos : 0 < meanScalar (gt t₀)) :
    HamiltonConvergencePinchedLimit3Core M := by
  rw [hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3]
  exact positiveEinsteinMetric3_of_normalizedFlow_meanScalar_critical
    hFlow hScalarVariation hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hCritical hVariance hMeanPos

section AsymptoticExtraction

/-- Zero traceless-Ricci energy makes the same metric stationary for normalized
Ricci flow.  Connected Schur rigidity supplies the one global Einstein factor;
the mean-scalar integral then identifies the normalization coefficient. -/
theorem normalizedRicciStationary_of_zero_tracelessRicci_energy
    [Nonempty M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hEnergy :
      (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) = 0) :
    IsClosedNormalizedRicciStationary g := by
  have htr : ∀ x : M, g.tracelessRicciNormSqAt x = 0 :=
    (integral_volumeMeasure_eq_zero_iff_of_continuous_nonneg
      g (tracelessRicciNormSqAt_continuous g)
      (tracelessRicciNormSqAt_integrable g)
      (fun x ↦ g.tracelessRicciNormSqAt_nonneg x (by norm_num))).1 hEnergy
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  let R₀ : ℝ := g.scalarAt x₀
  have hcurv : HasConstantSectionalCurvature3 g (R₀ / 6) :=
    hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected
      (g := g) (R₀ := R₀)
      (fun x ↦ scalarAt_mdifferentiableAt (g := g) x)
      htr ⟨x₀, rfl⟩
  have hEin : ∀ x : M, g.IsEinsteinAt (R₀ / 3) x := by
    intro x
    have hx := isEinsteinAt_of_hasConstantSectionalCurvature3 g hcurv x
    convert hx using 1 <;> ring
  have hvol : volumeMeasure g Set.univ ≠ 0 :=
    GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g
  have hmean : meanScalar g = R₀ := by
    have h := meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero
      (g := g) hEin hvol
    norm_num at h ⊢
    linarith
  intro x u w
  have hRic := (g.isEinsteinAt_iff (R₀ / 3) x).1 (hEin x) u w
  unfold normalizedRicciFlowRHSAt
  rw [hRic, hmean]
  norm_num
  ring

/-- Energy extraction along an arbitrary convergent family of time slices.

`sample` may in particular be a sequence `ℕ → ℝ`.  The three convergence
hypotheses are exactly the moving-measure compactness transports used by the
proof: total volume, traceless-Ricci energy, and scalar variance.  The exact
normalized mean-scalar identity turns decay of its derivative into decay of
the energy numerator; uniqueness of limits then forces zero traceless energy
for the candidate metric. -/
theorem integral_tracelessRicciNormSqAt_limit_eq_zero_of_normalized_energy_extraction
    {ι : Type*} {l : Filter ι} [NeBot l] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (sample : ι → ℝ)
    (hMeanDerivativeEnergy : ∀ i : ι,
      deriv (fun t ↦ meanScalar (gt t)) (sample i) =
        normalizedMeanScalarEnergyNumerator (gt (sample i)) /
          totalVolume (gt (sample i)))
    (hMeanDerivativeZero :
      Tendsto (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) l
        (nhds 0))
    (hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) l
        (nhds (totalVolume gLimit)))
    (hTracelessEnergy :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) l
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit))))
    (hScalarVariance :
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) l (nhds 0)) :
    (∫ x, gLimit.tracelessRicciNormSqAt x
      ∂(volumeMeasure gLimit)) = 0 := by
  have hNumeratorEq :
      (fun i : ι ↦ normalizedMeanScalarEnergyNumerator (gt (sample i))) =
        fun i ↦
          deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i)) := by
    funext i
    calc
      normalizedMeanScalarEnergyNumerator (gt (sample i)) =
          (normalizedMeanScalarEnergyNumerator (gt (sample i)) /
              totalVolume (gt (sample i))) *
            totalVolume (gt (sample i)) :=
        (div_mul_cancel₀ _ (totalVolume_ne_zero (gt (sample i)))).symm
      _ = deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i)) := by
        rw [hMeanDerivativeEnergy i]
  have hNumeratorZero :
      Tendsto
        (fun i ↦ normalizedMeanScalarEnergyNumerator (gt (sample i))) l
        (nhds 0) := by
    rw [hNumeratorEq]
    simpa using hMeanDerivativeZero.mul hVolume
  have hTwoEnergy :
      Tendsto
        (fun i ↦ 2 *
          (∫ x, (gt (sample i)).tracelessRicciNormSqAt x
            ∂(volumeMeasure (gt (sample i))))) l
        (nhds (2 *
          (∫ x, gLimit.tracelessRicciNormSqAt x
            ∂(volumeMeasure gLimit)))) :=
    tendsto_const_nhds.mul hTracelessEnergy
  have hThirdVariance :
      Tendsto
        (fun i ↦ (1 / 3 : ℝ) *
          (∫ x,
            ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
            ∂(volumeMeasure (gt (sample i))))) l (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hScalarVariance :
      Tendsto
        (fun i : ι ↦ (1 / 3 : ℝ) *
          (∫ x,
            ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
            ∂(volumeMeasure (gt (sample i))))) l
        (nhds ((1 / 3 : ℝ) * 0)))
  have hNumeratorEnergy :
      Tendsto
        (fun i ↦ normalizedMeanScalarEnergyNumerator (gt (sample i))) l
        (nhds (2 *
          (∫ x, gLimit.tracelessRicciNormSqAt x
            ∂(volumeMeasure gLimit)))) := by
    simpa only [normalizedMeanScalarEnergyNumerator_three, sub_zero] using
      hTwoEnergy.sub hThirdVariance
  have hzero :
      2 * (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) = 0 :=
    tendsto_nhds_unique hNumeratorEnergy hNumeratorZero
  linarith

/-- The candidate metric in an energy-extracted family is stationary. -/
theorem normalizedRicciStationary_of_normalized_energy_extraction
    {ι : Type*} {l : Filter ι} [NeBot l] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (sample : ι → ℝ)
    (hMeanDerivativeEnergy : ∀ i : ι,
      deriv (fun t ↦ meanScalar (gt t)) (sample i) =
        normalizedMeanScalarEnergyNumerator (gt (sample i)) /
          totalVolume (gt (sample i)))
    (hMeanDerivativeZero :
      Tendsto (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) l
        (nhds 0))
    (hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) l
        (nhds (totalVolume gLimit)))
    (hTracelessEnergy :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) l
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit))))
    (hScalarVariance :
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) l (nhds 0)) :
    IsClosedNormalizedRicciStationary gLimit :=
  normalizedRicciStationary_of_zero_tracelessRicci_energy gLimit
    (integral_tracelessRicciNormSqAt_limit_eq_zero_of_normalized_energy_extraction
      sample hMeanDerivativeEnergy hMeanDerivativeZero hVolume
        hTracelessEnergy hScalarVariance)

/-- Componentwise metric, Ricci, and mean-scalar convergence transports the
normalized right-hand side to the right-hand side of the candidate metric.
This is the speed-free form of the transport lemma used by
`NormalizedRicciFlowComponentConvergence`. -/
theorem tendsto_normalizedRicciFlowRHSAt_of_three_component_tendsto
    {ι : Type*} {l : Filter ι}
    {gι : ι → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun i ↦ (gι i).inner x u w) l
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun i ↦ (gι i).ricciAt x u w) l
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun i ↦ meanScalar (gι i)) l
      (nhds (meanScalar gLimit)))
    (x : M) (u w : TM3 x) :
    Tendsto (fun i ↦ normalizedRicciFlowRHSAt (gι i) x u w) l
      (nhds (normalizedRicciFlowRHSAt gLimit x u w)) := by
  have hRic :
      Tendsto (fun i ↦ (-2 : ℝ) * (gι i).ricciAt x u w) l
        (nhds ((-2 : ℝ) * gLimit.ricciAt x u w)) :=
    tendsto_const_nhds.mul (hRicci x u w)
  have hMeanScaled :
      Tendsto (fun i ↦ (2 / (3 : ℝ)) * meanScalar (gι i)) l
        (nhds ((2 / (3 : ℝ)) * meanScalar gLimit)) :=
    tendsto_const_nhds.mul hMean
  have hMeanMetric := hMeanScaled.mul (hMetric x u w)
  simpa [normalizedRicciFlowRHSAt] using hRic.add hMeanMetric

/-- The asymptotic energy extraction replaces the independent speed field in
`NormalizedRicciFlowComponentConvergence`. -/
theorem normalizedRicciFlowComponentConvergence_of_energy_extraction
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hMeanDerivativeEnergy : ∀ t : ℝ,
      deriv (fun s ↦ meanScalar (gt s)) t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t))
    (hMeanDerivativeZero :
      Tendsto (fun t ↦ deriv (fun s ↦ meanScalar (gt s)) t) atTop
        (nhds 0))
    (hVolume : Tendsto (fun t ↦ totalVolume (gt t)) atTop
      (nhds (totalVolume gLimit)))
    (hTracelessEnergy :
      Tendsto
        (fun t ↦ ∫ x, (gt t).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t))) atTop
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit))))
    (hScalarVariance :
      Tendsto
        (fun t ↦ ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t))) atTop (nhds 0)) :
    NormalizedRicciFlowComponentConvergence gt gLimit := by
  have hStationary : IsClosedNormalizedRicciStationary gLimit :=
    normalizedRicciStationary_of_normalized_energy_extraction
      (l := atTop) (fun t : ℝ ↦ t) hMeanDerivativeEnergy
        hMeanDerivativeZero hVolume hTracelessEnergy hScalarVariance
  refine ⟨hMetric, hRicci, hMean, ?_⟩
  intro x u w
  have hRHS :=
    tendsto_normalizedRicciFlowRHSAt_of_three_component_tendsto
      (gι := gt) hMetric hRicci hMean x u w
  simpa [hStationary x u w] using hRHS

/-- Along a sampled normalized flow, the same extraction hypotheses force the
actual metric time derivative to vanish in the limit. -/
theorem tendsto_timeDerivAt_zero_of_normalized_energy_extraction
    {ι : Type*} {l : Filter ι} [NeBot l] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (sample : ι → ℝ)
    (hFlow : ∀ (i : ι) (x : M),
      IsClosedNormalizedRicciFlowSolutionAt gt (sample i) x)
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun i ↦ (gt (sample i)).inner x u w) l
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun i ↦ (gt (sample i)).ricciAt x u w) l
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun i ↦ meanScalar (gt (sample i))) l
      (nhds (meanScalar gLimit)))
    (hMeanDerivativeEnergy : ∀ i : ι,
      deriv (fun t ↦ meanScalar (gt t)) (sample i) =
        normalizedMeanScalarEnergyNumerator (gt (sample i)) /
          totalVolume (gt (sample i)))
    (hMeanDerivativeZero :
      Tendsto (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) l
        (nhds 0))
    (hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) l
        (nhds (totalVolume gLimit)))
    (hTracelessEnergy :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) l
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit))))
    (hScalarVariance :
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) l (nhds 0))
    (x : M) (u w : TM3 x) :
    Tendsto (fun i ↦ timeDerivAt gt (sample i) x u w) l (nhds 0) := by
  have hStationary : IsClosedNormalizedRicciStationary gLimit :=
    normalizedRicciStationary_of_normalized_energy_extraction
      sample hMeanDerivativeEnergy hMeanDerivativeZero hVolume
        hTracelessEnergy hScalarVariance
  have hRHS :
      Tendsto
        (fun i ↦ normalizedRicciFlowRHSAt (gt (sample i)) x u w) l
        (nhds 0) := by
    have h := tendsto_normalizedRicciFlowRHSAt_of_three_component_tendsto
      (gι := fun i ↦ gt (sample i)) hMetric hRicci hMean x u w
    simpa [hStationary x u w] using h
  apply hRHS.congr'
  exact Eventually.of_forall fun i ↦
    (isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
      (hFlow i x) u w).symm

/-- Hamilton's reduced limit follows without an independently assumed
asymptotic-speed field: exact normalized energy evolution, decay of the mean
derivative and scalar variance, and the three explicit compactness transports
construct that field automatically. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalized_energy_extraction
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hMeanDerivativeEnergy : ∀ t : ℝ,
      deriv (fun s ↦ meanScalar (gt s)) t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t))
    (hMeanDerivativeZero :
      Tendsto (fun t ↦ deriv (fun s ↦ meanScalar (gt s)) t) atTop
        (nhds 0))
    (hVolume : Tendsto (fun t ↦ totalVolume (gt t)) atTop
      (nhds (totalVolume gLimit)))
    (hTracelessEnergy :
      Tendsto
        (fun t ↦ ∫ x, (gt t).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t))) atTop
        (nhds (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit))))
    (hScalarVariance :
      Tendsto
        (fun t ↦ ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t))) atTop (nhds 0))
    (hMeanPos : 0 < meanScalar gLimit) :
    HamiltonConvergencePinchedLimit3Core M :=
  hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_componentConvergence
    (normalizedRicciFlowComponentConvergence_of_energy_extraction
      hMetric hRicci hMean hMeanDerivativeEnergy hMeanDerivativeZero
        hVolume hTracelessEnergy hScalarVariance)
    hMeanPos

end AsymptoticExtraction

section FiniteDissipationExtraction

/-- The nonnegative dissipation used to select asymptotically critical time
slices.  It records both the derivative of normalized mean scalar curvature
and the scalar-curvature variance. -/
def normalizedMeanScalarVarianceDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ :=
  deriv (fun s ↦ meanScalar (gt s)) t +
    ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
      ∂(volumeMeasure (gt t))

/-- Scalar-curvature variance is nonnegative on every time slice. -/
theorem centeredScalarSqIntegral_nonneg
    (g : ClosedSmoothRiemannianMetric 3 M) :
    0 ≤ ∫ x, (g.scalarAt x - meanScalar g) ^ 2 ∂(volumeMeasure g) :=
  integral_nonneg fun x ↦ sq_nonneg (g.scalarAt x - meanScalar g)

/-- Finite combined dissipation selects an escaping sequence of time slices
on which both summands vanish.  Bounded monotonicity simultaneously identifies
the mean-scalar limit, so no independent convergence assumption for the mean
is needed along the selected sequence.

Continuity of the dissipation is the explicit point-selection hypothesis: it
upgrades decay of its integrals over unit intervals to decay at one point of
each interval. -/
theorem exists_meanScalar_deriv_and_variance_tendsto_zero_of_finite_dissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto (fun i ↦ meanScalar (gt (sample i))) atTop
        (nhds (⨆ t : ℝ, meanScalar (gt t))) := by
  let D : ℝ → ℝ := normalizedMeanScalarVarianceDissipation gt
  have hSelect : ∀ n : ℕ, ∃ c : ℝ,
      c ∈ uIcc (n : ℝ) ((n : ℝ) + 1) ∧
        (∫ t in (n : ℝ)..((n : ℝ) + 1), D t) = D c := by
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hIntervalSubset : uIcc (n : ℝ) ((n : ℝ) + 1) ⊆ Ici (0 : ℝ) := by
      rw [uIcc_of_le hn]
      intro t ht
      exact (Nat.cast_nonneg n).trans ht.1
    obtain ⟨c, hc, hmean⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg
        (hDissipationContinuous.mono hIntervalSubset)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (1 : ℝ)))
        (fun _ _ ↦ zero_le_one)
    refine ⟨c, hc, ?_⟩
    simpa only [mul_one, intervalIntegral.integral_const, sub_self, add_sub_cancel_left,
      one_smul] using hmean
  choose sample hsample hsampleMean using hSelect
  have hsampleLower : ∀ n : ℕ, (n : ℝ) ≤ sample n := by
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    simpa only [min_eq_left hn] using (hsample n).1
  have hsampleAtTop : Tendsto sample atTop atTop :=
    tendsto_atTop_mono hsampleLower tendsto_natCast_atTop_atTop
  have hNatAddAtTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hTail :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici (n : ℝ), D t) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_natCast_atTop_atTop
  have hTailAdd :
      Tendsto (fun n : ℕ ↦ ∫ t in Ici ((n : ℝ) + 1), D t) atTop
        (nhds 0) :=
    tendsto_integral_Ici_zero hNatAddAtTop
  have hUnitIntegral :
      Tendsto (fun n : ℕ ↦ ∫ t in (n : ℝ)..((n : ℝ) + 1), D t) atTop
        (nhds 0) := by
    have hTailDiff := hTail.sub hTailAdd
    have hEq : ∀ n : ℕ,
        (∫ t in Ici (n : ℝ), D t) -
            (∫ t in Ici ((n : ℝ) + 1), D t) =
          ∫ t in (n : ℝ)..((n : ℝ) + 1), D t := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      exact intervalIntegral.integral_Ici_sub_Ici'
        (hFiniteDissipation.mono_set (Ici_subset_Ici.2 hn0))
        (hFiniteDissipation.mono_set (Ici_subset_Ici.2 hn1))
    simpa only [sub_zero] using hTailDiff.congr' (Eventually.of_forall hEq)
  have hDissipationZero : Tendsto (fun n ↦ D (sample n)) atTop (nhds 0) :=
    hUnitIntegral.congr' <|
      Eventually.of_forall fun n ↦ hsampleMean n
  have hDerivativeNonneg : ∀ n : ℕ,
      0 ≤ deriv (fun t ↦ meanScalar (gt t)) (sample n) :=
    fun _ ↦ hMeanMono.deriv_nonneg
  have hVarianceNonneg : ∀ n : ℕ,
      0 ≤ ∫ x,
        ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
        ∂(volumeMeasure (gt (sample n))) :=
    fun n ↦ centeredScalarSqIntegral_nonneg (gt (sample n))
  have hDerivativeLe : ∀ n : ℕ,
      deriv (fun t ↦ meanScalar (gt t)) (sample n) ≤ D (sample n) := by
    intro n
    dsimp only [D, normalizedMeanScalarVarianceDissipation]
    linarith [hVarianceNonneg n]
  have hVarianceLe : ∀ n : ℕ,
      (∫ x, ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
        ∂(volumeMeasure (gt (sample n)))) ≤ D (sample n) := by
    intro n
    dsimp only [D, normalizedMeanScalarVarianceDissipation]
    linarith [hDerivativeNonneg n]
  have hDerivativeZero :
      Tendsto
        (fun n ↦ deriv (fun t ↦ meanScalar (gt t)) (sample n)) atTop
        (nhds 0) :=
    squeeze_zero hDerivativeNonneg hDerivativeLe hDissipationZero
  have hVarianceZero :
      Tendsto
        (fun n ↦ ∫ x,
          ((gt (sample n)).scalarAt x - meanScalar (gt (sample n))) ^ 2
          ∂(volumeMeasure (gt (sample n)))) atTop (nhds 0) :=
    squeeze_zero hVarianceNonneg hVarianceLe hDissipationZero
  have hMeanLimit :
      Tendsto (fun t ↦ meanScalar (gt t)) atTop
        (nhds (⨆ t : ℝ, meanScalar (gt t))) :=
    tendsto_atTop_ciSup hMeanMono hMeanBdd
  exact ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero,
    hMeanLimit.comp hsampleAtTop⟩

/-- On the finite-dissipation sequence, the exact three-dimensional normalized
mean-scalar identity and constant total volume also force the full
traceless-Ricci energy to vanish.  Thus derivative, scalar variance, and Ricci
energy decay are obtained together, with no independent energy-decay input. -/
theorem exists_normalized_energy_tendsto_zero_of_finite_dissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hMeanDerivativeEnergy : ∀ t : ℝ,
      deriv (fun s ↦ meanScalar (gt s)) t =
        normalizedMeanScalarEnergyNumerator (gt t) / totalVolume (gt t))
    (hVolumeConstant : ∀ t : ℝ,
      totalVolume (gt t) = totalVolume (gt 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto (fun i ↦ meanScalar (gt (sample i))) atTop
        (nhds (⨆ t : ℝ, meanScalar (gt t))) := by
  obtain ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero, hMeanLimit⟩ :=
    exists_meanScalar_deriv_and_variance_tendsto_zero_of_finite_dissipation
      gt hMeanMono hMeanBdd hDissipationContinuous hFiniteDissipation
  have hVolume :
      Tendsto (fun i ↦ totalVolume (gt (sample i))) atTop
        (nhds (totalVolume (gt 0))) := by
    simpa only [hVolumeConstant] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ totalVolume (gt 0)) atTop
          (nhds (totalVolume (gt 0))))
  have hNumeratorZero :
      Tendsto
        (fun i ↦ normalizedMeanScalarEnergyNumerator (gt (sample i))) atTop
        (nhds 0) := by
    have hEq : ∀ i : ℕ,
        normalizedMeanScalarEnergyNumerator (gt (sample i)) =
          deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i)) := by
      intro i
      calc
        normalizedMeanScalarEnergyNumerator (gt (sample i)) =
            (normalizedMeanScalarEnergyNumerator (gt (sample i)) /
                totalVolume (gt (sample i))) *
              totalVolume (gt (sample i)) :=
          (div_mul_cancel₀ _ (totalVolume_ne_zero (gt (sample i)))).symm
        _ = deriv (fun t ↦ meanScalar (gt t)) (sample i) *
              totalVolume (gt (sample i)) := by
          rw [hMeanDerivativeEnergy (sample i)]
    have hProductZero :
        Tendsto
          (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i) *
            totalVolume (gt (sample i))) atTop (nhds 0) := by
      simpa only [zero_mul] using hDerivativeZero.mul hVolume
    exact hProductZero.congr' <|
      Eventually.of_forall fun i ↦ (hEq i).symm
  have hTwoEnergyZero :
      Tendsto
        (fun i ↦ 2 *
          (∫ x, (gt (sample i)).tracelessRicciNormSqAt x
            ∂(volumeMeasure (gt (sample i))))) atTop (nhds 0) := by
    have hThirdVarianceZero :
        Tendsto
          (fun i ↦ (1 / 3 : ℝ) *
            (∫ x,
              ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
              ∂(volumeMeasure (gt (sample i))))) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hVarianceZero :
        Tendsto
          (fun i : ℕ ↦ (1 / 3 : ℝ) *
            (∫ x,
              ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
              ∂(volumeMeasure (gt (sample i))))) atTop
          (nhds ((1 / 3 : ℝ) * 0)))
    have hSumZero := hNumeratorZero.add hThirdVarianceZero
    simpa only [normalizedMeanScalarEnergyNumerator_three, sub_add_cancel,
      zero_add] using
      hSumZero
  have hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) := by
    have hHalf :
        Tendsto
          (fun i : ℕ ↦ (2 : ℝ)⁻¹ *
            (2 * (∫ x, (gt (sample i)).tracelessRicciNormSqAt x
              ∂(volumeMeasure (gt (sample i)))))) atTop
          (nhds ((2 : ℝ)⁻¹ * 0)) :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (2 : ℝ)⁻¹) atTop (nhds (2 : ℝ)⁻¹)).mul
          hTwoEnergyZero
    simpa only [← mul_assoc, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      one_mul, mul_zero] using hHalf
  exact ⟨sample, hsampleAtTop, hDerivativeZero, hVarianceZero, hEnergyZero,
    hMeanLimit⟩

/-- Fully expanded normalized-flow version of the finite-dissipation
extraction.  The flow equation and the two moving-integral differentiation
identifications supply both the exact mean-scalar energy identity and constant
total volume, so neither is retained as an independent asymptotic hypothesis. -/
theorem exists_normalizedFlow_energy_tendsto_zero_of_finite_dissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeanMono : Monotone (fun t ↦ meanScalar (gt t)))
    (hMeanBdd : BddAbove (Set.range fun t ↦ meanScalar (gt t)))
    (hDissipationContinuous :
      ContinuousOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarVarianceDissipation gt) (Ici 0)) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ deriv (fun t ↦ meanScalar (gt t)) (sample i)) atTop
        (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto (fun i ↦ meanScalar (gt (sample i))) atTop
        (nhds (⨆ t : ℝ, meanScalar (gt t))) := by
  apply exists_normalized_energy_tendsto_zero_of_finite_dissipation
    gt hMeanMono hMeanBdd hDissipationContinuous hFiniteDissipation
  · intro t
    exact (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
      (hFlow t) (by norm_num) (hDifferentiateMovingTotalScalar t)
        (hDifferentiateMovingVolume t)).deriv
  · intro t
    exact totalVolume_eq_of_closedNormalizedRicciFlow
      hFlow (by norm_num) hDifferentiateMovingVolume t 0

end FiniteDissipationExtraction

end Poincare
