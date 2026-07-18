import Poincare.Global.NormalizedFlowAbsoluteDissipation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite absolute dissipation gives an actual mean-scalar limit

The absolute-dissipation integrand dominates the norm of the time derivative
of the mean scalar.  Hence finite absolute dissipation gives finite total
variation of the mean scalar on the positive time ray.  The improper-integral
fundamental theorem then supplies a genuine finite limit at `+∞`.

The last part of the file uses that limit to replace the smooth sequential
compactness boundary by a strictly weaker, two-dimensional closed-range
condition: it is enough that the set of attainable pairs
`(mean scalar, total traceless-Ricci energy)` is closed in `ℝ × ℝ`.
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

/-- The canonical finite limit selected by finite total variation of the mean
scalar on the positive time ray. -/
def normalizedMeanScalarLimit
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) : ℝ :=
  limUnder atTop (fun t ↦ meanScalar (gt t))

/-- Finite absolute dissipation makes the mean-scalar derivative integrable
on the nonnegative time ray. -/
theorem integrableOn_deriv_meanScalar_of_finite_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    IntegrableOn (deriv fun t ↦ meanScalar (gt t)) (Ici 0) := by
  apply hFiniteDissipation.mono'
    (aestronglyMeasurable_deriv (fun t ↦ meanScalar (gt t))
      (MeasureTheory.volume.restrict (Ici 0)))
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t _ht
  unfold normalizedMeanScalarAbsoluteVarianceDissipation
  exact le_add_of_nonneg_right (centeredScalarSqIntegral_nonneg (gt t))

/-- A differentiable mean scalar with finite absolute dissipation converges to
the canonical finite limit at `+∞`. -/
theorem tendsto_meanScalar_normalizedMeanScalarLimit_of_finite_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanDeriv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ meanScalar (gt s))
        (deriv (fun s ↦ meanScalar (gt s)) t) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (normalizedMeanScalarLimit gt)) := by
  exact tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hMeanDeriv <|
    (integrableOn_deriv_meanScalar_of_finite_absoluteDissipation
      gt hFiniteDissipation).mono_set Ioi_subset_Ici_self

/-- The normalized flow equation and the two moving-integral derivative
identifications automatically supply the differentiability needed for the
finite mean-scalar limit. -/
theorem tendsto_meanScalar_normalizedMeanScalarLimit_of_normalizedFlow_finiteAbsoluteDissipation
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
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
    Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (normalizedMeanScalarLimit gt)) := by
  apply
    tendsto_meanScalar_normalizedMeanScalarLimit_of_finite_absoluteDissipation
      gt
  · intro t _ht
    exact (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
      (hFlow t) (by norm_num) (hDifferentiateMovingTotalScalar t)
        (hDifferentiateMovingVolume t)).differentiableAt.hasDerivAt
  · exact hFiniteDissipation

/-- Quantitative tail control: the error from the limiting mean scalar is at
most the remaining absolute dissipation. -/
theorem abs_meanScalar_sub_normalizedMeanScalarLimit_le_tail_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanDeriv : ∀ t : ℝ,
      HasDerivAt (fun s ↦ meanScalar (gt s))
        (deriv (fun s ↦ meanScalar (gt s)) t) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    |meanScalar (gt t) - normalizedMeanScalarLimit gt| ≤
      ∫ s in Ioi t, normalizedMeanScalarAbsoluteVarianceDissipation gt s := by
  let f : ℝ → ℝ := fun s ↦ meanScalar (gt s)
  let D : ℝ → ℝ := normalizedMeanScalarAbsoluteVarianceDissipation gt
  have hDerivIntegrableIci : IntegrableOn (deriv f) (Ici 0) :=
    integrableOn_deriv_meanScalar_of_finite_absoluteDissipation
      gt hFiniteDissipation
  have hDerivIntegrable : IntegrableOn (deriv f) (Ioi t) :=
    hDerivIntegrableIci.mono_set <| by
      intro s hs
      exact ht.trans hs.le
  have hDIntegrable : IntegrableOn D (Ioi t) :=
    hFiniteDissipation.mono_set <| by
      intro s hs
      exact ht.trans hs.le
  have hMeanTendsto : Tendsto f atTop (nhds (normalizedMeanScalarLimit gt)) :=
    tendsto_meanScalar_normalizedMeanScalarLimit_of_finite_absoluteDissipation
      gt (fun s _hs ↦ hMeanDeriv s) hFiniteDissipation
  have hIntegral :
      (∫ s in Ioi t, deriv f s) = normalizedMeanScalarLimit gt - f t :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun s _hs ↦ hMeanDeriv s) hDerivIntegrable hMeanTendsto
  calc
    |meanScalar (gt t) - normalizedMeanScalarLimit gt| =
        ‖∫ s in Ioi t, deriv f s‖ := by
          rw [hIntegral]
          simp only [f, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ ∫ s in Ioi t, ‖deriv f s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi t, D s := by
      apply setIntegral_mono_on hDerivIntegrable.norm hDIntegrable measurableSet_Ioi
      intro s _hs
      dsimp only [f, D]
      rw [Real.norm_eq_abs]
      unfold normalizedMeanScalarAbsoluteVarianceDissipation
      exact le_add_of_nonneg_right (centeredScalarSqIntegral_nonneg (gt s))

/-- Exponential absolute-dissipation decay gives an explicit exponential
convergence rate for the mean scalar. -/
theorem abs_meanScalar_sub_normalizedMeanScalarLimit_le_of_exponential_absoluteDissipation
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanDeriv : ∀ t : ℝ,
      HasDerivAt (fun s ↦ meanScalar (gt s))
        (deriv (fun s ↦ meanScalar (gt s)) t) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    {C rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t)
    (hDecay : ∀ s ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt s ≤
        C * Real.exp ((-rate) * s)) :
    |meanScalar (gt t) - normalizedMeanScalarLimit gt| ≤
      C * Real.exp ((-rate) * t) / rate := by
  have hTail :=
    abs_meanScalar_sub_normalizedMeanScalarLimit_le_tail_absoluteDissipation
      gt hMeanDeriv hFiniteDissipation ht
  have hDIntegrable : IntegrableOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ioi t) :=
    hFiniteDissipation.mono_set <| by
      intro s hs
      exact ht.trans hs.le
  have hExpIntegrable : IntegrableOn
      (fun s : ℝ ↦ C * Real.exp ((-rate) * s)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith : -rate < 0) t).const_mul C
  calc
    |meanScalar (gt t) - normalizedMeanScalarLimit gt| ≤
        ∫ s in Ioi t, normalizedMeanScalarAbsoluteVarianceDissipation gt s := hTail
    _ ≤ ∫ s in Ioi t, C * Real.exp ((-rate) * s) := by
      apply setIntegral_mono_on hDIntegrable hExpIntegrable measurableSet_Ioi
      intro s hs
      exact hDecay s (ht.trans hs.le)
    _ = C * Real.exp ((-rate) * t) / rate := by
      rw [MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (by linarith : -rate < 0)]
      field_simp

/-- Finite absolute dissipation gives one escaping sequence on which the
derivative, scalar variance, and traceless-Ricci energy vanish, while the mean
scalar converges to its actual finite full-time limit. -/
theorem exists_normalizedFlow_energy_tendsto_zero_and_mean_tendsto_limit_of_finite_absoluteDissipation
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
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0)) :
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
        (nhds (normalizedMeanScalarLimit gt)) := by
  obtain ⟨sample, hsample, hDerivative, hVariance, hEnergy⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  refine ⟨sample, hsample, hDerivative, hVariance, hEnergy, ?_⟩
  exact
    (tendsto_meanScalar_normalizedMeanScalarLimit_of_normalizedFlow_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation).comp hsample

/-- The two scalar invariants needed by the energy endpoint, viewed as the
range of all smooth closed Riemannian metrics on the fixed manifold. -/
def closedMetricMeanTracelessEnergyRange : Set (ℝ × ℝ) :=
  Set.range fun g : ClosedSmoothRiemannianMetric 3 M ↦
    (meanScalar g,
      ∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g))

/-- Closedness of the attainable mean/energy range is enough to realize the
zero-energy limit selected by finite absolute dissipation.  This is weaker
than extracting a smoothly convergent subsequence of metrics. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergyRange_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsample, _hDerivative, _hVariance, hEnergy, hMean⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_and_mean_tendsto_limit_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hPair :
      Tendsto
        (fun i ↦
          (meanScalar (gt (sample i)),
            ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
              ∂(volumeMeasure (gt (sample i)))))
        atTop (nhds (normalizedMeanScalarLimit gt, 0)) :=
    hMean.prodMk_nhds hEnergy
  have hPairMem :
      (normalizedMeanScalarLimit gt, 0) ∈
        closedMetricMeanTracelessEnergyRange (M := M) :=
    hRangeClosed.mem_of_tendsto hPair <|
      Eventually.of_forall fun i ↦
        ⟨gt (sample i), rfl⟩
  obtain ⟨gLimit, hLimit⟩ := hPairMem
  have hMeanLimit : meanScalar gLimit = normalizedMeanScalarLimit gt :=
    congrArg Prod.fst hLimit
  have hEnergyLimit :
      (∫ x, gLimit.tracelessRicciNormSqAt x ∂(volumeMeasure gLimit)) = 0 :=
    congrArg Prod.snd hLimit
  have hMeanLowerSample : ∀ i : ℕ, c ≤ meanScalar (gt (sample i)) := by
    intro i
    exact le_meanScalar_of_forall_le_scalarAt
      (gt (sample i)) c (hScalarLower (sample i))
  have hMeanLowerLimit : c ≤ normalizedMeanScalarLimit gt :=
    ge_of_tendsto hMean <| Eventually.of_forall hMeanLowerSample
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hEnergyLimit <| by
      rw [hMeanLimit]
      exact hc.trans_le hMeanLowerLimit

end Poincare
