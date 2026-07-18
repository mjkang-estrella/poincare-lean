import Poincare.Global.NormalizedFlowInvariantCompactness
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differential inequalities imply absolute-dissipation decay

The exponential-decay endpoint previously accepted a pointwise exponential
bound.  This file derives that bound from the standard coercive differential
inequality `D' ≤ -rate * D` by an integrating-factor argument.  Applied to the
normalized mean-scalar/variance dissipation, it yields integrability and feeds
the compact invariant-parameterization Hamilton endpoint.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- A positive-rate scalar differential inequality gives the expected
exponential upper bound. -/
theorem le_initial_mul_exp_neg_of_hasDerivAt_le_neg_mul
    (D D' : ℝ → ℝ) {rate : ℝ}
    (hDeriv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt D (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * D t)
    {t : ℝ} (ht : 0 ≤ t) :
    D t ≤ D 0 * Real.exp ((-rate) * t) := by
  let F : ℝ → ℝ := fun s ↦ Real.exp (rate * s) * D s
  let F' : ℝ → ℝ := fun s ↦
    Real.exp (rate * s) * (rate * D s + D' s)
  have hFDeriv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt F (F' s) s := by
    intro s hs
    dsimp only [F, F']
    convert (((hasDerivAt_id s).const_mul rate).exp.mul (hDeriv s hs)) using 1
    simp only [id_eq]
    ring
  have hFContinuous : ContinuousOn F (Ici (0 : ℝ)) := by
    intro s hs
    exact (hFDeriv s hs).continuousAt.continuousWithinAt
  have hFAntitone : AntitoneOn F (Ici (0 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hFContinuous
    · intro s hs
      exact (hFDeriv s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      have hsIci : s ∈ Ici (0 : ℝ) := interior_subset hs
      have hInside : rate * D s + D' s ≤ 0 := by
        linarith [hDifferentialInequality s hsIci]
      exact mul_nonpos_of_nonneg_of_nonpos
        (Real.exp_pos (rate * s)).le hInside
  have hWeighted : F t ≤ F 0 :=
    hFAntitone (by simp) ht ht
  have hWeighted' : Real.exp (rate * t) * D t ≤ D 0 := by
    simpa only [F, mul_zero, Real.exp_zero, one_mul] using hWeighted
  have hDivide : D t ≤ D 0 / Real.exp (rate * t) := by
    apply (le_div_iff₀ (Real.exp_pos (rate * t))).2
    simpa only [mul_comm] using hWeighted'
  calc
    D t ≤ D 0 / Real.exp (rate * t) := hDivide
    _ = D 0 * Real.exp ((-rate) * t) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- A coercive differential inequality for the actual absolute dissipation
automatically makes it integrable on the positive time ray. -/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  have hContinuous : ContinuousOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici (0 : ℝ)) := by
    intro t ht
    exact (hDeriv t ht).continuousAt.continuousWithinAt
  apply normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
    gt (hContinuous.aestronglyMeasurable measurableSet_Ici) hrate
  intro t ht
  exact le_initial_mul_exp_neg_of_hasDerivAt_le_neg_mul
    (normalizedMeanScalarAbsoluteVarianceDissipation gt) D'
      hDeriv hDifferentialInequality ht

/-- Fully assembled Hamilton endpoint from a differential dissipation
inequality and a compact parameterization of the two scalar invariants. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialAbsoluteDissipationDecay_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
      hFlow hHausdorff hJoint hStokes
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      metric parameter hRealize hInvariantContinuous hc hScalarLower

end Poincare
