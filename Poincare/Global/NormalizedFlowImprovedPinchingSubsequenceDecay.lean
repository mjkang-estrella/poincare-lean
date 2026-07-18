import Poincare.Global.NormalizedFlowFiniteTimeCurvatureCompactness
import Poincare.Global.NormalizedFlowImprovedPinchingDecay

/-!
# Decay of Hamilton's pinching maximum from finite dissipation

Finite absolute normalized-flow dissipation already supplies escaping times at
which squared traceless Ricci curvature is uniformly small.  A positive scalar
lower bound converts that statement to decay of the exponent-zero pinching
maximum along the same times.  Hamilton's forward improvement makes the
maximum antitone, so decay along the escaping sample forces decay on the full
forward ray.

This removes the separate integrability hypothesis on the spatial maximum.
No limiting metric or metric compactness is used in this module.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

/-- A nonnegative antitone function on the forward ray which tends to zero
along an escaping sample tends to zero on the whole forward ray. -/
theorem tendsto_zero_of_antitoneOn_Ici_of_nonneg_of_sample
    (D : ℝ → ℝ) (sample : ℕ → ℝ)
    (hNonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ D t)
    (hAntitone : AntitoneOn D (Ici (0 : ℝ)))
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hSampleZero : Tendsto (fun i ↦ D (sample i)) atTop (nhds 0)) :
    Tendsto D atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact ha.trans_le (hNonneg t ht)
  · intro b hb
    have hsampleNonneg : ∀ᶠ i in atTop, 0 ≤ sample i :=
      hSampleAtTop.eventually (eventually_ge_atTop (0 : ℝ))
    have hsampleLt : ∀ᶠ i in atTop, D (sample i) < b :=
      hSampleZero.eventually (Iio_mem_nhds hb)
    obtain ⟨i, hiNonneg, hiLt⟩ := (hsampleNonneg.and hsampleLt).exists
    filter_upwards [eventually_ge_atTop (sample i)] with t hit
    exact (hAntitone hiNonneg (hiNonneg.trans hit) hit).trans_lt hiLt

section PinchingMaximum

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- Uniform decay of `|Ric°|²` along an escaping sequence, together with a
positive scalar lower bound, gives decay of the exponent-zero spatial
pinching maximum along the shifted sequence.  Antitonicity then upgrades this
to decay on the full forward ray. -/
theorem tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_sample
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      rho ≤ (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ)))
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < epsilon) :
    Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) := by
  let shiftedSample : ℕ → ℝ := fun i ↦ sample i - t0
  have hShiftedAtTop : Tendsto shiftedSample atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [hSampleAtTop.eventually (eventually_ge_atTop (b + t0))]
      with i hi
    dsimp only [shiftedSample]
    linarith
  have hSampleMaximumZero : Tendsto
      (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (shiftedSample i))
      atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hShiftedAtTop.eventually (eventually_ge_atTop (0 : ℝ))]
        with i hi
      have hRpos : ∀ x : M,
          0 < (gt (t0 + shiftedSample i)).scalarAt x :=
        fun x ↦ hrho.trans_le (hScalarLower (shiftedSample i) hi x)
      exact ha.trans_le <|
        tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
          gt t0 0 (shiftedSample i) hRpos
            (hQTwo (shiftedSample i) hi)
    · intro eta heta
      have hepsilon : 0 < eta * rho ^ 2 :=
        mul_pos heta (sq_pos_of_pos hrho)
      filter_upwards [hShiftedAtTop.eventually (eventually_ge_atTop (0 : ℝ)),
        hUniformSmall (eta * rho ^ 2) hepsilon] with i hi hsmall
      have htime : t0 + shiftedSample i = sample i := by
        dsimp only [shiftedSample]
        ring
      obtain ⟨xmax, hmax⟩ :=
        exists_tracelessPinchingAt_isMaxOn
          (g := gt (sample i)) 0 (by
            intro x
            simpa only [htime] using hQTwo (shiftedSample i) hi x)
      rw [tracelessPinchingMaximumTrack, htime,
        tracelessPinchingMaximumAt_eq_of_isMaxOn
          (g := gt (sample i)) 0 hmax]
      rw [(gt (sample i)).tracelessPinchingAt_eq]
      norm_num
      have hRLower : rho ≤ (gt (sample i)).scalarAt xmax := by
        simpa only [← htime] using
          hScalarLower (shiftedSample i) hi xmax
      have hRpos : 0 < (gt (sample i)).scalarAt xmax :=
        hrho.trans_le hRLower
      apply (div_lt_iff₀ (sq_pos_of_pos hRpos)).2
      calc
        (gt (sample i)).tracelessRicciNormSqAt xmax < eta * rho ^ 2 :=
          hsmall xmax
        _ ≤ eta * ((gt (sample i)).scalarAt xmax) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ hrho.le hRpos.le).2 hRLower) heta.le
  apply tendsto_zero_of_antitoneOn_Ici_of_nonneg_of_sample
    (tracelessPinchingMaximumTrack gt t0 0) shiftedSample
      _ hAntitone hShiftedAtTop hSampleMaximumZero
  intro s hs
  have hRpos : ∀ x : M, 0 < (gt (t0 + s)).scalarAt x :=
    fun x ↦ hrho.trans_le (hScalarLower s hs x)
  exact tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
    gt t0 0 s hRpos (hQTwo s hs)

/-- Finite absolute dissipation, intrinsic first-curvature-derivative bounds,
and uniform noncollapse give full exponent-zero maximum decay once Hamilton's
forward improvement supplies antitonicity.  No integrability premise on the
maximum remains. -/
theorem tracelessPinchingMaximumTrack_tendsto_zero_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_uniformNoncollapse_of_hamilton_forward_improvement
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 A B rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower gt)
    (hScalarLower : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      rho ≤ (gt (t0 + s)).scalarAt x)
    (hQCont : ∀ s ∈ Ici (0 : ℝ),
      Continuous ↿(fun tau (x : M) ↦
        (gt ((t0 + s) + tau)).tracelessPinchingAt x 0))
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hEvol : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
        gt (t0 + s) x 0
          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
    (hPin : ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt (t0 + s)) (1 / 6)) :
    Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) := by
  have hGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianMFDerivBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  obtain ⟨sample, hSampleAtTop, _hEnergyZero, hUniformSmall⟩ :=
    exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_mfderivBound
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hGradient hNoncollapse
  have hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ)) :=
    tracelessPinchingMaximumTrack_antitoneOn_of_hamilton_forward_improvement
      (gt := gt) (t0 := t0) (epsilon := (1 / 6 : ℝ)) (delta := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PinchingAlgebra.pinchedTracelessAdmissibleDelta3])
      hQCont hQTwo hEvol hPin
  exact
    tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_sample
      gt hrho hScalarLower hQTwo hAntitone sample hSampleAtTop hUniformSmall

end PinchingMaximum

end Poincare
