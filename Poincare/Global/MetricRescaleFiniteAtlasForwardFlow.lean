import Poincare.Global.MetricRescaleFiniteAtlasIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Forward-time normalized rescaling through a finite inverse atlas

The all-real wrapper in `MetricRescaleFiniteAtlasIntegrals` assumes that the
scale is positive and all geometric data are available at every real time.
This module supplies the forward-flow interface on `Ici 0`.

There are two genuine endpoint issues.

* From `τ(0) = 0` and `τ'(t) = c(t)⁻¹ > 0` on the nonnegative ray, the
  time change maps that ray into itself.  This is proved by strict
  monotonicity, rather than postulated.
* `timeReparameterizedConstRescaling` is an all-real metric path and hence
  needs a positive scale at negative arguments too.  We define an explicit
  globally positive extension.  It equals `c` on `Ici 0` and, using only
  continuity of `c` at zero, is eventually equal to `c` in the full germ of
  every nonnegative time.  Consequently all two-sided derivatives at forward
  times transport to the extension.

The final wrappers require inverse-chart area formulas, nonzero base volume,
the base Ricci-flow equation, and time differentiability only at reached base
times `τ(t)` with `t ∈ Ici 0`.  A convenience form obtains the last two
items from a base flow supplied on its forward ray.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Explicit globally positive extension used to turn a forward positive
scale into the all-real scale required by the metric-path constructor.

On the forward ray it is exactly `c`.  At a negative time it replaces `c t`
by `max (c t) (c 0 / 2)`. -/
def positiveForwardScaleExtension (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then c t else max (c t) (c 0 / 2)

/-- The explicit extension is unchanged at every nonnegative time. -/
@[simp] theorem positiveForwardScaleExtension_eq_of_mem_Ici
    (c : ℝ → ℝ) {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    positiveForwardScaleExtension c t = c t := by
  rw [positiveForwardScaleExtension,
    if_pos (show (0 : ℝ) ≤ t from ht)]

/-- Forward positivity makes the explicit extension positive on all of
`Real`. -/
theorem positiveForwardScaleExtension_pos
    (c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t) :
    ∀ t : ℝ, 0 < positiveForwardScaleExtension c t := by
  intro t
  by_cases ht : 0 ≤ t
  · simpa [positiveForwardScaleExtension, ht] using hc t ht
  · rw [positiveForwardScaleExtension, if_neg ht]
    have hhalf : 0 < c 0 / 2 :=
      div_pos (hc 0 (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)))
        (by norm_num)
    exact hhalf.trans_le (le_max_right _ _)

/-- The positive extension has the same full germ as `c` at every
nonnegative time.

At a positive time this follows because nearby times remain positive.  At
zero, continuity makes `c s > c 0 / 2` for all sufficiently close negative
`s`, so the `max` branch is also equal to `c s`. -/
theorem positiveForwardScaleExtension_eventuallyEq_of_mem_Ici
    (c : ℝ → ℝ) (hc0 : 0 < c 0) (hContinuousZero : ContinuousAt c 0)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    positiveForwardScaleExtension c =ᶠ[𝓝 t] c := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with hzero | hpos
  · subst t
    have hhalf : c 0 / 2 < c 0 := by linarith
    have hevent : ∀ᶠ s in 𝓝 (0 : ℝ), c 0 / 2 < c s :=
      hContinuousZero.eventually (Ioi_mem_nhds hhalf)
    filter_upwards [hevent] with s hs
    by_cases hs0 : 0 ≤ s
    · simp [positiveForwardScaleExtension, hs0]
    · rw [positiveForwardScaleExtension, if_neg hs0,
        max_eq_left hs.le]
  · filter_upwards [Ioi_mem_nhds hpos] with s hs
    rw [positiveForwardScaleExtension,
      if_pos (show (0 : ℝ) ≤ s from
        (show (0 : ℝ) < s from hs).le)]

/-- A positive derivative `τ' = c⁻¹` makes the time change strictly
increasing on the nonnegative ray and, when `τ(0)=0`, maps that ray into
itself. -/
theorem timeReparameterization_mapsTo_Ici_of_hasDerivAt_inv_pos
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t) :
    MapsTo τ (Ici (0 : ℝ)) (Ici (0 : ℝ)) := by
  have hContinuous : ContinuousOn τ (Ici (0 : ℝ)) := by
    intro t ht
    exact (hτ t ht).continuousAt.continuousWithinAt
  have hStrict : StrictMonoOn τ (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
      hContinuous
    · intro t ht
      exact (hτ t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact inv_pos.mpr (hc t (interior_subset ht))
  intro t ht
  have hmono : τ 0 ≤ τ t :=
    hStrict.monotoneOn
      (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)) ht
      (show (0 : ℝ) ≤ t from ht)
  simpa [hτ0] using hmono

/-- The all-real metric path obtained from the explicit positive extension of
a forward positive scale. -/
def forwardTimeReparameterizedConstRescaling
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t) :
    ℝ → ClosedSmoothRiemannianMetric n M :=
  timeReparameterizedConstRescaling gt τ
    (positiveForwardScaleExtension c)
    (positiveForwardScaleExtension_pos c hc)

/-- At a forward time, the extended rescaling is exactly the rescaling by the
original factor `c t`. -/
theorem forwardTimeReparameterizedConstRescaling_apply_of_mem_Ici
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    forwardTimeReparameterizedConstRescaling gt τ c hc t =
      (gt (τ t)).constSMul (c t) (hc t ht) := by
  simp [forwardTimeReparameterizedConstRescaling,
    timeReparameterizedConstRescaling, ht]

/-- Finite-atlas mean-scalar scaling for the forward rescaling at one reached
time. -/
theorem meanScalar_forwardTimeReparameterizedConstRescaling_eq_base
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ))
    (harea : FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t ht))
    (hVolume : totalVolume (gt (τ t)) ≠ 0) :
    meanScalar (forwardTimeReparameterizedConstRescaling gt τ c hc t) =
      (c t)⁻¹ * meanScalar (gt (τ t)) := by
  rw [forwardTimeReparameterizedConstRescaling_apply_of_mem_Ici
    gt τ c hc ht]
  exact harea.meanScalar_constSMul hVolume

/-- At a forward time, the implicit scale coefficient for the positive
extension is the base-flow mean-scalar coefficient. -/
theorem forwardNormalizedRescaling_meanCoefficient_eq_base
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ))
    (harea : FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t ht))
    (hVolume : totalVolume (gt (τ t)) ≠ 0) :
    (2 / (n : ℝ)) *
        meanScalar (forwardTimeReparameterizedConstRescaling gt τ c hc t) *
          positiveForwardScaleExtension c t =
      (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
  rw [meanScalar_forwardTimeReparameterizedConstRescaling_eq_base
    C gt τ c hc ht harea hVolume]
  rw [positiveForwardScaleExtension_eq_of_mem_Ici c ht]
  calc
    (2 / (n : ℝ)) * ((c t)⁻¹ * meanScalar (gt (τ t))) * c t =
        (2 / (n : ℝ)) * meanScalar (gt (τ t)) * ((c t)⁻¹ * c t) := by
          ring
    _ = (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
      rw [inv_mul_cancel₀ (ne_of_gt (hc t ht)), mul_one]

/-- Forward normalized-rescaling wrapper with data required only at reached
base times.

The target path uses the explicit globally positive extension, but that
extension agrees with `c` in a full neighborhood of every time in `Ici 0`.
Thus the supplied two-sided scale derivative transports without changing its
value, including at time zero. -/
theorem isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_reachedBaseData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t ht))
    (hVolume : ∀ t ∈ Ici (0 : ℝ), totalVolume (gt (τ t)) ≠ 0)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt gt (τ t) x)
    (htime : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt gt (τ t) x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (forwardTimeReparameterizedConstRescaling gt τ c hc) t x := by
  have hzeroMem : (0 : ℝ) ∈ Ici (0 : ℝ) := by norm_num
  have hContinuousZero : ContinuousAt c 0 :=
    (hscaleBase 0 hzeroMem).continuousAt
  intro t ht x
  let cExt : ℝ → ℝ := positiveForwardScaleExtension c
  let hcExt : ∀ s : ℝ, 0 < cExt s :=
    positiveForwardScaleExtension_pos c hc
  have hcExtEq : cExt =ᶠ[𝓝 t] c :=
    positiveForwardScaleExtension_eventuallyEq_of_mem_Ici
      c (hc 0 hzeroMem) hContinuousZero ht
  have hscaleExt : HasDerivAt cExt
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t :=
    (hscaleBase t ht).congr_of_eventuallyEq hcExtEq
  change IsClosedNormalizedRicciFlowSolutionAt
    (timeReparameterizedConstRescaling gt τ cExt hcExt) t x
  apply
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow
      gt τ cExt hcExt
  · exact (hτ t ht).congr_deriv (by
      simp [cExt, positiveForwardScaleExtension_eq_of_mem_Ici c ht])
  · exact hscaleExt.congr_deriv
      (forwardNormalizedRescaling_meanCoefficient_eq_base
        C gt τ c hc ht (harea t ht) (hVolume t ht)).symm
  · exact hflow t ht x
  · exact htime t ht x

/-- Convenience forward wrapper when the base Ricci flow and its time
differentiability are supplied on the base forward ray.  The proved
monotonicity of `τ` shows that every reached time belongs to that ray. -/
theorem isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (harea : ∀ (t : ℝ) (ht : t ∈ Ici (0 : ℝ)),
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t ht))
    (hVolume : ∀ t ∈ Ici (0 : ℝ), totalVolume (gt (τ t)) ≠ 0)
    (hflow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt gt s x)
    (htime : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt gt s x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (forwardTimeReparameterizedConstRescaling gt τ c hc) t x := by
  have hτMaps : MapsTo τ (Ici (0 : ℝ)) (Ici (0 : ℝ)) :=
    timeReparameterization_mapsTo_Ici_of_hasDerivAt_inv_pos τ c hτ0 hc hτ
  apply
    isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_reachedBaseData
      C gt τ c hc hτ hscaleBase harea hVolume
  · intro t ht x
    exact hflow (τ t) (hτMaps ht) x
  · intro t ht x
    exact htime (τ t) (hτMaps ht) x

/-! Density-only compatibility-free interfaces.  The restricted
inverse-chart area formula is now automatic, so forward rescaling needs only
integrability of the base chart densities at reached times. -/

/-- Forward mean-scalar scaling from base density integrability alone. -/
theorem meanScalar_forwardTimeReparameterizedConstRescaling_eq_base_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ))
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : totalVolume (gt (τ t)) ≠ 0) :
    meanScalar (forwardTimeReparameterizedConstRescaling gt τ c hc t) =
      (c t)⁻¹ * meanScalar (gt (τ t)) := by
  exact meanScalar_forwardTimeReparameterizedConstRescaling_eq_base
    C gt τ c hc ht
      (FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
        C (gt (τ t)) (c t) (hc t ht) hDensity)
      hVolume

/-- The forward normalized-rescaling mean coefficient from base density
integrability alone. -/
theorem forwardNormalizedRescaling_meanCoefficient_eq_base_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ))
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : totalVolume (gt (τ t)) ≠ 0) :
    (2 / (n : ℝ)) *
        meanScalar (forwardTimeReparameterizedConstRescaling gt τ c hc t) *
          positiveForwardScaleExtension c t =
      (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
  exact forwardNormalizedRescaling_meanCoefficient_eq_base
    C gt τ c hc ht
      (FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
        C (gt (τ t)) (c t) (hc t ht) hDensity)
      hVolume

/-- Forward normalized rescaling at reached base times, with the
area-formula input replaced by base density integrability. -/
theorem isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_reachedBaseData_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (hDensity : ∀ (t : ℝ) (_ht : t ∈ Ici (0 : ℝ)),
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt (τ t)) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t ∈ Ici (0 : ℝ), totalVolume (gt (τ t)) ≠ 0)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt gt (τ t) x)
    (htime : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt gt (τ t) x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (forwardTimeReparameterizedConstRescaling gt τ c hc) t x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_reachedBaseData
      C gt τ c hc hτ hscaleBase
        (fun t ht ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
          C (gt (τ t)) (c t) (hc t ht) (hDensity t ht))
        hVolume hflow htime

/-- Forward normalized rescaling from a base forward flow, with only base
density integrability at the finite-atlas measure seam. -/
theorem isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hτ0 : τ 0 = 0)
    (hc : ∀ t ∈ Ici (0 : ℝ), 0 < c t)
    (hτ : ∀ t ∈ Ici (0 : ℝ), HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t ∈ Ici (0 : ℝ), HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (hDensity : ∀ (t : ℝ) (_ht : t ∈ Ici (0 : ℝ)),
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt (τ t)) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t ∈ Ici (0 : ℝ), totalVolume (gt (τ t)) ≠ 0)
    (hflow : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedRicciFlowSolutionAt gt s x)
    (htime : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      TimeDifferentiableAt gt s x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (forwardTimeReparameterizedConstRescaling gt τ c hc) t x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow
      C gt τ c hτ0 hc hτ hscaleBase
        (fun t ht ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
          C (gt (τ t)) (c t) (hc t ht) (hDensity t ht))
        hVolume hflow htime

end Poincare
