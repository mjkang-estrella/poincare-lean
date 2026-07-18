import Poincare.Global.NormalizedFlowConvergenceEndpoint
import Poincare.Global.MetricVariation
import Poincare.Global.ScalarMeanLowerBound

/-!
# Pointwise normalized-flow equation and convergence endpoint

The normalized closed-flow predicate is section-tested.  As for the
unnormalized equation, bump extension globalizes an arbitrary tangent vector
and converts the section-tested equation to the pointwise bilinear identity
`timeDerivAt = normalizedRicciFlowRHSAt`.

Consequently, componentwise metric/Ricci/mean-scalar convergence and decay of
the actual metric time derivative imply the reduced Hamilton limit payload;
decay of the normalized right-hand side no longer has to be assumed separately.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section PointwiseEquation

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The section-tested normalized closed Ricci-flow equation is the expected
pointwise bilinear equation on arbitrary tangent vectors. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (v w : TM x) :
    timeDerivAt gt t₀ x v w =
      normalizedRicciFlowRHSAt (gt t₀) x v w := by
  let Z : ∀ y : M, TM y := bumpExtend (n := n) (M := M) x v
  have hZ : ClosedC2TangentField Z := by
    simpa [Z] using bumpExtend_closedC2TangentField (n := n) (M := M) x v
  have hregZ : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x := by
    exact CovariantDerivative.derivRegularAt_of_contMDiff
      (cov := (gt t₀).leviCivita) hZ x
  have hregExt :
      CovariantDerivative.DerivRegularAt
        (gt t₀).leviCivita (extend E v) x :=
    CovariantDerivative.derivRegularAt_extend
      (cov := (gt t₀).leviCivita) (x := x) v
  have hflow' :=
    isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
      (gt := gt) (t₀ := t₀) (x := x) hflow
      (Z := Z) hZ hregZ w
  have htraceCongr :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregZ w =
        CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w := by
    exact ricciTraceAt_congr_of_eventuallyEq
      (cov := (gt t₀).leviCivita)
      (Z := Z) (Z' := extend E v) (x := x)
      (by simpa [Z] using (hZ x))
      (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
      hregZ hregExt
      (by simpa [Z] using
        (bumpExtend_eventuallyEq_extend (n := n) (M := M) x v))
      w
  have htrace :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
        (gt t₀).ricciAt x v w := by
    have h :=
      CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
        (cov := (gt t₀).leviCivita) (Z := extend E v) (x := x)
        (FiberBundle.contMDiffAt_extend' (k := 2) I E v) hregExt w
    calc
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hregExt w =
          (gt t₀).ricciAt x w v := by
            simpa [ClosedSmoothRiemannianMetric.ricciAt] using h
      _ = (gt t₀).ricciAt x v w := (gt t₀).ricciAt_symm x w v
  rw [htraceCongr, htrace] at hflow'
  simpa [Z, normalizedRicciFlowRHSAt] using hflow'

end PointwiseEquation

section Convergence

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [SimplyConnectedSpace M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/-- Actual normalized-flow equations plus decay of the metric time derivative
construct the asymptotic-speed field of component convergence. -/
theorem normalizedRicciFlowComponentConvergence_of_timeDerivative
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hTimeDerivative : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ timeDerivAt gt t x u w) atTop (nhds 0)) :
    NormalizedRicciFlowComponentConvergence gt gLimit := by
  refine ⟨hMetric, hRicci, hMean, ?_⟩
  intro x u w
  apply (hTimeDerivative x u w).congr'
  exact Eventually.of_forall fun t ↦
    (isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
      (hFlow t x) u w)

/-- Component convergence and decay of the actual normalized metric speed,
together with positive limiting mean scalar, imply the reduced Hamilton
pinched-limit payload. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_timeDerivativeConvergence
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hTimeDerivative : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ timeDerivAt gt t x u w) atTop (nhds 0))
    (hMeanPos : 0 < meanScalar gLimit) :
    HamiltonConvergencePinchedLimit3Core M :=
  hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_componentConvergence
    (normalizedRicciFlowComponentConvergence_of_timeDerivative
      hFlow hMetric hRicci hMean hTimeDerivative)
    hMeanPos

/-- A uniform positive lower bound for the mean scalar passes to the
componentwise limit. -/
theorem meanScalar_limit_pos_of_tendsto_of_eventually_lower
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ t in atTop, c ≤ meanScalar (gt t)) :
    0 < meanScalar gLimit :=
  hc.trans_le (ge_of_tendsto hMean hlower)

/-- The convergence endpoint with positivity supplied by an eventual uniform
mean-scalar lower bound along the normalized flow. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_timeDerivativeConvergence_of_meanLower
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hTimeDerivative : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ timeDerivAt gt t x u w) atTop (nhds 0))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ t in atTop, c ≤ meanScalar (gt t)) :
    HamiltonConvergencePinchedLimit3Core M :=
  hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_timeDerivativeConvergence
    hFlow hMetric hRicci hMean hTimeDerivative
    (meanScalar_limit_pos_of_tendsto_of_eventually_lower hMean hc hlower)

/-- The convergence endpoint with positivity supplied directly by an eventual
uniform pointwise scalar-curvature lower bound along the normalized flow. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_timeDerivativeConvergence_of_scalarLower
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {gLimit : ClosedSmoothRiemannianMetric 3 M}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hMetric : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).inner x u w) atTop
        (nhds (gLimit.inner x u w)))
    (hRicci : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ (gt t).ricciAt x u w) atTop
        (nhds (gLimit.ricciAt x u w)))
    (hMean : Tendsto (fun t ↦ meanScalar (gt t)) atTop
      (nhds (meanScalar gLimit)))
    (hTimeDerivative : ∀ (x : M) (u w : TM3 x),
      Tendsto (fun t ↦ timeDerivAt gt t x u w) atTop (nhds 0))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ᶠ t in atTop, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_timeDerivativeConvergence_of_meanLower
      hFlow hMetric hRicci hMean hTimeDerivative hc
  filter_upwards [hScalarLower] with t ht
  exact le_meanScalar_of_forall_le_scalarAt (gt t) c ht

end Convergence

end Poincare
