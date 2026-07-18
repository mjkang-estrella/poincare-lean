import Poincare.Global.NormalizedFlowScalarIntegralVariation
import Poincare.Global.RicciFlowScalarRegularity

/-!
# Closed normalized-flow Stokes-boundary reduction

The repository's Riemannian volume is Hausdorff-defined, while the current
mathlib manifold library does not expose a divergence theorem identifying the
integral of this intrinsic `laplacianAt` with zero.  The available Euclidean
box divergence theorem does not apply directly to this manifold/measure
representation.

This module therefore reduces the scalar-variation Stokes boundary to the
single primary closed-manifold statement

`∫_M Δ_g R dμ_g = 0`.

No new declaration is postulated.  `ClosedLaplacianStokes` is a named proposition carrying
exactly the integrability and zero-integral facts that a future intrinsic
divergence theorem must prove.
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

/-- Primary closed-manifold Stokes statement for the repository's intrinsic
Laplacian and Hausdorff-defined Riemannian volume. -/
def ClosedLaplacianStokes
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) : Prop :=
  Integrable (fun x : M ↦ g.laplacianAt f x) (volumeMeasure g) ∧
    (∫ x, g.laplacianAt f x ∂(volumeMeasure g)) = 0

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The scalar-variation divergence-minus-Laplacian boundary is one scalar
Laplacian once the existing double-divergence, trace-Laplacian, linearity, and
contracted-Bianchi interfaces are supplied. -/
theorem scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hTensorSub :
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap :
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hRicciLinearity :
      TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    scalarVariationStokesBoundaryAt gt t₀ x =
      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
  unfold scalarVariationStokesBoundaryAt
  rw [hTensorSub,
    tensorDoubleDivergenceAt_negTwoRicci_eq_neg_laplacian_scalar
      (gt t₀) x hRicciLinearity hBianchi,
    hTraceLap]
  ring

/-- For normalized Ricci flow, the trace-Laplacian substitution is automatic
from the pointwise trace formula and `C²` scalar regularity.  The spatially
constant mean-scalar term has zero Laplacian. -/
theorem traceMetricVariationLaplacianTimeDerivNegTwoRicciAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t₀).scalarAt z) y) :
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let R : M → ℝ := fun y ↦ g.scalarAt y
  let C : M → ℝ := fun _ ↦ 2 * meanScalar g
  have hTrace :
      (fun y : M ↦
        traceMetricVariationAt g (timeDerivAt gt t₀) y) =
        C + (-2 : ℝ) • R := by
    funext y
    rw [
      traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
        (hFlow y) hn]
    simp [C, R, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hC₂ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 C y := by
    intro y
    exact contMDiffAt_const
  have hR₂ : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 R y := by
    intro y
    simpa [R, g] using hScalar₂ y
  have hNegR₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 ((-2 : ℝ) • R) y := by
    intro y
    simpa using (contMDiffAt_const.smul (hR₂ y) :
      ContMDiffAt I 𝓘(ℝ) 2 ((fun _ : M ↦ (-2 : ℝ)) • R) y)
  change g.laplacianAt
      (fun y : M ↦ traceMetricVariationAt g (timeDerivAt gt t₀) y) x =
    -2 * g.laplacianAt R x
  rw [hTrace, g.laplacianAt_add' hC₂ hNegR₂,
    g.laplacianAt_const (2 * meanScalar g) x,
    g.laplacianAt_const_smul' (-2 : ℝ) hR₂]
  ring

section DoubleDivergenceLinearity

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Covariant differentiation is additive in the raw covariant two-tensor
field. -/
theorem covTensor2DerivAt_add_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hh : CovTensor2ExtDifferentiableAt h x)
    (hk : CovTensor2ExtDifferentiableAt k x)
    (v p q : TM x) :
    covTensor2DerivAt g (fun y a b ↦ h y a b + k y a b) x v p q =
      covTensor2DerivAt g h x v p q +
        covTensor2DerivAt g k x v p q := by
  unfold covTensor2DerivAt
  rw [show
    (fun y : M ↦
      h y (extend E p y) (extend E q y) +
        k y (extend E p y) (extend E q y)) =
      (fun y : M ↦ h y (extend E p y) (extend E q y)) +
        fun y : M ↦ k y (extend E p y) (extend E q y) by rfl]
  rw [extDerivFun_add (hh p q) (hk p q)]
  simp only [ContinuousLinearMap.add_apply]
  ring

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The divergence one-form is additive in the raw covariant two-tensor
field. -/
theorem tensorDivergenceOneFormAt_add_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hh : CovTensor2ExtDifferentiableAt h x)
    (hk : CovTensor2ExtDifferentiableAt k x)
    (w : TM x) :
    tensorDivergenceOneFormAt g
        (fun y a b ↦ h y a b + k y a b) x w =
      tensorDivergenceOneFormAt g h x w +
        tensorDivergenceOneFormAt g k x w := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDivergenceOneFormAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact covTensor2DerivAt_add_field g hh hk _ _ _

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The double divergence is additive when the two tensor fields and their
divergence one-forms have the regularity consumed by its definition. -/
theorem tensorDoubleDivergenceAt_add_field
    (g : ClosedSmoothRiemannianMetric n M)
    {h k : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hh : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hk : ∀ y : M, CovTensor2ExtDifferentiableAt k y)
    (hDiv : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ tensorDivergenceOneFormAt g h y (extend E w y)) x)
    (kDiv : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ tensorDivergenceOneFormAt g k y (extend E w y)) x) :
    tensorDoubleDivergenceAt g
        (fun y a b ↦ h y a b + k y a b) x =
      tensorDoubleDivergenceAt g h x + tensorDoubleDivergenceAt g k x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  change
    (∑ j,
      (extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g
            (fun z a c ↦ h z a c + k z a c) y (extend E (b j) y))
          x (sharp j) -
        tensorDivergenceOneFormAt g
          (fun z a c ↦ h z a c + k z a c) x
            (g.leviCivita (extend E (b j)) x (sharp j)))) =
      (∑ j,
        (extDerivFun
            (fun y : M ↦ tensorDivergenceOneFormAt g h y
              (extend E (b j) y)) x (sharp j) -
          tensorDivergenceOneFormAt g h x
            (g.leviCivita (extend E (b j)) x (sharp j)))) +
      ∑ j,
        (extDerivFun
            (fun y : M ↦ tensorDivergenceOneFormAt g k y
              (extend E (b j) y)) x (sharp j) -
          tensorDivergenceOneFormAt g k x
            (g.leviCivita (extend E (b j)) x (sharp j)))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  let F : M → ℝ := fun y ↦
    tensorDivergenceOneFormAt g h y (extend E (b j) y)
  let K : M → ℝ := fun y ↦
    tensorDivergenceOneFormAt g k y (extend E (b j) y)
  have hField :
      (fun y : M ↦ tensorDivergenceOneFormAt g
        (fun z a c ↦ h z a c + k z a c) y (extend E (b j) y)) =
        F + K := by
    funext y
    exact tensorDivergenceOneFormAt_add_field g (hh y) (hk y) _
  have hOuter :
      extDerivFun
          (fun y : M ↦ tensorDivergenceOneFormAt g
            (fun z a c ↦ h z a c + k z a c) y (extend E (b j) y))
          x (sharp j) =
        extDerivFun F x (sharp j) + extDerivFun K x (sharp j) := by
    rw [hField]
    have hadd := congrArg
      (fun L : TM x →L[ℝ] ℝ ↦ L (sharp j))
      (extDerivFun_add (hDiv (b j)) (kDiv (b j)))
    simpa [F, K] using hadd
  have hCorrection :=
    tensorDivergenceOneFormAt_add_field g (hh x) (hk x)
      (g.leviCivita (extend E (b j)) x (sharp j))
  rw [hOuter, hCorrection]
  ring

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A spatially constant multiple of the metric has zero divergence
one-form. -/
theorem tensorDivergenceOneFormAt_const_metric_eq_zero
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ)
    (x : M) (w : TM x) :
    tensorDivergenceOneFormAt g
      (fun y p q ↦ c * g.inner y p q) x w = 0 := by
  rw [tensorDivergenceOneFormAt_scalar_metric g mdifferentiableAt_const w]
  unfold extDerivFun
  simp

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A spatially constant multiple of the metric has zero double
divergence. -/
theorem tensorDoubleDivergenceAt_const_metric_eq_zero
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (x : M) :
    tensorDoubleDivergenceAt g
      (fun y p q ↦ c * g.inner y p q) x = 0 := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  unfold tensorDoubleDivergenceAt
  simp_rw [tensorDivergenceOneFormAt_const_metric_eq_zero]
  unfold extDerivFun
  simp

/-- The spatially constant normalizing multiple of the metric does not change
the double divergence.  Consequently a global normalized-flow equation
supplies the repository's existing `timeDeriv = -2 Ric` double-divergence
substitution once the Ricci divergence one-form has the regularity needed to
differentiate it. -/
theorem tensorDoubleDivergenceTimeDerivNegTwoRicciAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀)
            (ricciVariationField (gt t₀)) y (extend E w y)) x) :
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let c : ℝ := (2 / (n : ℝ)) * meanScalar g
  let hNeg : ∀ y : M, TM y → TM y → ℝ :=
    negTwoRicciVariationField g
  let hConst : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ c * g.inner y p q
  have hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField g) y :=
    fun y ↦ covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y
  have hNegDiff : ∀ y : M, CovTensor2ExtDifferentiableAt hNeg y := by
    intro y p q
    have hscaled : MDifferentiableAt I 𝓘(ℝ)
        (fun z : M ↦ (-2 : ℝ) *
          ricciVariationField g z (extend E p z) (extend E q z)) y :=
      mdifferentiableAt_const.mul (hRicDiff y p q)
    simpa [hNeg, negTwoRicciVariationField, ricciVariationField] using hscaled
  have hConstDiff : ∀ y : M, CovTensor2ExtDifferentiableAt hConst y := by
    intro y p q
    have hp := mdifferentiableAt_extend I E p
    have hq := mdifferentiableAt_extend I E q
    have hmetric := g.metric_pairing_mdiffAt hp hq
    have hscaled : MDifferentiableAt I 𝓘(ℝ)
        (fun z : M ↦ c * g.inner z (extend E p z) (extend E q z)) y :=
      mdifferentiableAt_const.mul hmetric
    simpa [hConst] using hscaled
  have hNegDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt g hNeg y (extend E w y)) x := by
    intro w
    have hscaled : MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ (-2 : ℝ) *
          tensorDivergenceOneFormAt g (ricciVariationField g) y
            (extend E w y)) x :=
      mdifferentiableAt_const.mul (by simpa [g] using hRicDivDiff w)
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      change tensorDivergenceOneFormAt g
          (fun z v u ↦ (-2 : ℝ) * ricciVariationField g z v u)
            y (extend E w y) =
        (-2 : ℝ) * tensorDivergenceOneFormAt g
          (ricciVariationField g) y (extend E w y)
      exact tensorDivergenceOneFormAt_smul_field
        (g := g) (h := ricciVariationField g) (x := y)
        (hRicDiff y) (-2 : ℝ) (extend E w y)
  have hConstDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt g hConst y (extend E w y)) x := by
    intro w
    have hzero : MDifferentiableAt I 𝓘(ℝ)
        (fun _ : M ↦ (0 : ℝ)) x := mdifferentiableAt_const
    apply hzero.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y ↦ by
      exact tensorDivergenceOneFormAt_const_metric_eq_zero
        g c y (extend E w y)
  have hTimeEq :
      ∀ᶠ y in nhds x, ∀ p q : TM y,
        timeDerivAt gt t₀ y p q = hNeg y p q + hConst y p q := by
    exact Filter.Eventually.of_forall fun y p q ↦ by
      have hEq :=
        isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
          (hFlow y) p q
      simpa [g, c, hNeg, hConst, normalizedRicciFlowRHSAt,
        negTwoRicciVariationField, ricciVariationField] using hEq
  unfold TensorDoubleDivergenceTimeDerivNegTwoRicciAt
  calc
    tensorDoubleDivergenceAt g (timeDerivAt gt t₀) x =
        tensorDoubleDivergenceAt g
          (fun y p q ↦ hNeg y p q + hConst y p q) x :=
      tensorDoubleDivergenceAt_congr_of_eventuallyEq g hTimeEq
    _ = tensorDoubleDivergenceAt g hNeg x +
          tensorDoubleDivergenceAt g hConst x :=
      tensorDoubleDivergenceAt_add_field
        g hNegDiff hConstDiff hNegDivDiff hConstDivDiff
    _ = tensorDoubleDivergenceAt g hNeg x := by
      rw [show tensorDoubleDivergenceAt g hConst x = 0 by
        exact tensorDoubleDivergenceAt_const_metric_eq_zero g c x,
        add_zero]
    _ = tensorDoubleDivergenceAt g (negTwoRicciVariationField g) x := rfl

end DoubleDivergenceLinearity

/-- Under a global normalized-flow equation and `C²` scalar regularity, every
local geometric substitution in the Stokes boundary is automatic.  The
boundary is exactly `ΔR`; no separate tensor-substitution or contracted-
Bianchi premise remains. -/
theorem scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y) :
    scalarVariationStokesBoundaryAt gt t₀ x =
      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ tensorDivergenceOneFormAt g
          (ricciVariationField g) y (extend E w y)) x := by
    intro w
    exact ricciDivergenceOneForm_mdifferentiableAt_of_scalar_contMDiffAt_two
      g (by simpa [g] using hScalar₂ x) w
  have hTensorSub :
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x :=
    tensorDoubleDivergenceTimeDerivNegTwoRicciAt_of_normalizedFlow
      hFlow (by simpa [g] using hRicDivDiff)
  have hTraceLap :
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x :=
    traceMetricVariationLaplacianTimeDerivNegTwoRicciAt_of_normalizedFlow
      hFlow hn hScalar₂
  have hRicciLinearity :
      TensorDoubleDivergenceNegTwoRicciLinearityAt g x :=
    TensorDoubleDivergenceNegTwoRicciLinearityAt.of_covTensor2Regular
      g x
      (fun y ↦ covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y)
      hRicDivDiff
  have hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ g.scalarAt z) y (extend E w y)) x := by
    intro w
    have hw : MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (extend E w)) x := by
      simpa using (mdifferentiableAt_extend I E w)
    exact CovariantDerivative.mdiffAt_extDerivFun_apply
      (by simpa [g] using hScalar₂ x) hw
  have hBianchi : ClosedContractedBianchiAt g x :=
    closedContractedBianchiAt_canonical
      g x (by simpa [g] using hScalar₂ x) hScalarExt₂
  exact scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt
    hTensorSub hTraceLap (by simpa [g] using hRicciLinearity)
      (by simpa [g] using hBianchi)

/-- Global function equality version of the automatic normalized-flow
boundary reduction. -/
theorem scalarVariationStokesBoundary_eq_laplacian_scalarAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y) :
    scalarVariationStokesBoundaryAt gt t₀ =
      fun x ↦ (gt t₀).laplacianAt
        (fun y ↦ (gt t₀).scalarAt y) x := by
  funext x
  exact
    scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
      hFlow hn hScalar₂

/-- After all local geometry is discharged, the spatial scalar-variation
boundary is integrable and has zero integral from the single primary
`ClosedLaplacianStokes` statement. -/
theorem scalarVariationStokesBoundary_integrable_and_integral_eq_zero_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y)) :
    Integrable (scalarVariationStokesBoundaryAt gt t₀)
        (volumeMeasure (gt t₀)) ∧
      (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
        ∂(volumeMeasure (gt t₀))) = 0 := by
  rw [
    scalarVariationStokesBoundary_eq_laplacian_scalarAt_of_normalizedFlow
      hFlow hn hScalar₂]
  exact hStokes

/-- Total-scalar derivative with every local Stokes-boundary obligation
discharged.  The sole remaining spatial input is the primary closed-manifold
integral `ClosedLaplacianStokes`. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow_closedLaplacianStokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y))
    (hDifferentiateMovingIntegral :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀) :
    HasDerivAt (fun t ↦ totalScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀ := by
  have hBoundary :=
    scalarVariationStokesBoundary_integrable_and_integral_eq_zero_of_normalizedFlow
      hFlow hn hScalar₂ hStokes
  exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow
    hFlow hn hScalarVariation hBoundary.1 hBoundary.2
      hDifferentiateMovingIntegral

/-- Mean-scalar derivative with the local geometry and spatial Stokes
boundary reduced completely to `ClosedLaplacianStokes`.  Beyond it, only the
moving total-scalar and total-volume differentiation identifications remain. -/
theorem hasDerivAt_meanScalar_of_normalizedFlow_closedLaplacianStokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y))
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀) /
        totalVolume (gt t₀)) t₀ := by
  have hTotalScalar :=
    hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow_closedLaplacianStokes
      hFlow hn hScalar₂ hScalarVariation hStokes
        hDifferentiateMovingTotalScalar
  exact hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    hFlow hn hTotalScalar hDifferentiateMovingVolume

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Global pointwise form of the normalized scalar Stokes reduction. -/
theorem scalarVariationStokesBoundary_eq_laplacian_scalarAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hTensorSub : ∀ x : M,
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : ∀ x : M,
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hRicciLinearity : ∀ x : M,
      TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ∀ x : M, ClosedContractedBianchiAt (gt t₀) x) :
    scalarVariationStokesBoundaryAt gt t₀ =
      fun x ↦ (gt t₀).laplacianAt
        (fun y ↦ (gt t₀).scalarAt y) x := by
  funext x
  exact scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt
    (hTensorSub x) (hTraceLap x) (hRicciLinearity x) (hBianchi x)

/-- `ClosedLaplacianStokes` supplies both pieces needed by the scalar-integral
variation bridge: boundary integrability and boundary integral cancellation. -/
theorem scalarVariationStokesBoundary_integrable_and_integral_eq_zero
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hTensorSub : ∀ x : M,
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : ∀ x : M,
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hRicciLinearity : ∀ x : M,
      TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ∀ x : M, ClosedContractedBianchiAt (gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y)) :
    Integrable (scalarVariationStokesBoundaryAt gt t₀)
        (volumeMeasure (gt t₀)) ∧
      (∫ x, scalarVariationStokesBoundaryAt gt t₀ x
        ∂(volumeMeasure (gt t₀))) = 0 := by
  rw [scalarVariationStokesBoundary_eq_laplacian_scalarAt
    hTensorSub hTraceLap hRicciLinearity hBianchi]
  exact hStokes

/-- Total-scalar derivative with Stokes reduced to the primary integral of a
scalar Laplacian. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_closedLaplacianStokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hTensorSub : ∀ x : M,
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : ∀ x : M,
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hRicciLinearity : ∀ x : M,
      TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ∀ x : M, ClosedContractedBianchiAt (gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y))
    (hDifferentiateMovingIntegral :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀) :
    HasDerivAt (fun t ↦ totalScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀ := by
  have hBoundary :=
    scalarVariationStokesBoundary_integrable_and_integral_eq_zero
      hTensorSub hTraceLap hRicciLinearity hBianchi hStokes
  exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlow
    hFlow hn hScalarVariation hBoundary.1 hBoundary.2
      hDifferentiateMovingIntegral

/-- Mean-scalar derivative with the spatial Stokes theorem reduced to
`ClosedLaplacianStokes`; only the two moving-measure differentiation
identifications remain separate. -/
theorem hasDerivAt_meanScalar_of_closedLaplacianStokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hn : (n : ℝ) ≠ 0)
    (hScalarVariation : ∀ x : M,
      deriv (fun t ↦ (gt t).scalarAt x) t₀ =
        scalarVariationStokesBoundaryAt gt t₀ x -
          metricVariationRicciPairingAt
            (gt t₀) (timeDerivAt gt t₀) x)
    (hTensorSub : ∀ x : M,
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : ∀ x : M,
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hRicciLinearity : ∀ x : M,
      TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ∀ x : M, ClosedContractedBianchiAt (gt t₀) x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y))
    (hDifferentiateMovingTotalScalar :
      HasDerivAt (fun t ↦ totalScalar (gt t))
        (rawTotalScalarFirstVariation gt t₀) t₀)
    (hDifferentiateMovingVolume :
      HasDerivAt (fun t ↦ totalVolume (gt t))
        (totalVolumeFirstVariation (gt t₀) (timeDerivAt gt t₀)) t₀) :
    HasDerivAt (fun t ↦ meanScalar (gt t))
      (normalizedMeanScalarEnergyNumerator (gt t₀) /
        totalVolume (gt t₀)) t₀ := by
  have hTotalScalar :=
    hasDerivAt_totalScalar_energyNumerator_of_closedLaplacianStokes
      hFlow hn hScalarVariation hTensorSub hTraceLap hRicciLinearity
        hBianchi hStokes hDifferentiateMovingTotalScalar
  exact hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
    hFlow hn hTotalScalar hDifferentiateMovingVolume

end Poincare
