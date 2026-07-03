import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm
import Poincare.Global.RicciFlow
import Poincare.Global.ScalarVariation

/-!
# Closed-manifold scalar evolution statement

This module records the closed-manifold Hamilton scalar evolution equation in
terms of the current global vocabulary:
`scalarAt`, `laplacianAt`, `ricciNormSqAt`, and
`IsClosedRicciFlowSolutionAt`.

The full closed-manifold proof is intentionally not supplied here.  The
single-chart analogues already live in `ModelLaplacian.lean`; this file adds
the statement layer and a static Ricci-flat sanity instance.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Hamilton's scalar evolution equation at a point of a time-family of closed
smooth Riemannian metrics.

The implicit regularity instance is exactly the one required by the existing
`scalarAt` and `ricciNormSqAt` wrappers for each time-slice.
-/
def SatisfiesHamiltonScalarEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  HasDerivAt (fun t ↦ (gt t).scalarAt x)
    ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
      2 * (gt t₀).ricciNormSqAt x) t₀

/-- Unfold the closed Hamilton scalar evolution statement. -/
@[simp] theorem satisfiesHamiltonScalarEvolutionAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x ↔
      HasDerivAt (fun t ↦ (gt t).scalarAt x)
        ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
          2 * (gt t₀).ricciNormSqAt x) t₀ :=
  Iff.rfl

namespace ClosedSmoothRiemannianMetric

section StaticFlat

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- A vanishing Ricci bilinear form has zero raised Ricci endomorphism. -/
theorem ricciEndoAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciEndoAt x = 0 := by
  ext u
  simp only [LinearMap.zero_apply]
  exact LeviCivitaExistence.metric_nondegenerate g x (g.ricciEndoAt x u) fun w ↦ by
    rw [g.inner_ricciEndoAt, hric u w]

/-- A vanishing Ricci bilinear form has zero pointwise squared Ricci norm. -/
theorem ricciNormSqAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciNormSqAt x = 0 := by
  rw [g.ricciNormSqAt_eq_trace, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/-- A vanishing Ricci bilinear form has zero scalar curvature. -/
theorem scalarAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.scalarAt x = 0 := by
  rw [g.scalarAt_eq_trace_ricciEndoAt, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/--
If the Ricci bilinear form vanishes everywhere, then the scalar curvature
function is identically zero, so its Laplacian vanishes by `laplacianAt_const`.
-/
theorem laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) (x : M) :
    g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 := by
  have hscalar :
      (fun y : M ↦ g.scalarAt y) = fun _ : M ↦ 0 := by
    funext y
    exact g.scalarAt_eq_zero_of_ricciAt_eq_zero (hric y)
  rw [hscalar]
  exact g.laplacianAt_const 0 x

/-- Along a time-constant metric family, scalar curvature has zero time derivative. -/
theorem hasDerivAt_scalarAt_const (t₀ : ℝ) (x : M) :
    HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ := by
  simpa using hasDerivAt_const t₀ (g.scalarAt x)

end StaticFlat

end ClosedSmoothRiemannianMetric

/--
Static Ricci-flat closed metrics satisfy the closed Hamilton scalar evolution
equation.

The Ricci-flatness hypothesis is the genuine pointwise bilinear vanishing
needed here: it implies both `scalarAt ≡ 0` and `ricciNormSqAt = 0`.
-/
theorem hamilton_scalar_evolution_static_flat
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (t₀ : ℝ) (x : M)
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) :
    SatisfiesHamiltonScalarEvolutionAt (fun _ : ℝ ↦ g) t₀ x := by
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (((fun _ : ℝ ↦ g) t).leviCivita) 1 :=
    fun _ ↦ inferInstance
  have hderiv : HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ :=
    g.hasDerivAt_scalarAt_const t₀ x
  have hlap : g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 :=
    g.laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero hric x
  have hnorm : g.ricciNormSqAt x = 0 :=
    g.ricciNormSqAt_eq_zero (hric x)
  have hrhs : g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x = 0 := by
    rw [hlap, hnorm]
    ring
  unfold SatisfiesHamiltonScalarEvolutionAt
  rw [hrhs]
  simpa using hderiv

/--
The predicate package still needed to turn the closed scalar-variation formula
into Hamilton's scalar evolution at one spacetime point.
-/
def HamiltonScalarEvolutionPredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceAssemblyAt gt t₀ x ∧
    DeltaGammaContractionTraceAssemblyAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

/--
Variant predicate package where the two `δΓ` divergence assemblies are supplied
in Hessian-trace form.  The conversion to `HamiltonScalarEvolutionPredicatesAt`
uses only `laplacianAt_eq_sum_hessianAt`.
-/
def HamiltonScalarEvolutionHessianPredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x ∧
    DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

/--
Variant predicate package where the two Hessian assemblies are supplied by the
more local second-order trace-derivative bridges.
-/
def HamiltonScalarEvolutionTraceDerivativePredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x ∧
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

theorem hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionHessianPredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionPredicatesAt gt t₀ x := by
  rcases hPred with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact
    ⟨raise', hext, hreg, hgt, hRaise,
      deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv,
      deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩

theorem hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionTraceDerivativePredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionHessianPredicatesAt gt t₀ x := by
  rcases hPred with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact
    ⟨raise', hext, hreg, hgt, hRaise,
      deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative hDiv,
      deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩

theorem hamiltonScalarEvolutionPredicatesAt_of_traceDerivativePredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionTraceDerivativePredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionPredicatesAt gt t₀ x :=
  hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
    (hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates hPred)

/--
Hamilton scalar evolution follows from a closed Ricci-flow solution once the
closed scalar-variation predicates and contracted-Bianchi obligation are
available at the point.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hEq : ∀ v w : TM x,
      timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w :=
    fun v w ↦
      isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt hflow hext v w
  have hHas :=
    hasDerivAt_scalarAt_lichnerowicz
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hreg hgt hRaise hDiv hCon
  have hPair :
      metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        -2 * (gt t₀).ricciNormSqAt x :=
    metricVariationRicciPairingAt_timeDeriv_eq_negTwoRicci
      (gt := gt) (t₀ := t₀) (x := x) hEq
  have hTensorNeg :
      tensorDoubleDivergenceAt (gt t₀)
          (negTwoRicciVariationField (gt t₀)) x =
        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x :=
    tensorDoubleDivergenceAt_negTwoRicci_eq_neg_laplacian_scalar
      (gt t₀) x hlin hBianchi
  have hTensorTime :
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x =
        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
    rw [hTensorSub, hTensorNeg]
  have hRhs :
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
          2 * (gt t₀).ricciNormSqAt x := by
    rw [hTensorTime, hTraceLap, hPair]
    ring
  unfold SatisfiesHamiltonScalarEvolutionAt
  convert hHas using 1
  exact hRhs.symm

/--
Hamilton scalar evolution with the three algebraic substitution predicates
discharged from a Ricci-flow solution on a neighborhood of `x`.

The remaining non-algebraic curvature identity is the closed twice-contracted
Bianchi predicate; the other hypotheses are the regularity and assembly data
needed by the existing scalar-variation formula and by the Laplacian/double
divergence linearity lemmas.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hflow : IsClosedRicciFlowSolutionAt gt t₀ x :=
    (hNearFlow.self_of_nhds).1
  have hext : ClosedRicciFlowExtensionRegularAt gt t₀ x :=
    (hNearFlow.self_of_nhds).2
  have hTensorSub :
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x :=
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
      (gt := gt) (t₀ := t₀) (x := x) hNearFlow
  have hTraceLap :
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x :=
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
      (gt := gt) (t₀ := t₀) (x := x) hNearFlow
      hTraceGrad hNegScalarGrad hScalarDiff hScalarGrad
  have hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x :=
    TensorDoubleDivergenceNegTwoRicciLinearityAt.of_covTensor2Regular
      (gt t₀) x hRicDiff hRicDivDiff
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hflow hext hreg hgt hRaise hDiv hCon
      hTensorSub hTraceLap hlin hBianchi

/--
Hamilton scalar evolution for a closed Ricci-flow solution, with the closed
contracted-Bianchi identity discharged by the canonical second-Bianchi chain.

The remaining hypotheses are the regularity and scalar-variation assembly
data consumed by the existing variation formula and substitution lemmas.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalar₂ :
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t₀).scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ (gt t₀).scalarAt z) y (extend E w y)) x)
    (hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    simpa using (gt t₀).mdifferentiableAt_gradient hScalar₂
  have hBianchi : ClosedContractedBianchiAt (gt t₀) x :=
    closedContractedBianchiAt_canonical
      (g := gt t₀) (x := x) hScalar₂ hScalarExt₂
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hNearFlow hreg hgt hRaise hDiv hCon hTraceGrad hNegScalarGrad
    hScalarDiff hScalarGrad hRicDiff hRicDivDiff hBianchi

/-
Remaining hypotheses in `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'`.

* `hNearFlow`: neighborhood Ricci-flow equation plus extension regularity; used
  to substitute `timeDerivAt = -2 Ric` in the algebraic tail.
* `hNearRegExt`: neighborhood metric-flow regularity and differentiated metric
  entries in canonical extension slots; supplies `hreg` and the `hExt` witness
  for both Hessian-trace `δΓ` discharge wrappers.
* `hgt`: pointwise metric time differentiability for every nearby fiber; gives
  the actual bilinear witnesses for trace-entry regularity and supplies the
  base-point `TimeDifferentiableAt` hypothesis.
* `hRaise`: derivative of the metric-raise map at `x`; this is the remaining
  time derivative witness needed by the scalar-variation formula.
* `hBridge`: the scalar-entry derivative bridge for `δΓ`; this is the
  contraction-side canonical wrapper input.
* `hSecond`, `hTimeCovDiff`: second and first covariant differentiability of
  `timeDerivAt`; these discharge the divergence-side Hessian trace.
* `hEntries`: `C²` trace-entry regularity for `timeDerivAt`; this discharges
  the contraction-side Hessian derivative and the trace-gradient witness.
* `hScalar₂`: scalar curvature is `C²` at every point of the time-slice; this
  supplies scalar differentiability, the scalar gradient witness, and the
  canonical contracted-Bianchi scalar-extension witnesses.
* `hRicDivDiff`: differentiability of the Ricci divergence one-form at `x`;
  together with canonical Ricci tensor differentiability it supplies the
  `-2 Ric` double-divergence linearity predicate.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hNearRegExt :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hTimeCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hreg : MetricFlowRegularAt gt t₀ x :=
    (hNearRegExt.self_of_nhds).1
  have hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y))
              x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀ :=
    (hNearRegExt.self_of_nhds).2
  have hNearCon :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀) := by
    filter_upwards [hNearRegExt] with y hy
    exact ⟨hy.1, hTimeCovDiff y, hy.2⟩
  have hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x :=
    deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly
      (deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt hNearRegExt hBridge hSecond hTimeCovDiff
        (by
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
          let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
          have hTrace₂ :
              ContMDiffAt I 𝓘(ℝ) 2 f x := by
            simpa [g, H, f] using
              traceMetricVariationAt_contMDiffAt_two_of_entries
                (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
                hEntries
                (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
                (by intro y p q; rfl)
          simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂))
  have hConHessian :
      DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x :=
    deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative
      (deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt
        (gt := gt) (t₀ := t₀) (x := x)
        hBridge hreg hgt hExt hNearCon hEntries
        (by
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
          let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
          have hTrace₂ :
              ContMDiffAt I 𝓘(ℝ) 2 f x := by
            simpa [g, H, f] using
              traceMetricVariationAt_contMDiffAt_two_of_entries
                (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
                hEntries
                (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
                (by intro y p q; rfl)
          simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂))
  have hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x :=
    deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hConHessian
  have hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
    let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
    have hTrace₂ : ContMDiffAt I 𝓘(ℝ) 2 f x := by
      simpa [g, H, f] using
        traceMetricVariationAt_contMDiffAt_two_of_entries
          (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
          hEntries
          (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
          (by intro y p q; rfl)
    simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂
  have hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let f : M → ℝ := fun y ↦ g.scalarAt y
    have hNeg₂ :
        ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (-2 : ℝ) * g.scalarAt y) x := by
      have hconst :
          ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ (-2 : ℝ)) x :=
        contMDiffAt_const
      simpa [g, f, Pi.smul_apply, smul_eq_mul] using
        hconst.smul (hScalar₂ x)
    simpa [g] using (gt t₀).mdifferentiableAt_gradient hNeg₂
  have hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y :=
    fun y ↦ (hScalar₂ y).mdifferentiableAt two_ne_zero
  have hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ (gt t₀).scalarAt z) y (extend E w y)) x := by
    intro w
    have hW : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E w)) x := by
      simpa using (mdifferentiableAt_extend I E w)
    exact CovariantDerivative.mdiffAt_extDerivFun_apply (hScalar₂ x) hW
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hNearFlow hreg (hgt x) hRaise hDiv hCon hTraceGrad hNegScalarGrad
      hScalarDiff (hScalar₂ x) hScalarExt₂
      (fun y ↦
        covTensor2ExtDifferentiableAt_ricciVariationField_canonical
          (g := gt t₀) (x := y))
      hRicDivDiff

/--
Hamilton scalar evolution from the Hessian-trace form of the two `δΓ`
assemblies.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
  satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise
    (deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv)
    (deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon)
    hTensorSub hTraceLap hlin hBianchi

theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_trace_derivative_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
  satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise
    (deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative hDiv)
    (deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative hCon)
    hTensorSub hTraceLap hlin hBianchi

/-- The Ricci pinching inequality gives the Hamilton reaction lower bound. -/
theorem hamilton_scalar_reaction_bound_at
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (hn : 0 < (n : ℝ)) :
    (2 / (n : ℝ)) * g.scalarAt x ^ 2 ≤ 2 * g.ricciNormSqAt x := by
  have hpinch := g.scalarAt_sq_le_nat_mul_ricciNormSqAt x
  have hscale :=
    mul_le_mul_of_nonneg_left hpinch
      (show 0 ≤ 2 / (n : ℝ) by positivity)
  calc
    (2 / (n : ℝ)) * g.scalarAt x ^ 2
        ≤ (2 / (n : ℝ)) * ((n : ℝ) * g.ricciNormSqAt x) := hscale
    _ = 2 * g.ricciNormSqAt x := by
        field_simp [ne_of_gt hn]

/--
Pointwise Hamilton-Riccati supersolution:
`∂ₜR ≥ ΔR + (2/n) R²`, with the derivative supplied by
`SatisfiesHamiltonScalarEvolutionAt`.
-/
theorem hamilton_scalar_riccati_supersolution_at
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ))
    (hHam : SatisfiesHamiltonScalarEvolutionAt gt t₀ x) :
    ∃ R',
      HasDerivAt (fun t ↦ (gt t).scalarAt x) R' t₀ ∧
        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
            + (2 / (n : ℝ)) * (gt t₀).scalarAt x ^ 2 ≤ R' := by
  refine ⟨(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
      + 2 * (gt t₀).ricciNormSqAt x, ?_, ?_⟩
  · simpa [SatisfiesHamiltonScalarEvolutionAt] using hHam
  · have hreact :=
      hamilton_scalar_reaction_bound_at
        (g := gt t₀) (x := x) hn
    linarith

/--
At a spatial minimum, the Laplacian contribution is nonnegative, so the scalar
minimum obeys the pointwise Riccati differential inequality.  The hypothesis
`hMinLap` is the honest spatial-minimum witness `0 ≤ ΔR` at `x`.
-/
theorem hamilton_scalar_minimum_riccati_step_at
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ))
    (hHam : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hMinLap :
      0 ≤ (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x) :
    ∃ R',
      HasDerivAt (fun t ↦ (gt t).scalarAt x) R' t₀ ∧
        (2 / (n : ℝ)) * (gt t₀).scalarAt x ^ 2 ≤ R' := by
  rcases hamilton_scalar_riccati_supersolution_at
      (gt := gt) (t₀ := t₀) (x := x) hn hHam with
    ⟨R', hR', hineq⟩
  exact ⟨R', hR', by linarith⟩

/--
The unproven closed-manifold Hamilton scalar evolution frontier.

This definition is a target statement, not a theorem: every closed Ricci-flow
solution should satisfy `∂ₜ R = ΔR + 2 |Ric|²` once the required curvature
regularity for each time-slice is available.  The single-chart analogues are
`hamilton_scalar_evolution_of_bianchi`,
`hamilton_scalar_evolution_of_bianchi_curved`,
`hamilton_scalar_evolution_ricci_flow`,
`curved_ricci_flow_scalar_evolution`, and
`curved_ricci_flow_scalar_evolution_trace_form` in `ModelLaplacian.lean`.
-/
def HamiltonScalarEvolutionProgram : Prop :=
  ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
    IsClosedRicciFlowSolutionAt gt t₀ x →
      ∀ hcurv : ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
        letI : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
          hcurv
        SatisfiesHamiltonScalarEvolutionAt gt t₀ x

/--
Predicate-discharge version of the Hamilton scalar evolution program.

This is deliberately conditional: it packages the current closed-manifold
analytic obligations instead of asserting the unconditional program.
-/
theorem hamiltonScalarEvolutionProgram_of_predicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionPredicatesAt (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) := by
  intro gt t₀ x hflow hcurv
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
    hcurv
  rcases hPred gt t₀ x hflow hcurv with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise hDiv hCon hTensorSub hTraceLap hlin hBianchi

theorem hamiltonScalarEvolutionProgram_of_hessianPredicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionHessianPredicatesAt (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) :=
  hamiltonScalarEvolutionProgram_of_predicates
    (n := n) (M := M)
    (fun gt t₀ x hflow hcurv ↦ by
      letI : ∀ t : ℝ,
          CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
        hcurv
      exact hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
        (hPred gt t₀ x hflow hcurv))

theorem hamiltonScalarEvolutionProgram_of_traceDerivativePredicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionTraceDerivativePredicatesAt
              (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) :=
  hamiltonScalarEvolutionProgram_of_hessianPredicates
    (n := n) (M := M)
    (fun gt t₀ x hflow hcurv ↦ by
      letI : ∀ t : ℝ,
          CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
        hcurv
      exact hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates
        (hPred gt t₀ x hflow hcurv))

end Poincare
