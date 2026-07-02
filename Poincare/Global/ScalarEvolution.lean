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

end Poincare
