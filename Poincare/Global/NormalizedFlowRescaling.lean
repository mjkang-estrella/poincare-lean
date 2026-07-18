import Poincare.Global.MetricRescaleCurvature
import Poincare.Global.MetricVariation
import Poincare.Global.NormalizedFlow

/-!
# Normalized Ricci flow from time reparameterization and rescaling

Let `g(s)` solve the unnormalized closed Ricci flow.  If `τ'(t) = c(t)⁻¹`
and

`c'(t) = (2 / n) * meanScalar (c(t) • g(τ(t))) * c(t)`,

then `c(t) • g(τ(t))` solves the normalized closed Ricci flow.  The proof is
the pointwise product and chain rule.  Constant metric rescaling leaves the
covariant Ricci tensor unchanged, so the reparameterized unnormalized term is
exactly `-2 Ric` after the factors `c` and `c⁻¹` cancel.

The algebraic theorem below retains actual `HasDerivAt` hypotheses for every
tested base-metric component.  A second theorem derives those hypotheses from
`TimeDifferentiableAt` and the section-tested unnormalized closed Ricci-flow
predicate.  The target flow's quantified `DerivRegularAt` certificate is not
transported between connections: `ricciTraceAt_eq_ricciBilinearAt` identifies
its trace directly with the canonical Ricci bilinear form.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory
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
local notation "TM" => (TangentSpace I : M → Type _)

/-- A positive time-dependent constant rescaling of a reparameterized metric
family.  Positivity is retained as data because `constSMul` constructs a
Riemannian metric only for a positive factor. -/
def timeReparameterizedConstRescaling
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t) :
    ℝ → ClosedSmoothRiemannianMetric n M :=
  fun t ↦ (gt (τ t)).constSMul (c t) (hc t)

/--
The algebraic rescaling/reparameterization mechanism for normalized Ricci
flow at one spacetime point.

The componentwise `HasDerivAt` hypothesis is the precise regularity needed by
the chain rule.  Merely knowing the source equation as an equality of `deriv`
values would not justify differentiating through `τ`.
-/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_componentHasDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    {t₀ : ℝ} {x : M}
    (hτ : HasDerivAt τ (c t₀)⁻¹ t₀)
    (hscale : HasDerivAt c
      ((2 / (n : ℝ)) *
        meanScalar (timeReparameterizedConstRescaling gt τ c hc t₀) * c t₀) t₀)
    (hbaseComponent : ∀ v w : TM x,
      HasDerivAt (fun s ↦ (gt s).inner x v w)
        (-2 * (gt (τ t₀)).ricciAt x v w) (τ t₀)) :
    IsClosedNormalizedRicciFlowSolutionAt
      (timeReparameterizedConstRescaling gt τ c hc) t₀ x := by
  let G : ℝ → ClosedSmoothRiemannianMetric n M :=
    timeReparameterizedConstRescaling gt τ c hc
  refine ⟨?_, ?_⟩
  · intro t
    exact
      ⟨(G t).leviCivita_metricCompatibleAt x,
        (G t).leviCivita_torsionFreeAt x⟩
  · intro Z hZ hreg w
    have hcomposed :
        HasDerivAt (fun t ↦ (gt (τ t)).inner x (Z x) w)
          ((-2 * (gt (τ t₀)).ricciAt x (Z x) w) * (c t₀)⁻¹) t₀ :=
      (hbaseComponent (Z x) w).comp t₀ hτ
    have hproduct :
        HasDerivAt
          (fun t ↦ c t * (gt (τ t)).inner x (Z x) w)
          (((2 / (n : ℝ)) * meanScalar (G t₀) * c t₀) *
              (gt (τ t₀)).inner x (Z x) w +
            c t₀ *
              ((-2 * (gt (τ t₀)).ricciAt x (Z x) w) * (c t₀)⁻¹)) t₀ := by
      simpa [G] using hscale.mul hcomposed
    have htrace₀ :=
      CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
        (cov := (G t₀).leviCivita) (Z := Z) (x := x) (hZ x) hreg w
    have htrace :
        CovariantDerivative.ricciTraceAt (G t₀).leviCivita hreg w =
          (G t₀).ricciAt x (Z x) w := by
      calc
        CovariantDerivative.ricciTraceAt (G t₀).leviCivita hreg w =
            (G t₀).ricciAt x w (Z x) := by
              simpa [ClosedSmoothRiemannianMetric.ricciAt] using htrace₀
        _ = (G t₀).ricciAt x (Z x) w :=
          (G t₀).ricciAt_symm x w (Z x)
    have hricci :
        (G t₀).ricciAt x (Z x) w =
          (gt (τ t₀)).ricciAt x (Z x) w := by
      simpa [G, timeReparameterizedConstRescaling] using
        ClosedSmoothRiemannianMetric.constSMul_ricciAt
          (gt (τ t₀)) (c t₀) (hc t₀) x (Z x) w
    have hinner :
        (fun t ↦ (G t).inner x (Z x) w) =
          (fun t ↦ c t * (gt (τ t)).inner x (Z x) w) := by
      funext t
      simp [G, timeReparameterizedConstRescaling,
        ClosedSmoothRiemannianMetric.constSMul_inner]
    have hinner₀ :
        (G t₀).inner x (Z x) w =
          c t₀ * (gt (τ t₀)).inner x (Z x) w := by
      simp [G, timeReparameterizedConstRescaling,
        ClosedSmoothRiemannianMetric.constSMul_inner]
    have hcancel :
        c t₀ *
            ((-2 * (gt (τ t₀)).ricciAt x (Z x) w) * (c t₀)⁻¹) =
          -2 * (gt (τ t₀)).ricciAt x (Z x) w := by
      field_simp [ne_of_gt (hc t₀)]
    rw [hinner, hproduct.deriv, htrace, hricci, hinner₀, hcancel]
    ring

/--
A differentiable unnormalized closed Ricci flow supplies the componentwise
`HasDerivAt` premise of the algebraic theorem.  Canonical extension
regularity converts the source's section-tested equation to the bilinear
identity `∂ₛg = -2 Ric` before the chain rule is applied.
-/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    {t₀ : ℝ} {x : M}
    (hτ : HasDerivAt τ (c t₀)⁻¹ t₀)
    (hscale : HasDerivAt c
      ((2 / (n : ℝ)) *
        meanScalar (timeReparameterizedConstRescaling gt τ c hc t₀) * c t₀) t₀)
    (hflow : IsClosedRicciFlowSolutionAt gt (τ t₀) x)
    (htime : TimeDifferentiableAt gt (τ t₀) x) :
    IsClosedNormalizedRicciFlowSolutionAt
      (timeReparameterizedConstRescaling gt τ c hc) t₀ x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_componentHasDerivAt
      gt τ c hc hτ hscale
  intro v w
  have hpoint :
      timeDerivAt gt (τ t₀) x v w =
        -2 * (gt (τ t₀)).ricciAt x v w :=
    isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt hflow
      (closedRicciFlowExtensionRegularAt_canonical gt (τ t₀) x) v w
  exact (htime v w).hasDerivAt.congr_deriv (by
    simpa [timeDerivAt] using hpoint)

/-- The rescaling construction solves the normalized equation at every
spacetime point when the source flow and all derivative data are global. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_all_times
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (hτ : ∀ t : ℝ, HasDerivAt τ (c t)⁻¹ t)
    (hscale : ∀ t : ℝ, HasDerivAt c
      ((2 / (n : ℝ)) *
        meanScalar (timeReparameterizedConstRescaling gt τ c hc t) * c t) t)
    (hflow : ∀ s : ℝ, ∀ x : M, IsClosedRicciFlowSolutionAt gt s x)
    (htime : ∀ s : ℝ, ∀ x : M, TimeDifferentiableAt gt s x) :
    ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (timeReparameterizedConstRescaling gt τ c hc) t x := by
  intro t x
  exact
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow
      gt τ c hc (hτ t) (hscale t) (hflow (τ t) x) (htime (τ t) x)

end Poincare
