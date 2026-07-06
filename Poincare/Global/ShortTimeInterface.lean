import Poincare.Global.Statement
import Poincare.Global.ScalarEvolution

/-!
# Short-time Ricci-flow existence interface

This module isolates the Hamilton-DeTurck short-time existence input for
closed smooth three-manifolds.  It is a statement layer only: it does not prove
parabolic PDE existence, and it does not manufacture the extra regularity
packages consumed by the closed scalar-evolution theorem.
-/

noncomputable section

open Bundle FiberBundle
open Filter Set
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3
local notation "TM" => (TangentSpace I : M → Type _)

/--
Hamilton-DeTurck short-time existence for closed smooth three-manifolds.

For every initial closed smooth Riemannian metric `g₀`, there is a positive
time `T` and a metric family `gt` with `gt 0 = g₀` satisfying the pointwise
closed Ricci-flow equation on the half-open interval `(0, T)`.

This is a named hypothesis interface, not a proof of the parabolic existence
theorem and not an instantiable certificate.
-/
def RicciFlowShortTimeExistence3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M,
    ∃ T : ℝ, 0 < T ∧
      ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
        gt 0 = g₀ ∧
          ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
            IsClosedRicciFlowSolutionAt gt t x

/-- The short-time interface unfolds to its metric-family payload. -/
theorem ricciFlowShortTimeExistence3_eq :
    RicciFlowShortTimeExistence3 M =
      (∀ g₀ : ClosedSmoothRiemannianMetric 3 M,
        ∃ T : ℝ, 0 < T ∧
          ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
            gt 0 = g₀ ∧
              ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
                IsClosedRicciFlowSolutionAt gt t x) :=
  rfl

/--
Shape check: once an initial metric is available, the target family type is
inhabited by the constant family.
-/
@[reducible] def shortTimeMetricFamilyInhabited
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    Inhabited (ℝ → ClosedSmoothRiemannianMetric 3 M) :=
  ⟨fun _ ↦ g₀⟩

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] in
/-- Shape check: the constant metric family has the requested initial value. -/
theorem const_metricFamily_zero
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    (fun _ : ℝ ↦ g₀) 0 = g₀ :=
  rfl

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] in
/--
Static Ricci-flat metrics satisfy the Ricci-flow equation clause.

This deliberately reuses `isClosedRicciFlowSolutionAt_const_of_ricciFlat` from
`Poincare.Global.RicciFlow`; it does not assert that an arbitrary constant
metric is a Ricci-flow solution.
-/
theorem static_ricciFlat_flowClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM y},
      ClosedC2TangentField (n := 3) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t x := by
  intro t _ht x
  exact isClosedRicciFlowSolutionAt_const_of_ricciFlat
    (n := 3) (M := M) (g := g) (x := x)
    (fun {Z} hZ hreg w ↦ hric x hZ hreg w) t

/--
Extract the family supplied by the short-time existence interface for a chosen
initial metric.
-/
theorem exists_shortTime_ricciFlow_of_interface
    (hShort : RicciFlowShortTimeExistence3 M)
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
        gt 0 = g₀ ∧
          ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
            IsClosedRicciFlowSolutionAt gt t x :=
  hShort g₀

/--
The short-time interface supplies the flow half of the neighborhood hypothesis
used by `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`.

It does not derive `ClosedRicciFlowExtensionRegularAt`, metric-flow
regularity, time differentiability, metric-raise differentiability, or the
closed scalar-variation assembly predicates.  Those remain separate analytic
regularity obligations.
-/
theorem exists_shortTime_flow_half_of_hamiltonScalarEvolution_input
    (hShort : RicciFlowShortTimeExistence3 M)
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    ∃ T : ℝ, ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
      0 < T ∧ gt 0 = g₀ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          IsClosedRicciFlowSolutionAt gt t x ∧
            (∀ᶠ y in nhds x, IsClosedRicciFlowSolutionAt gt t y) := by
  rcases hShort g₀ with ⟨T, hT, gt, hinit, hflow⟩
  refine ⟨T, gt, hT, hinit, ?_⟩
  intro t ht x
  exact ⟨hflow t ht x, Eventually.of_forall (hflow t ht)⟩

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] in
/--
For an already extracted short-time family, the pointwise flow clause upgrades
to the flow-only neighborhood clause required as one component of
`satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`.
-/
theorem eventually_isClosedRicciFlowSolutionAt_of_shortTime_flow
    {T : ℝ} {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hflow : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t x)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) :
    ∀ᶠ y in nhds x, IsClosedRicciFlowSolutionAt gt t y :=
  Eventually.of_forall (hflow t ht)

end Poincare
