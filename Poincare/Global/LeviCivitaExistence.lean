import Poincare.Global.LeviCivita
import Poincare.KoszulExistence

/-!
# Levi-Civita existence in the global Mathlib manifold layer

Route decision.  Route A is the shortest verified path in the current API:
`Poincare.KoszulExistence` already constructs
`CovariantDerivative.leviCivitaConnection` from the global Koszul formula,
proves the connection axioms, and proves pointwise metric compatibility and
torsion-freeness.  The pinned Mathlib API supplies
`VectorField.mlieBracket`, `CovariantDerivative.torsion_eq_zero_iff`, and
`MDifferentiableAt.inner_bundle`; those are exactly the pieces needed to
specialize the existing construction to `ClosedSmoothRiemannianMetric`.

Route B is also supported by verified ingredients (`chartMetric`,
`chartLeviCivita`, and `chartLeviCivita_contMDiff` in `ChartTransport`), but
the current hard interface is transporting the chart-domain operator back to a
single global `CovariantDerivative` and proving agreement on overlaps.
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

namespace LeviCivitaExistence

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

omit [T2Space M] in
/-- A smooth closed Riemannian metric differentiates pairings of differentiable tangent fields. -/
theorem metric_pairing_mdiffAt (g : ClosedSmoothRiemannianMetric n M)
    {x : M} {A B : ∀ y : M, TM y}
    (hA : MDiffAtTangentField A x) (hB : MDiffAtTangentField B x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M => g.inner y (A y) (B y)) x := by
  letI : RiemannianBundle TM := g.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle I ∞ E TM :=
    g.toIsContMDiffRiemannianBundle
  have hinner :
      MDifferentiableAt I 𝓘(ℝ) (fun y : M => inner ℝ (A y) (B y)) x := by
    exact MDifferentiableAt.inner_bundle
      (by simpa [MDiffAtTangentField] using hA)
      (by simpa [MDiffAtTangentField] using hB)
  simpa [ClosedSmoothRiemannianMetric.fiber_inner_eq] using hinner

omit [T2Space M] in
/-- Positive-definiteness gives the left nondegeneracy needed by the Koszul construction. -/
theorem metric_nondegenerate (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (v : TM x) (hv : ∀ w : TM x, g.inner x v w = 0) : v = 0 := by
  by_contra hne
  have hpos := g.inner_pos x hne
  rw [hv v] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

private def pairingRegularity (g : ClosedSmoothRiemannianMetric n M) :
    ∀ (x : M) (A B : ∀ y : M, TM y),
      MDifferentiableAt I ((closedSmoothModelWithCorners n).prod 𝓘(ℝ, E)) (T% A) x →
        MDifferentiableAt I ((closedSmoothModelWithCorners n).prod 𝓘(ℝ, E)) (T% B) x →
          MDifferentiableAt I 𝓘(ℝ) (fun y : M => g.inner y (A y) (B y)) x :=
  fun _ _ _ hA hB =>
    metric_pairing_mdiffAt g
      (by simpa [MDiffAtTangentField] using hA)
      (by simpa [MDiffAtTangentField] using hB)

/--
The global Koszul candidate specialized to a smooth closed Riemannian metric.
The underlying construction is `CovariantDerivative.leviCivitaConnection`.
-/
noncomputable def closedLeviCivitaConnection
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative I E TM :=
  CovariantDerivative.leviCivitaConnection g.inner
    (fun y v w => g.inner_symm y v w)
    (fun y v hv => metric_nondegenerate g y v hv)
    (pairingRegularity g)

end LeviCivitaExistence

end Poincare
