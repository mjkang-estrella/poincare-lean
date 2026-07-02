import Poincare.Global.LeviCivitaTransport

/-!
# Local regularity bridges for the closed Levi-Civita connection

This module collects the local regularity facts needed to turn the
chart-transported Levi-Civita value identification into the global
`ContMDiffCovariantDerivative` instance.
-/

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/--
The inverse-chart pullback of a `C^m` tangent field is `C^m` at source
points after applying the chart.

This is the regularity upgrade of
`chartTransportedLeviCivitaSection_mdiffAt_apply_chart`; it isolates one
of the local-to-global gluing ingredients for the closed Levi-Civita
connection.
-/
theorem chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E]
    (x₀ : M) {X : Π y : M, TangentSpace I y} {y : M} {m : ℕ∞ω}
    (hy : y ∈ (extChartAt I x₀).source)
    (hX : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) m (T% X) y)
    (hm : m + 1 ≤ (∞ : ℕ∞ω)) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (T% (chartTransportedLeviCivitaSection (I := I) x₀ X))
      (extChartAt I x₀ y) := by
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hsmWithin :
      CMDiffAt[range I] ∞ ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) :=
    contMDiffWithinAt_extChartAt_symm_range (n := ∞) x₀ htarget
  have hsm :
      CMDiffAt ∞ ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) := by
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
  have hinv :
      (mfderiv% ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)).IsInvertible := by
    have hinvWithin := isInvertible_mfderivWithin_extChartAt_symm htarget
    rwa [I.range_eq_univ, mfderivWithin_univ] at hinvWithin
  have hX' :
      CMDiffAt m (T% X) (((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)) := by
    rw [hleft]
    exact hX
  have hpull := hX'.mpullback_vectorField_preimage hsm hinv hm
  simpa [chartTransportedLeviCivitaSection, I.range_eq_univ] using hpull

end CovariantDerivative

namespace Poincare

/-!
The full theorem
`closedLeviCivitaConnection_contMDiff` is not introduced here yet: the
remaining step is to convert the value-level identification theorem
`chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` into
an eventually-equal statement for the hom-bundle section required by
`CovariantDerivative.ContMDiffCovariantDerivative`.
-/

end Poincare

