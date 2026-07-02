# M1-lc-existence notes

## Route decision

Chosen route: Route A, global Koszul.

API evidence:

- `Poincare/KoszulExistence.lean` already defines `CovariantDerivative.koszulRHS`, `koszulFunctionalAt`, `leviCivitaValueAt`, `leviCivitaDirectionalAt`, and the bundled `CovariantDerivative.leviCivitaConnection`.
- The same file proves the substantive Koszul construction layer: `isCovariantDerivativeOn_leviCivitaCovFun`, `leviCivitaConnection_metricCompatibleAt`, and `leviCivitaConnection_torsionFreeAt`.
- Mathlib provides `VectorField.mlieBracket` and its add/smul laws in `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`.
- Mathlib provides the bundled torsion tensor and `CovariantDerivative.torsion_eq_zero_iff` in `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Torsion.lean`.
- Mathlib provides `CovariantDerivative.of_isCovariantDerivativeOn_of_open_cover`, so Route B gluing is a plausible route, and this repo already has `chartMetric`, `chartLeviCivita`, and `chartLeviCivita_contMDiff` in `Poincare/ChartTransport.lean`.

Reason for not choosing Route B in this layer: the verified chart-model connection exists, but the current missing bridge is transporting chart-domain operators back to one global tangent-bundle `CovariantDerivative` and proving overlap agreement. Route A already has a global bundled connection, so the first verified global layer should specialize it to `ClosedSmoothRiemannianMetric`.

## Current verified layer

Exact Lean declarations added in `Poincare.Global.LeviCivitaExistence`:

- `Poincare.LeviCivitaExistence.metric_pairing_mdiffAt`
- `Poincare.LeviCivitaExistence.metric_nondegenerate`
- `Poincare.LeviCivitaExistence.closedLeviCivitaConnection`

## Remaining decomposition

1. Prove compatibility of the specialized candidate with the global predicate:
   ```lean
   theorem closedLeviCivitaConnection_metricCompatible
       (g : ClosedSmoothRiemannianMetric n M) :
       IsMetricCompatible g (closedLeviCivitaConnection g)
   ```
2. Convert pointwise torsion-freeness to Mathlib's bundled torsion tensor:
   ```lean
   theorem closedLeviCivitaConnection_torsion
       (g : ClosedSmoothRiemannianMetric n M) :
       (closedLeviCivitaConnection g).torsion = 0
   ```
3. Package the target existence theorem:
   ```lean
   theorem levi_civita_exists (g : ClosedSmoothRiemannianMetric n M) :
       ∃ cov, IsMetricCompatible g cov ∧ cov.torsion = 0
   ```
4. If a chart-transport proof is later needed independently, prove a pulled-back local operator statement:
   ```lean
   theorem chartLeviCivita_isCovariantDerivativeOn_chartTarget
       (...) :
       IsCovariantDerivativeOn E (...) (extChartAt I x₀).source
   ```
5. Prove overlap agreement for chart-transport gluing via uniqueness:
   ```lean
   theorem chartLeviCivita_agree_on_overlap
       (...) :
       EqOn (localChartCov x₀) (localChartCov x₁)
         ((extChartAt I x₀).source ∩ (extChartAt I x₁).source)
   ```
