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
- `Poincare.LeviCivitaExistence.closedLeviCivitaConnection_metricCompatible`
- `Poincare.LeviCivitaExistence.closedLeviCivitaConnection_torsion`
- `Poincare.levi_civita_exists`

## Remaining decomposition

The target existence statement is discharged in this layer. Remaining follow-up work is now hardening and Route-B independence:

1. Prove smooth regularity of the global specialized connection:
   ```lean
   theorem closedLeviCivitaConnection_contMDiff
       (g : ClosedSmoothRiemannianMetric n M) :
       CovariantDerivative.ContMDiffCovariantDerivative
         (LeviCivitaExistence.closedLeviCivitaConnection g) 1
   ```
2. Prove the specialized existence theorem with the full standard closed-manifold context explicitly documented:
   ```lean
   theorem levi_civita_exists_closed_context
       [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
       (g : ClosedSmoothRiemannianMetric n M) :
       ∃ cov, IsMetricCompatible g cov ∧ cov.torsion = 0
   ```
3. If a chart-transport proof is later needed independently, prove a pulled-back local operator statement:
   ```lean
   theorem chartLeviCivita_isCovariantDerivativeOn_chartTarget
       (...) :
       IsCovariantDerivativeOn E (...) (extChartAt I x₀).source
   ```
4. Prove overlap agreement for chart-transport gluing via uniqueness:
   ```lean
   theorem chartLeviCivita_agree_on_overlap
       (...) :
       EqOn (localChartCov x₀) (localChartCov x₁)
         ((extChartAt I x₀).source ∩ (extChartAt I x₁).source)
   ```
5. Package chart gluing via Mathlib's open-cover constructor:
   ```lean
   theorem levi_civita_exists_by_chart_gluing
       (g : ClosedSmoothRiemannianMetric n M) :
       ∃ cov, IsMetricCompatible g cov ∧ cov.torsion = 0
   ```
