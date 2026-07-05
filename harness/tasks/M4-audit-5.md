Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-5: complete the static-flow non-vacuity program

Read `harness/reports/M4-audit-4_done.md` (its honest-strength closing paragraph) and `M4-audit-1_report.md` (gap items 2-5). The bump/global obstruction is CLOSED; what remains conditional is "the scalar-variation predicate package: metric-flow regularity, raise-map time derivative, delta-Gamma assemblies, double-divergence linearity, contracted-Bianchi inputs" plus the scalar/Ricci-norm C² and quotient/gradient regularity bundles.

Deliverable — witness the ENTIRE remaining package on the STATIC RICCI-FLAT flow (`gt t = g`, Ric ≡ 0), where every time-derivative is zero and every spatial object is the canonical instance:
1. **Inventory** (read-only first): list every hypothesis of `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` and `hamilton_pinching_preserved`'s Track (grep the statements); classify each as (time-regularity | spatial-canonical | algebraic-identity).
2. **Witness the time-regularity members**: constant families — `MetricFlowRegularAt`, `TimeDifferentiableAt`, raise-map time derivative = 0, etc. (constants have `HasDerivAt _ 0` — mechanical; some may already exist from the goal-2 static instance work — REUSE).
3. **Witness the spatial members**: the canonical C¹/C² instances on main should discharge these directly for a fixed smooth metric; where the quotient/gradient differentiability needs R > 0, use a space form (Ric = λg, λ > 0) instead of Ricci-flat for the pinching-side witnesses — deliver BOTH witnesses if the chains need different signs.
4. **The capstone**: `example`/theorem instantiating a headline theorem end-to-end on the static witness (e.g. `satisfiesHamiltonScalarEvolutionAt` holds at the static space form — both sides zero/constant — confirming the full hypothesis chain is simultaneously inhabitable). This is the audit's final non-vacuity certificate.
5. Report: the final honest-strength table (per headline theorem: witnessed / conditional-on-what).

Commit per package member group. Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.MetricVariation`, report names.
