Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-40: the curvature-entry derivative bridge (δΓ bridge pattern, curvature edition)

SCOPE: one bridge. Read `harness/reports/M3-predicates-39_blocked.md`. The missing atom: the derivative of the closed curvature-entry scalars — `y ↦ g.inner y (curvature-values at y on extend sections) (extend ...)` — identified as `g(closedCurvatureCovDerivAt ..., ...)` + Levi-Civita slot corrections.

TEMPLATE (read it end-to-end first): `deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt` (predicates-23, on main) — the SAME triple-pairing product rule with δΓ replaced by curvature values. Differences to handle:
- The curvature values' field differentiability: for the FIXED ∞-smooth metric g, the curvature entries are compositions of connection values and their derivatives — all smooth (the `leviCivita_contMDiff` instance + the entry/Schwarz toolkit). If a `CurvatureFieldMDifferentiableAt`-style honest class keeps the statement clean, add it + prove it satisfiable for the canonical connection (NOT just static: derive from g's smoothness — this is the fixed-metric case, no time family).
- `closedCurvatureCovDerivAt`'s definition (predicates-36 scaffold) = the covariant derivative of the curvature values — flat derivative + slot corrections; the bridge is the rearrangement, as in the δΓ case.

Then (if budget): chain into `ClosedRicciDerivativeExpansionAt` near x — the Ricci entries are Gram-contracted curvature entries; the bridge + the Gram-inverse cancellation (the standard pattern) yields the witness → the predicates-38 consumers fire → bridges (1)/(2) of the Bianchi endgame DONE (only the cyclic core (3) would remain).

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
