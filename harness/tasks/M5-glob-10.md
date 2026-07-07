Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-10: THE PARKED WALL — the double-anchor reanchor law

Context: THE CRITICAL PATH now runs through the long-parked reanchor law. READ FIRST: `harness/reports/M5-geo-11_blocked.md` (the parked spec + Koszul plan), `harness/reports/M5-glob-9_blocked.md` (the demanded velocity/Christoffel transition law VERBATIM), and what `GeodesicReanchor/GeodesicReanchorLaw/GeodesicReanchorClose.lean` already prove. THE LAW: the geodesic germ re-anchored at a point of its own trajectory — `germ_{x₀}(v, t₀ + s) = germ_{x₁}(v₁, s)` with `x₁ = germ(v, t₀)` and `v₁` = the transported velocity — the double-anchor ODE argument: both sides solve the SAME geodesic ODE (in the x₁-chart after transition) with the same initial data at `s = 0` — PL uniqueness closes IF the chart-transition of the ODE is proven: the geodesic equation is CHART-COVARIANT (the Christoffel transition law — the Koszul plan: the transition Christoffels differ by the chart-change second derivative; the machinery: `ChartIdentification/ChartTransport/LocalConnectionRegularity.lean` + the curvature-bridge zone files did analogous transitions). NEW since parking: the ENTIRE derivative/uniqueness arsenal (PL packages, linearized uniqueness, strict derivatives, the zone machinery). ASSEMBLE the law → feed `OffAnchorNaturality/ExpNaturality` → the re-centering EqOn → `RigidStepCompatibleWith` → THE CHAIN FIRES. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-10_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ReanchorLawFinal.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ReanchorLawFinal` and report the actual result. Commit your work.
