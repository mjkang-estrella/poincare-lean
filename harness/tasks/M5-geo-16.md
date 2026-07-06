Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-16: GOAL 10 — transverse Gauss lemma modulo the named smooth-dependence interface

Context: `Poincare/Global/GaussLemmaRadial.lean` (report `harness/reports/M5-geo-15_done.md`, READ FIRST) proved the radial-radial Gauss identity unconditionally and NAMED the honest blocker interface `ChartGeodesicInitialVelocitySmoothDependence` (differentiable dependence of the chart geodesic flow on initial velocity — the Mathlib ODE gap). House style: conditional theorems on named interfaces are the established currency (cf. the M5 sphere-endgame interfaces).

Deliverables, in a NEW file `Poincare/Global/GaussLemmaTransverse.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE VARIATION IDENTITY, conditional on the interface: for a two-parameter family `γ(s, t)` supplied by the interface (chart geodesics with initial velocity `v + s·w`), differentiate the constant-speed identity in `s` and combine with `chartChristoffelField_pairing_eq_blendedChartMetric` (`GeodesicSpeed.lean`) + symmetry of the Christoffel pairing to derive the classical Gauss pairing conservation: `∂_t [G(γ)(∂_s γ, ∂_t γ)] = (1/2) ∂_s [G(γ)(∂_t γ, ∂_t γ)]`-shaped (adapt to the interface's exact payload; document).
2. TRANSVERSE GAUSS, conditional: `G(ray t)(J t, ray' t) = G(anchor)(w, v) + t·(initial-speed s-derivative term)`-shaped conclusion, specializing to the orthogonal case `G(anchor)(w,v) = 0` ⟹ the pairing stays `0` IF the s-derivative of speed vanishes (constant speed in s at t=0 — from the interface payload); at minimum the pairing-evolution ODE identity is the frozen deliverable, the full statement shape is adaptable.
3. Report `harness/reports/M5-geo-16_{done|blocked}.md`: exactly what the interface must supply (refine its statement if the current one under/over-shoots — propose, do not edit the existing file), and the discharge route (quantitative PL smooth dependence or a bespoke Gronwall-difference argument).

No vacuous wrappers; every hypothesis used or removed. Verify: `lake build Poincare.Global.GaussLemmaTransverse` and report the actual result. Commit your work.
