Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-15: GOAL 10 — toward the radial Gauss lemma

Context: `harness/reports/M5-geo-14_done.md` (READ FIRST) proved constant speed (`chart_geodesic_speed_constantOn`, pairing identity `chartChristoffelField_pairing_eq_blendedChartMetric` in `Poincare/Global/GeodesicSpeed.lean`) and decomposes the radial Gauss lemma: (1) two-parameter geodesic variations `γ(s, t)` (family of chart geodesics with varying initial velocity), (2) mixed time/parameter derivative commutation on the local existence rectangle, (3) differentiate the constant-speed identity in the variation parameter + the compatibility identity, targeting the radial form `G(exp_x v) (d exp_x(v) w) (d exp_x(v) v) = G_x w v`.

CAUTION (honest scoping): step (1)-(2) may need smooth/differentiable dependence of ODE solutions on initial conditions, which the pinned Mathlib may lack (geo-5/geo-12 reports flagged this). FIRST assess: for the RADIAL direction only (`w = v`, i.e. differentiating along the ray parameter `s ↦ exp(s·v)`), the Gauss pairing follows from constant speed + homogeneity ALONE — no variation theory: `G(γ(t))(γ'(t))(γ'(t)) = G_x(v)(v)` is constant speed; the radial-radial Gauss identity is its restatement through the `expAt` ray law (`expAt_eventually_eq_geodesicGermAt`, `ExponentialFixedTime.lean`; `geodesicGermAt_chart_hasDerivAt`). DELIVER THE RADIAL-RADIAL CASE UNCONDITIONALLY; state the transverse case (`w ⊥ v`) as an honest named interface/lemma-statement ONLY IF the variation machinery genuinely blocks — with the precise missing ODE-dependence statement isolated in the report.

Deliverables, in a NEW file `Poincare/Global/GaussLemmaRadial.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. RADIAL-RADIAL GAUSS: the speed of the exponential ray at parameter `t` equals the initial speed, stated through `expAt`/`geodesicGermAt` and the blended chart metric (exact spelling free; semantics: `G(ray(t))(ray'(t), ray'(t)) = G(x₀-anchor)(v₀, v₀)` on the honest interval).
2. Whatever transverse-case progress is genuinely available without fake variation theory; else the isolated ODE-dependence blocker statement.
3. Report `harness/reports/M5-geo-15_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.GaussLemmaRadial` and report the actual result. Commit your work.
