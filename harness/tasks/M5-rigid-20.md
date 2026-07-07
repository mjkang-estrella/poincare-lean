Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-20: the coefficient-evolution ODE — the weight from compatibility

Context: `harness/reports/M5-rigid-19_blocked.md` (READ FIRST). ORCHESTRATOR REDUCTION: the missing transverse-transverse endpoint pairing reduces via the EXPLICIT sin formulas (`J_w(t) = sin t · w` in chart coordinates, `JacobiOscillator.lean`) to the CHART-METRIC COEFFICIENT EVOLUTION: `G(z(t))(w, w')` for FIXED chart vectors `w, w'` along the geodesic `z(t)`. Its t-derivative is `(∂G along z')(w,w')`, computable through the PROVEN compatibility pairing identity (`chartChristoffelField_pairing_eq_blendedChartMetric`, `GeodesicSpeed.lean` — the same identity that gave constant speed, now applied to fixed vectors instead of the velocity): `d/dt G(z(t))(w,w') = G(Γ(z')(w), w') + G(w, Γ(z')(w'))`-shaped. For transverse `w, w'` along a unit-speed geodesic in constant curvature 1, combine with the Christoffel structure to derive the scalar ODE for the coefficient (the target-side computation in `CartanExpansionBridge.lean` produced the explicit weight — its ODE is knowable from the explicit conformal data: differentiate the sphere weight and MATCH; the source satisfies the same ODE by the same identities + constant curvature) — then ODE uniqueness (the linear machinery in `GeodesicLinearized.lean`) gives: source weight = sphere weight.

Deliverables, in a NEW file `Poincare/Global/CoefficientEvolution.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE DERIVATIVE IDENTITY for `t ↦ G(z(t))(w,w')` via the compatibility pairing (fixed vectors).
2. THE ODE + UNIQUENESS: both weights satisfy the same scalar ODE with the same initial data ⟹ equal; PIN against the sphere's explicit weight first (refutation protocol — verify the proposed ODE holds for `roundSphereEndpointChartWeight` before proving the general case).
3. THE PAIRING THEOREM: `G(z(t))(J_w, J_{w'}) = sin²t · weight(t) · G(z₀)(w,w')`-shaped (the consumer's exact form — read `CartanLocalIsometry.lean`'s punctured source predicate).
4. If reachable: the punctured source expansion + 🎯 the unconditional local isometry; else isolate.
5. Report `harness/reports/M5-rigid-20_{done|blocked}.md` with the pinning outcome.

No vacuous wrappers. Verify: `lake build Poincare.Global.CoefficientEvolution` and report the actual result. Commit your work.
