Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-22: the source-owned expansion from the ODE — the true statement closes

Context: `harness/reports/M5-rigid-21_blocked.md` (READ FIRST). The chart-dependence refutation is PROVEN and the reshape landed (`CartanWeightInvariant.lean`): source-owned invariant endpoint bundle, weighted anchor pairing, weight-canceling punctured consumers (`cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceOwned_and_roundSphere`). THE REMAINING GEOMETRIC THEOREM: derive the SOURCE-OWNED coefficient expansion from the source chart ODE — i.e., construct the source weight via rigid-20's machinery (`CoefficientEvolution.lean`: the fixed-vector derivative identity gives the coefficient ODE along the geodesic; scalar linear ODE existence/uniqueness constructs the solution = THE source-owned weight) and prove the source-owned bundle's fields: the transverse-transverse endpoint pairing = sin²t · (source weight t) · anchor pairing (the sin factors from `JacobiOscillator.lean` + the constructed weight's defining ODE integrated), radial term via constant speed, cross terms via integrated Gauss. This is now a TRUE statement (the weight is defined to make it work) — the content is the interval bookkeeping connecting the pieces.

Deliverables, in a NEW file `Poincare/Global/CartanSourceOwned.lean` (do NOT edit any existing file, incl. `Poincare.lean` — note rigid-21 already wired its import):
1. THE SOURCE WEIGHT constructION (ODE solution along each radial geodesic).
2. THE SOURCE-OWNED EXPANSION (the bundle's exact fields).
3. 🎯 THE UNCONDITIONAL LOCAL ISOMETRY via the weight-canceling consumer.
4. Report `harness/reports/M5-rigid-22_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanSourceOwned` and report the actual result. Commit your work.
