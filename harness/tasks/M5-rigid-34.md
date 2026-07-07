Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-34: the scale-generic bridge — the honest scale, shared by both sides

Context: `harness/reports/M5-rigid-33_blocked.md` (READ FIRST): `CartanCoefficientBridge.lean` hardcodes `transverseScale v = sin‖v‖/‖v‖` (Euclidean chart norm), while the hosted `(u,T)` route yields the honest metric-speed scale — different in general (the anchor chart metric ≠ Euclidean). THE FIX: SANCTIONED ADDITIVE EDIT to `CartanCoefficientBridge.lean` (and, if its shapes require, `CartanLocalIsometry/CartanWeightInvariant.lean` — new defs/variants ONLY, no changes to existing statements; everything downstream must keep compiling): a SCALE-GENERIC bridge variant — the bridge's proof pattern never uses the specific function, only that BOTH sides' blocks carry THE SAME scale functions (radial scale, transverse scale) — re-prove the bridge parameterized over the scale pair. THEN in a NEW file `Poincare/Global/CartanScaleGeneric.lean`: instantiate with the HOSTED honest scales (the working-speed sin values from the `(u,T)` data, `CartanHomogeneity.lean` + the pinned scalars `CartanIsometryTheorem/CartanIsometryPackage.lean`); the TARGET side carries the same scales because the alignment `L` intertwines the anchor metrics (the u-speed is alignment-invariant — `TangentAlignment.map_app`-family in `CartanMap.lean`) — 🎯 THE LOCAL ISOMETRY.

Deliverables: the generic bridge variant (additive) + the hosted instantiation + the isometry; strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-rigid-34_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanCoefficientBridge Poincare.Global.CartanScaleGeneric` (BOTH must pass) and report the actual result. Commit your work.
