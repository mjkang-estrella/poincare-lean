Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-32: the homogeneity conversion — small velocities host the unit-speed formulas

Context: `harness/reports/M5-rigid-31_blocked.md` (READ FIRST): the shrunk ball + PL law at `t = ‖v‖` are proven (`CartanDomainShrink.lean`), but the unit direction `‖v‖⁻¹ • v` has norm 1 — outside the small-velocity flows. THE CONVERSION (proven machinery): HOMOGENEITY — `geodesicGermAt g x₀ (s • w) t = geodesicGermAt g x₀ w (s·t)` (`ExponentialGerm.lean` germ form; `ExponentialFixedTime.lean` flow form on Icc; `ExponentialRayLawFull.lean`). The geodesic with SMALL velocity `v` over `[0,1]` is the geodesic with direction `w := δ₀·(v/‖v‖)`-scaled... CONCRETELY: pick the working velocity `u := (δ/2)·(v/‖v‖)` (norm δ/2 < δ — inside every ball) and time `T := ‖v‖/(δ/2)` — then `expAt(v) = germ(u, T)` by homogeneity (both equal `germ(v/s, s·1)` chains — compose the proven laws), and the interval facts at velocity `u` over `[0, T]` (with `T ≤ τ` for `‖v‖` small — shrink once more) host ALL the proven block ingredients; the sin factors appear as `sin(speed·T)/speed`-shaped where `speed = ‖u‖_metric` — reconcile the normalization with the blocks' expected `sin‖v‖` form via the constant-speed value (the anchor metric norm of `u` relates to `‖v‖` through the chart metric — the alignment/anchor lemmas in `CartanMap.lean` handle the anchor normalization; derive carefully, document, and PIN the endpoint value against the sphere if any normalization is uncertain).

Deliverables, in a NEW file `Poincare/Global/CartanHomogeneity.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE CONVERSION: `expAt(v)` and its differential data expressed through the working velocity `u` and time `T` (homogeneity chains).
2. THE BLOCK HYPOTHESES at `(u, T)` from the proven interval facts (the rigid-30/31 conversion completed).
3. 🎯 THE LOCAL ISOMETRY on the (再)shrunk ball via the bridge; else isolate ONE statement.
4. Report `harness/reports/M5-rigid-32_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanHomogeneity` and report the actual result. Commit your work.
