Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-83: bounded w + homogeneous extension — the package closes

Context: `harness/reports/M5-rigid-82_blocked.md` (READ FIRST). PROVEN: the bounded-center uniform linear PL lemma + the obstruction (the PL center carries the quadratic metric value — unrestricted `∀ w` impossible) (`UniformPL.lean`). THE RESOLUTION (two proven-adjacent steps): (1) THE BOUNDED PACKAGE: instantiate the bounded-center lemma at the hosted datum with `w` restricted to a closed ball (radius from the hosted data — the center bound is then finite; the coefficient path facts from the base geodesic as in rigid-82's lemma) — giving `hplNorm` on the ball; (2) THE HOMOGENEOUS EXTENSION: the endpoint pairing facts are BILINEAR-HOMOGENEOUS in `w` (`Ψ_{c·w} = c·Ψ_w`, `LinearizedAdditivity.lean` smul; pairings scale by `c·c'`) — so the ball-restricted transverse-transverse formulas EXTEND to all `w` by rescaling (`w = ‖w‖·ŵ`, `ŵ` in the ball — algebra). CHECK the consumers (`PLNormFeed/BundleDischarge/CorrectedRadial.lean`): if they consume pairing FORMULAS (not the package directly), feed the extended formulas; if the package itself, feed the ball version + note where the unrestricted form is actually used. Then → the transverse blocks land → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/BoundedPackage.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-83_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.BoundedPackage` and report the actual result. Commit your work.
