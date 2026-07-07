Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-89: the membership bound — the norm trajectory stays in the ball

Context: `harness/reports/M5-rigid-88_blocked.md` (READ FIRST — the VERBATIM membership field: the norm-system state `(a, b, q)`-shaped trajectory in a closed ball of some radius). PROVEN EVERYTHING ELSE (`IsometryComplete.lean` feeds). THE BOUND: the norm-system scalars along the hosted flow are (i) CONTINUOUS on the compact interval (compositions of the continuous flow/metric — or (ii) BETTER: their VALUES ARE PINNED — `actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc` (`CartanIsometryTheorem.lean`) / the speed-generic pinned versions (`SpeedGeneric.lean`) give `a = sin²(s·t)·q, b = s·sin·cos·q, c = s²cos²·q`-shaped EXPLICIT values — bounded by `max(1, s, s²)·q` via `|sin|,|cos| ≤ 1` — so the trajectory lies in the closed ball of radius computable from `q` and `s` OUTRIGHT). CHOOSE the radius as that explicit bound (the `radius` in the membership field is existentially supplied by the assembly — check: if the radius is a FIXED datum from the package, use the pinned bound ≤ radius side condition — shrink if the hosted data allows). Feed the membership → `SolutionsFeed` completes → BOTH transverse blocks → the assembly → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/MembershipBound.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-89_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.MembershipBound` and report the actual result. Commit your work.
