Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-11: THE PULLBACK ASSEMBLY — cartanMap is a local isometry

Context: everything is staged. `CartanDifferential.lean` (report `harness/reports/M5-rigid-10_done.md`, READ FIRST): endpoint homogeneity, radial derivative surface, transverse `sin t/t` endpoint derivative, Gauss cross-pairing zero, the `cartanMap` chart differential CHAIN RULE, and "the final pullback algebra boundary" isolated for composition. `CartanPullback.lean` (rigid-9): the radial/transverse Gram decomposition + tangent-alignment preservation. Both metrics have the SAME factors (the sphere satisfies the same constant-curvature hypothesis: `roundSphereMetric3_hasConstantSectionalCurvature_one`; the Jacobi machinery `JacobiOscillator.lean` is metric-generic).

THE TASK: compose — for `u, u'` at a point of the normal ball, expand both through the decomposition (rigid-9), apply the differential surface on each part (rigid-10: radial→radial factor 1, transverse→transverse factor `sin‖v‖/‖v‖`, cross→0), the alignment preserves the anchor pairings, and the SAME factors appear on the sphere side — the pullback pairing equals the source pairing: THE PULLBACK IDENTITY, hence `cartanMap` is a LOCAL ISOMETRY on the normal ball (state as the pointwise chart-metric pullback equality; spelling free, semantics frozen).

Deliverables, in a NEW file `Poincare/Global/CartanLocalIsometry.lean` (do NOT edit any existing file, incl. `Poincare.lean`): the pullback identity + the packaged local-isometry statement. Strict-partial: ONE isolated algebra step. Report `harness/reports/M5-rigid-11_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanLocalIsometry` and report the actual result. Commit your work.
