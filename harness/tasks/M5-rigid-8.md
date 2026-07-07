Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-8: metric preservation of the Cartan map — the local isometry

Context: THE JACOBI FORMULA is proven (`jacobi_position_eq_sin_smul_on_Icc`, `JacobiOscillator.lean`): along unit-speed geodesics of ANY constant-curvature-1 closed metric, transverse Jacobi fields are `sin t · w` — identically on `M` and on `RoundSphere3` (`roundSphereMetric3_hasConstantSectionalCurvature_one`). The Cartan map exists (`CartanMap.lean` + `TangentAlignmentExists.lean`): `Φ = expAt_{p₀} ∘ L ∘ (expAt_{x₀})⁻¹`, a source-target homeomorphism. The flow derivative identifies `D(expAt)` on directions with Jacobi values (`GeodesicFlowDerivative.lean`, `ExponentialFrechet.lean` derivative machinery; radial direction = ray law + constant speed, `GaussLemmaRadial/GeodesicLengthFinal.lean`).

THE CLASSICAL ASSEMBLY: for `v` in the normal ball and `u` a tangent direction at `expAt_{x₀} v`, decompose the pullback `u` into radial + transverse parts at the chart level; `D(expAt)` maps: radial ↦ radial with factor 1 (ray law/constant speed), transverse `w` ↦ Jacobi value `sin‖v‖/‖v‖ · (transported w)`-shaped — THE SAME FACTORS on both sides because both Jacobi formulas are `sin`; `L` intertwines the anchor metrics; hence `Φ` pulls back `roundSphereMetric3.inner` to `g.inner` on the normal ball.

HONEST SLICING (deliver in order; strict-partial valid):
1. `D(expAt)` ON TRANSVERSE DIRECTIONS = the Jacobi value (connect the flow-derivative machinery to `jacobi_position_eq_sin_smul_on_Icc` — the derivative of `s ↦ expAt(t·(v + s·w))` at `s=0` IS `J(t)` up to the homogeneity reparametrization; state precisely).
2. THE PULLBACK IDENTITY at a point: `(roundSphere metric at Φ(x))(DΦ u, DΦ u') = g(x)(u, u')` for the radial/transverse decomposition (both-sides sin factors cancel; `L` handles the anchor).
3. Packaging: `cartanMap` is a LOCAL ISOMETRY on the normal ball (pointwise pullback identity; spelling free, semantics frozen).
4. Report `harness/reports/M5-rigid-8_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/CartanIsometry.lean` (do NOT edit existing files, incl. `Poincare.lean`). No vacuous wrappers. Verify: `lake build Poincare.Global.CartanIsometry` and report the actual result. Commit your work.
