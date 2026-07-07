Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-10: the endpoint differential surface — D(expAt) packaged

Context: `harness/reports/M5-rigid-9_blocked.md` (READ FIRST). Proven: the radial/transverse Gram decomposition + tangent-alignment preservation (`CartanPullback.lean`); the transverse derivative/Jacobi bridge with the sin formula (`CartanIsometry.lean`); the radial ray-law derivative (`ExponentialRayLaw.lean`, `ExponentialDerivativeZero.lean`); Gauss orthogonality at endpoints (`GaussLemmaIntegrated.lean`); the Fréchet/strict derivative machinery (`ExponentialFrechet.lean`, `ExponentialLocalHomeo.lean`). THE TASK: package the ENDPOINT DIFFERENTIAL ACTION of the fixed-time exponential as one theorem surface — for `v` in the normal ball and the decomposition `u = a·v + w` (`w ⊥ v`): the derivative of `s ↦ expAt(v + s·u)` at `s = 0` (chart-read at the endpoint) has: radial component factor 1, transverse component `(sin‖v‖/‖v‖)·(parallel-transported w)`-shaped, zero cross pairing (Gauss). Each piece exists as a lemma family — the packaging is the derivative-of-composite bookkeeping (homogeneity converts `v + s·u` variations into the time/velocity parameterizations the proven lemmas use) + one PartialHomeomorph chain-rule statement for the composed `cartanMap` differential.

Deliverables, in a NEW file `Poincare/Global/CartanDifferential.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE ENDPOINT SURFACE (the four numbered facts of the blocked report, as clean composable statements).
2. THE CHAIN RULE for `cartanMap`'s differential through `expAt_{p₀} ∘ L ∘ (expAt_{x₀})⁻¹` (PartialHomeomorph/inverse-derivative composition — the strict-derivative inverses from `ExponentialLocalHomeo.lean`).
3. If reachable: THE PULLBACK IDENTITY + local isometry (compose with rigid-9's decomposition algebra); else isolate the final algebra.
4. Report `harness/reports/M5-rigid-10_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanDifferential` and report the actual result. Commit your work.
