Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-17: THE FINAL INPUT — the punctured source expansion from Jacobi facts

Context: `harness/reports/M5-rigid-16_blocked.md` (READ FIRST). The ENTIRE corrected local-isometry chain is assembled and waits on ONE theorem: the punctured weighted source endpoint expansion for `g` with `HasConstantSectionalCurvature3 g 1` (the exact predicate in `CartanLocalIsometry.lean`'s punctured surfaces), derived from the interval facts. THE TEMPLATE: the punctured TARGET-side proof (`CartanExpansionBridge.lean`, rigid-14/16) — READ IT: replicate its structure with the generic machinery replacing sphere-specific inputs. The ingredient map: radial term — ray-law derivative + constant speed (`ExponentialRayLaw.lean`, `GeodesicSpeed.lean`); transverse term — `expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul` (`CartanIsometry.lean`) + the Jacobi formula (`JacobiOscillator.lean`); the chart WEIGHT — the endpoint chart-metric evaluation on Jacobi values, controlled by the transverse Gauss variation identity integrated (`GaussLemmaTransverse.lean`, `GaussLemmaIntegrated.lean`) — the same computation the target proof performs with explicit data, done generically; cross terms — the integrated Gauss orthogonal law.

Deliverables, in a NEW file `Poincare/Global/CartanSourceFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE PUNCTURED SOURCE EXPANSION (the exact remaining hypothesis).
2. 🎯 THE UNCONDITIONAL LOCAL ISOMETRY via the case-split consumer (`CartanPunctured.lean`).
3. Report `harness/reports/M5-rigid-17_{done|blocked}.md`; if blocked, ONE statement + say precisely which ingredient's generic form is missing.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanSourceFinal` and report the actual result. Commit your work.
