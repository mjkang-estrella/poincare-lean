Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-19: the endpoint assembly — the weight identity and the source expansion

Context: `harness/reports/M5-rigid-18_done.md` (READ FIRST — the payload map + the isolated endpoint assembly boundary). `SmoothDependenceDischarge.lean` provides: fixed-time initial-velocity derivatives, mixed `J' = K`, the payload-fed pointwise transverse Gauss identity, the uniform discharge package, the integrated Gauss payload bridge (explicit interval hypotheses). The Jacobi sin formula (`JacobiOscillator.lean`), constant speed, ray-law derivative, and the punctured consumer chain (`CartanPunctured.lean` etc.) all stand ready.

THE ASSEMBLY (rigid-17's isolated statement, now with the payloads live): the endpoint chart-metric evaluation on Jacobi values — `G(z(t))(J_w(t), J_{w'}(t))` — via: integrate the payload-fed transverse Gauss variation identity from 0 to t (initial pairing from the anchor data), insert the sin formulas, produce the WEIGHT identity in rigid-14/16's corrected punctured shape; combine with radial (constant speed) and cross (integrated Gauss orthogonal) terms into the PUNCTURED WEIGHTED SOURCE ENDPOINT EXPANSION for any constant-curvature-1 `g`.

Deliverables, in a NEW file `Poincare/Global/CartanAssembly.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE WEIGHT IDENTITY (endpoint Jacobi pairing).
2. THE PUNCTURED SOURCE EXPANSION (the exact consumer hypothesis).
3. 🎯 THE UNCONDITIONAL LOCAL ISOMETRY (instantiate `CartanPunctured.lean`'s case-split consumer).
4. Report `harness/reports/M5-rigid-19_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanAssembly` and report the actual result. Commit your work.
