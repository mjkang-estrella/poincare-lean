Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-70: the decomposed assembly — three proven cases, one bilinear split

Context: `harness/reports/M5-rigid-69_blocked.md` (READ FIRST). PROVEN: the radial `t·speed²` law + the transverse `horth` feed (integrated Gauss) + the transverse-restricted endpoint variants (`OrthogonalityFeed.lean`, `SpeedGeneric.lean` additions). THE REMAINING BRIDGE: the radial/transverse-DECOMPOSED hosted endpoint assembly — for arbitrary `a, a'`, split at the anchor `a = ρ·v + w`, `a' = ρ'·v + w'` (`G(anchor)`-orthogonal decomposition — THE GRAM ALGEBRA EXISTS: `CartanPullback.lean` rigid-9 radial/transverse decomposition; the linearized families are ADDITIVE (`LinearizedAdditivity.lean`) so `Ψ_a = ρ·Ψ_v + Ψ_w` — bilinearity expands the endpoint pairing into 4 terms: radial-radial (the `t·speed²`/speed facts — `SpeedPackage/TheLocalIsometry.lean`), radial-transverse ×2 (ZERO — the `horth` feed), transverse-transverse (the restricted variants). Assemble the FULL bilinear hosted endpoint pairing formula for arbitrary `a, a'`; the SAME on the target (aligned; `L` preserves the decomposition — alignment intertwining, `CartanPullback.lean`'s preservation lemmas); the two full formulas match through `L` (the equality chain / common-speed consumer, `SourcePackage/SpeedGeneric.lean`) → 🎯 `cartanMap_isLocalIsometry`. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/DecomposedAssembly.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-70_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.DecomposedAssembly` and report the actual result. Commit your work.
