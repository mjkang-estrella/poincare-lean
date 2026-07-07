Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-31: the domain shrink — all radii intersected, the blocks land

Context: `harness/reports/M5-rigid-30_blocked.md` (READ FIRST). The single mismatch: the bridge (`CartanCoefficientBridge.lean`) quantifies `v` over the exp-homeo source, while the proven ingredients (Jacobi pairing `CartanIsometryPackage/CartanIsometryTheorem.lean`, constant speed, integrated Gauss, flow-derivative identification) carry cutoff-one PL radius/interval hypotheses (`‖v₀‖ < δ`, `t ∈ Icc 0 τ`). THE FIX (the geo-30/geo-7 shrink pattern — replay it): construct the SHRUNK BALL — a `δ' > 0` with `ball 0 δ' ⊆` (exp-homeo source) ∩ (the cutoff-one flow's velocity ball) ∩ (the interval horizon reaches `t = ‖v‖` for `‖v‖ < δ'`, i.e. `δ' ≤ τ`) — radii intersection arithmetic over the existing existence statements (`ExponentialLocalHomeo.lean`, `GeodesicLengthFinal.lean` shrunk-flow package, `ExponentialFixedTime.lean`); then the CONVERSION THEOREM: for `v` in the shrunk ball (`v ≠ 0`), the endpoint evaluation at `t = ‖v‖` satisfies every block hypothesis — including the flow-derivative identification of `D(expAt)` images with `J(‖v‖)` values (the ray law + homogeneity convert the `t·v`-parameterization; `ExponentialRayLaw*.lean`).

Deliverables, in a NEW file `Poincare/Global/CartanDomainShrink.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE SHRUNK BALL + the conversion theorem (the blocks' hypotheses at `t = ‖v‖` for shrunk-ball `v ≠ 0`).
2. THE BLOCK INSTANTIATIONS on the shrunk ball (source + target) via the conversion.
3. 🎯 THE LOCAL ISOMETRY on the shrunk ball (the bridge applied; restate the bridge's conclusion restricted to the shrunk ball — a smaller normal ball is still a normal ball).
4. Report `harness/reports/M5-rigid-31_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanDomainShrink` and report the actual result. Commit your work.
