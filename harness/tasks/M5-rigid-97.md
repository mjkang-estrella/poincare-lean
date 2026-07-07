Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-97: uniform εlin — the ball-uniform PL shrink breaks the order

Context: `harness/reports/M5-rigid-96_blocked.md` (READ FIRST): `εlin` is produced AFTER `T`/`v` are fixed — the order blocks `T < εlin`. THE RESOLUTION (uniformity): the linearized PL shrink `εlin` is determined by the COEFFICIENT BOUNDS along the base curve (`PLPackages.lean`'s construction — READ what its εlin depends on: sup of Γ-related quantities along the hosted flow) — and those bounds are UNIFORM over `v` in a compact ball (the base flows live in a compact tube — the compact-tube uniformity machinery: `GeodesicDerivative.lean`'s uniform remainders, `UniformNormalRadius.lean`'s Lebesgue pattern, `GeodesicDependence.lean`). PROVE: a uniform `εlin_min > 0` valid for ALL `v` in a closed ball (extract the ball-uniform coefficient bound; the PL shrink formula is monotone in the bound). THEN: shrink the `v`-ball so the hosted `T(v) = ‖v‖/(δ/2) < εlin_min` (choose the ball radius `< δ/2·εlin_min`) — the order breaks: `T < εlin` holds for every `v` in the final ball. Feed `SmallTCommon/IntervalAlign`'s machinery → the selectors fire → the master bundle closes → the assembly → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/UniformShrink.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-97_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.UniformShrink` and report the actual result. Commit your work.
