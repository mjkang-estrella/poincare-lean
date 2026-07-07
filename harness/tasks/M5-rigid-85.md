Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-85: solutions replace PL — additivity dissolves hplLinear

Context: `harness/reports/M5-rigid-84_blocked.md` (READ FIRST — the verbatim `hplLinear`: centered `IsPicardLindelof` packages at `(0, T⁻¹•(w+w'))` with common constants + membership fields). THE DISSOLUTION BY LINEARITY: the centered packages exist to produce/uniquify the solution with initial data `(0, T⁻¹(w+w'))` — but that solution IS `Ψ_w + Ψ_{w'}` (endpoint/pointwise ADDITIVITY, `LinearizedAdditivity.lean` — the sum of solutions of a LINEAR system solves it with summed initial data; the proof exists) and uniqueness is `linearODE_solution_uniqueOn_Icc` (`CoefficientEvolution.lean`) — NO centered PL construction needed. THE TASK: an ALTERNATIVE bounded transverse feed variant consuming SOLUTIONS + uniqueness instead of centered PL packages — replay `BoundedPackage.lean`'s bounded feed proof (READ where it uses `hplLinear`: presumably to obtain the `w+w'` solution for the polarization step) with the additivity-provided sum solution substituted; membership fields for the sum from the individual memberships (triangle inequality on the closed balls — enlarge `aLin` by 2× if needed). ADDITIVE only (NEW file; edits to `BoundedPackage.lean` only as new variants if unavoidable). Then the feed completes at the hosted datum → the transverse blocks → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/SolutionsFeed.lean`. Report `harness/reports/M5-rigid-85_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SolutionsFeed Poincare.Global.BoundedPackage` (BOTH must pass) and report the actual result. Commit your work.
