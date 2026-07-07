Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-27: THE ASSEMBLY — from the integrated system to the local isometry

Context: `harness/reports/M5-rigid-26_done.md` (READ FIRST). EVERYTHING IS PROVEN; this is composition: (1) the pointwise bridge `chart_linearized_state_feeds_norm_system_at` (`JacobiNormClose.lean`) quantified along the cutoff-one flow interval (`GeodesicLengthFinal.lean` zone membership; `JacobiOscillator.lean` interval oscillator) discharges the hypotheses of (2) `closed_norm_system_eq_pinned_on_Icc` (`JacobiIntegrated.lean`) ⟹ `a(t) = sin²t·|w|²_anchor` for the ACTUAL Jacobi scalars of any constant-curvature-1 `g`; (3) polarize (`JacobiNormSystem.lean`'s algebra + flow-derivative linearity in `w` — prove `J_{w+w'} = J_w + J_{w'}` from linearized uniqueness if not yet explicit) ⟹ the transverse-transverse pairing; (4) radial-radial (constant speed) + radial-transverse (integrated Gauss) ⟹ THE EXP-CHART COEFFICIENT FORMULAS for `g`; (5) both sides + the conjugation `expChart_symm_cartanChartMap_expChart_eq_tangentAlignment` (`CartanNormalCoords.lean`) + the alignment's metric intertwining ⟹ THE PULLBACK ⟹ 🎯 `cartanMap` IS A LOCAL ISOMETRY (state cleanly; the exp-chart formulation is the deliverable — the old chart-weight consumers are superseded on this route).

Deliverables in a NEW file `Poincare/Global/CartanIsometryTheorem.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-rigid-27_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanIsometryTheorem` and report the actual result. Commit your work.
