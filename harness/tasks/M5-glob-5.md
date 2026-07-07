Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-5: germ determinacy — the conjugation makes both maps linear

Context: `harness/reports/M5-glob-4_blocked.md` (READ FIRST — the VERBATIM `RigidStepCompatible` demand). PROVEN: the IFT partial homeomorphism with pullback (`IsometryConsumers.lean`); the exp-conjugation `expChart_symm_cartanChartMap_expChart_eq_tangentAlignment` (`CartanNormalCoords.lean` — the Cartan map read in exp charts IS the linear alignment). THE DETERMINACY: two Cartan-type maps with the same value and tangent action at a point agree on the common normal ball — VIA THE CONJUGATION: each map is `exp_target ∘ L_i ∘ exp_source⁻¹` on its ball; same value + tangent action ⟹ `L_1 = L_2` (linear maps agreeing as tangent actions — the alignment's defining fields) ⟹ the maps agree where both conjugations hold. ASSEMBLE: (1) the overlap agreement theorem (the conjugation on the intersection ball — shrink radii); (2) produce `CartanChain.ChainState.RigidStepCompatible` for a re-anchored step (READ its exact fields in `CartanChain.lean` — the agreement + the re-anchored germ data from `CartanContinuation.lean`'s re-anchoring); (3) feed `CartanContinuation.twoStep_*` and `CartanChain.chain_step_restr_eqOnSource` → the chain fires along subdivisions → as far toward the global `Φ` as closes. Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-glob-5_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/GermDeterminacy.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.GermDeterminacy` and report the actual result. Commit your work.
