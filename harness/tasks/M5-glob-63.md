Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-63: LASER — the selector, ONLY

Context: `harness/reports/M5-glob-62_blocked.md` (READ FIRST — the VERBATIM selector + cross-point transfer demands). ⚠️ SCOPE: EXACTLY the selector, nothing downstream. (1) DEFINE `q ↦ ζ_q` (the hosted doubly-augmented base at `q` — `Classical.choose` over the per-point existential from the hosted flow machinery — identify WHICH existing theorem provides it per ball point: the `UniformFlowExport/SecondDischarge` exports), `q ↦ Ω_q` (`OmegaGronwall.exists_hosted_thirdVariation_solution_family_on_paired_base`'s choose), `q ↦ D_q` (`HostedCLM`'s construction at `Ω_q`); (2) their `choose_spec` facts restated as the selector's defining lemmas; (3) THE CROSS-POINT TRANSFER: for `q, q'` nearby, the SELECTED `D_q, D_{q'}` satisfy the Grönwall bound — the paired-base bound (`OmegaGronwall`) is stated for a SPECIFIC pair construction; the selected objects at `q, q'` coincide with that pair's components by PL/linearODE UNIQUENESS (same ODE + same initial data ⟹ same solution — the uniqueness lemmas identify any two valid choices) ⟹ the bound transfers. Report `harness/reports/M5-glob-63_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TheSelector.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TheSelector` and report the actual result. Commit your work.
