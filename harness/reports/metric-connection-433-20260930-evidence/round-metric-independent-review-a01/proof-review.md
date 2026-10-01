# Independent round-metric proof-body review

Reviewer: `exact_target_migration`. Candidate author: root orchestrator.
Base: `37628ffa5cf60c2ab90994452279aaf1bc82dab4`.
Reviewed candidate SHA256: `3708d528df92dd840e68f48c7f458c341cc8093b1f692cd503b31e77edd51541`.
Worktree: `/Users/mjkang/.codex/worktrees/round-metric-433/poincare`.

## Review conclusion

No actionable finding within the sealed migration scope. The candidate repairs only the four permitted proof bodies. This report is independent review evidence, not Task acceptance, merge, commit, full retained-root compatibility or completion certification.

The immutable whole-source mask guard passes. A second independently implemented declaration-block comparison checks17 declarations, including the private finrank instance. All seven alias/data-definition blocks are byte-identical: RoundSphere3, RoundSphereAmbient4, RoundSphereModel3, the actual inclusion mfderiv, both-slot ambient pullback inner form, model-inner function and complete bundled metric constructor. All untouched proofs, private instance, imports/preamble and every public header are unchanged. Only inner_apply, inner_mfderiv_eq, modelInner_contDiff and inner_contMDiff proof bodies differ.

The evaluation proof uses ordinary definitional reflexivity. The using! changes affect ordinary proof elaboration for existing definitionally equal dictionaries; no option, kernel/trust switch, new instance or computational data appears in the diff. Fresh Lean checks the resulting proof terms.

## Coordinate proof

Candidate lines199-220 retain the original eventual-neighborhood argument. `chart_source_mem_nhds RoundSphereModel3 x₀` supplies actual points x in the chart source. Lines201-204 derive `hx_triv : x ∈ (trivializationAt ... x₀).baseSet` by `simpa using hx`. This is genuine local chart membership, not a new theorem premise or fabricated global invertibility hypothesis. The same membership is used in `inCoordinates_apply_eq₂` and at line220 for BOTH `Trivialization.symmL_apply` rewrites, one per bilinear slot.

Mathlib's checked lemma at Topology/VectorBundle/Basic.lean428 requires exactly membership in the trivialization baseSet and concludes `e.symmL R b y = e.symm b y`. Thus the new change/rw argument identifies the actual partial inverse with its continuous linear version where that identification is valid. Both slots, the actual inclusion differential and the original tangent-bundle coordinate models are retained. The final equality remains inside the existing eventual germ used by hmodel.congr_of_eventuallyEq.

All16 exact exported interfaces and universe arities pass the fresh frozen probe. Smoothness remains explicit ENat.top coerced into WithTop ENat. Norms, topologies, regularity orders and hypotheses are unchanged; in particular this is smooth C-infinity and does not silently substitute analytic omega.

## Fresh independent gates

- `env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/RoundSphereMetric.lean`: exit0,5.890573s.
- `env LEAN_NUM_THREADS=1 lake env lean harness/v2/state/upstream-verification-20260930/round-metric-433-task-a01/FrozenMigrationProbe-a03.lean`: exit0,17.287071s. All16 FROZEN_CONTRACT_OK and16 AXIOM_CONTRACT_OK markers independently validated against the sealed Task list, including the actual data declarations. All dependency safety checks reject unsafe/partial constants and permit only propext, Classical.choice and Quot.sound.
- Immutable `check-scope.py`: exit0 with PRESERVED_FULL_SURROUNDING_SOURCE `749926a80852fb3450a2f6a9431940cb5e065dc3e8b2073d2424e610a2133720`.
- Exact scoped forbidden-token scan: exit1 with no matches.
- `git diff --check`: exit0.

Every fresh gate binds the same candidate hash. HEAD, source bytes, sealed definition-context hashes and dirty-only-RoundSphereMetric status were stable throughout this review. The source, diff, context hashes, exact cwd/argv/environment overrides, command exits/timings and full transcripts are preserved append-only. Existing warnings concern unchanged APIs/proofs and a deprecated spelling in the immutable probe.

The root reported its already-running scoped build completed successfully and the artifact was ready before the independent compiler/probe runs. The reviewer did not duplicate that build, launch any other build/helper agent, mutate source, commit, merge or accept.

## Integration boundary

This is a retained-root version-compatibility review of the existing metric on the fixed standard sphere. It introduces no arbitrary-manifold source, universal Hamilton input, smoothing result or core existence closure. Root still owns independent serial integration/full retained-root/exact final completion gates.
