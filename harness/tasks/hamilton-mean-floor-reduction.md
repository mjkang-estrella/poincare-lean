# Worker contract (plan-and-implement)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/hamilton-mean-floor-reduction`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files, `Poincare.lean`, audit scripts, missions, or ledgers; you may add EXACTLY ONE new Lean module, `Poincare/Global/HamiltonMeanFloorReduction.lean`, containing only proved reductions and statement definitions. Commit each verified item on your branch; report actual command output to `harness/reports/hamilton-mean-floor-reduction_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting statement and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only. Distinguish (a) proved in repo, (b) in Mathlib, (c) absent.

Context: read `HANDOFF.md` top section first. The open Hamilton obligation is `HamiltonReactionCore3Final` in `Poincare/Global/HamiltonReactionCoreFinal.lean` (forward-time normalized Ricci flow with joint C³ entries, compact realization with continuous jet profiles, positive mean-scalar floor `0 < c ∧ ∀ t : Ici 0, c ≤ meanScalar (gt t)`, uniform reaction domination). Mission `harness/v2/missions/hamilton-front.json`. Prior reports: `harness/reports/reaction-record-decomposition_done.md` (sections 2.3, 3, 4 on the mean floor and S9/S10), `harness/reports/ricci-flow-existence-interface-survey_done.md`.

# Task hamilton-mean-floor-reduction

Objective: replace the positive mean-scalar floor clause of `HamiltonReactionCore3Final` by hypotheses about the initial metric and the flow that the landed maximum-principle material discharges, and state the exact residual.

Landed material to study first (verify by grep and probe):
- `Poincare/Global/NormalizedFlowScalarLowerProfile.lean`: `exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove` (uniform pointwise scalar lower bound from positive initial scalar, a normalized Hamilton scalar evolution predicate `SatisfiesNormalizedHamiltonScalarEvolutionAt`, scalar C² and joint continuity, and a continuous normalization primitive bounded above) and everything else in that file.
- `Poincare/Global/ScalarMeanLowerBound.lean`: `meanScalar_pos_of_forall_scalarAt_ge` (pointwise floor gives mean floor).
- Producers of `SatisfiesNormalizedHamiltonScalarEvolutionAt` from `IsClosedNormalizedRicciFlowSolutionAt` plus regularity (search for `satisfiesNormalizedHamiltonScalarEvolutionAt_of_` and the unnormalized `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`, `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`; determine exactly what regularity they need and whether joint C³ metric entries (`MetricEntriesJointContDiffAt gt t x 3`) supply it via the landed `scalarAt_contMDiffAt_two_of_normalizedRicciFlow` and `timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three` in `HamiltonReactionEndpoint.lean` and `MetricFlowJointRegularity.lean`).
- What the "normalization primitive" is (the integral of the mean scalar, or of `(2/3) meanScalar`); whether "bounded above" follows from a nonpositive or bounded mean-scalar derivative (S9 `meanScalar_deriv_nonneg_...` has the opposite sign) or from a mean upper bound; and the landed mean-continuity results (`ClosedRicciFlowNormalization.continuousOn_meanScalar_of_ricciFlow` for unnormalized flows; find or prove the normalized analogue).

Required work, in order:
1. Prove, in the new module, the strongest theorem of this shape that the landed material supports:
   ```lean
   theorem meanScalar_floor_of_initial_scalar_pos
       (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
       (hflow : ∀ t ∈ Ici (0:ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
       (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
       (hinit : ∀ x, 0 < (gt 0).scalarAt x)
       <residual hypotheses, as few as possible, each named and justified> :
       ∃ c : ℝ, 0 < c ∧ ∀ t : Ici (0:ℝ), c ≤ meanScalar (gt t.1)
   ```
   with the section variables of `HamiltonReactionCoreFinal.lean`. If the normalization-primitive bound cannot be derived, keep it as an explicit hypothesis and say so.
2. Define `HamiltonReactionCore3Init M : Prop` = `HamiltonReactionCore3Final` with the floor clause replaced by `(∀ x, 0 < (gt 0).scalarAt x)` plus the residual hypotheses of step 1; prove `hamiltonReactionCore3Final_of_init`, `hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Init`, the universal statement `UniversalHamiltonReactionCoreInitStatement`, and `universalHamiltonConvergence_of_universalHamiltonReactionCoreInit`, mirroring `HamiltonReactionCoreFinal.lean`.
3. Report: the exact residual hypotheses with probed signatures, the classification of each (A derivable / B analysis / C unclear), and whether the uniform reaction domination clause admits a similar reduction to an initial pinching condition via the landed `hamilton_pinching_preserved` / `hamilton_eigenvalue_pinching_floor_preserved` (survey only for this item; do not implement).

Exact stop condition: step 1 and 2 theorems pass the gate; the report states the residual precisely. A core that keeps the floor clause under another name is only partial; say so.
