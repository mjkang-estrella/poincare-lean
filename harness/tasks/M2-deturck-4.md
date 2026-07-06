Read harness/worker_contract.md first and obey it strictly.

# Task M2-deturck-4: GOAL 9 — the DeTurck summand C² lemma

Context: `harness/reports/M2-deturck-3_blocked.md` isolates the SINGLE missing lemma behind the DeTurck field regularity discharge:

```lean
theorem deTurckVectorFieldSummand_closedC2
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ (ClosedSmoothModel n))) :
    ClosedC2TangentField (deTurckVectorFieldSummand g bg i)
```

(`deTurckVectorFieldSummand`, the tensorial rewrite through `CovariantDerivative.difference`, and the reducer `deTurckVectorFieldRegularAt_holds_of_summand_regularity` are in `Poincare/Global/DeTurckFieldRegularity.lean`.) The report names the two genuine bridges expected: (a) `C²` smoothness of the difference section `x ↦ (g.leviCivita.difference bg.leviCivita) x` from `leviCivita_contMDiff₂ g/bg` (the hom-bundle section-smoothness patterns of `Global/LeviCivitaRegularity.lean` / `LeviCivitaTransport.lean` are the templates); (b) `C²` smoothness of the raised basis field `x ↦ metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)` (Gram-inverse smoothness — mine the M3 Gram machinery in `Global/ScalarVariation.lean`).

Deliverables, in a NEW file `Poincare/Global/DeTurckSummandRegularity.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. The two bridge lemmas (or finer pieces — many small lemmas preferred), each standalone and named.
2. The frozen `deTurckVectorFieldSummand_closedC2` exactly as stated (general `n`; specialize only if genuinely blocked, and say so).
3. The unconditional payoff `theorem deTurckVectorFieldRegularAt_holds (gt) (bg) (t) : DeTurckVectorFieldRegularAt gt bg t` via the existing reducer.
4. Report `harness/reports/M2-deturck-4_{done|blocked}.md`; if blocked, isolate the next single missing statement.

Verify: `lake build Poincare.Global.DeTurckSummandRegularity` and report the actual result. Commit your work.
