Read harness/worker_contract.md first and obey it strictly.

# Task M2-deturck-2: GOAL 9 — the DeTurck vector field construction

Context: `Poincare/Global/DeTurck.lean` (report `harness/reports/M2-deturck-1_done.md`) landed `lieDerivMetricAt`, `IsClosedRicciDeTurckSolutionAt`, the zero-field reduction iff, and the short-time/pullback interfaces. Its isolated next task (see the report's sketch) is the actual DeTurck vector field: the `g`-trace of the connection difference `Γ(g) − Γ(bg)` against a fixed background metric. LEGACY CONSTRAINT unchanged: genuine `Global/` vocabulary only; do not import/reference the quarantined legacy interface packages.

Deliverables, in a NEW file `Poincare/Global/DeTurckField.lean` (do NOT edit any existing file, incl. `Poincare.lean`):

1. CONNECTION DIFFERENCE, pointwise: for `g bg : ClosedSmoothRiemannianMetric n M` (or `3` if generality blocks — say so) and the canonical extension frame used throughout the M3 campaign (`extend`-frame; see `traceMetricVariationAt` / `CovariantDerivative.scalarCurvatureAt` Gram machinery in `Global/ScalarVariation.lean` / the CovariantDerivative API), define the difference values `(g.leviCivita (extend … j) x) (extend … i x) − (bg.leviCivita (extend … j) x) (extend … i x) : TM x` and package the `g`-Gram-inverse-weighted trace
   `deTurckVectorFieldAt g bg x : TM x` — the invariant spelling of `W^k = g^{ij} (Γ(g)^k_{ij} − Γ(bg)^k_{ij})`. REUSE the existing Gram-frame/trace machinery; do not re-derive it. Spelling freedom sanctioned; the classical trace semantics is frozen — document the exact final formula in the report.
2. SELF-DIFFERENCE SANITY: `deTurckVectorFieldAt g g x = 0` (each difference summand vanishes).
3. FAMILY + GAUGED-FLOW SPECIALIZATION: `deTurckVectorField (gt : ℝ → …) (bg) (t) : ∀ x, TM x := fun x => deTurckVectorFieldAt (gt t) bg x`; `def DeTurckVectorFieldRegularAt gt bg t : Prop := ClosedC2TangentField (deTurckVectorField gt bg t)` (honest Prop, no instances); `def IsDeTurckGaugedFlowAt (gt) (bg) (t₀) (x) : Prop := IsClosedRicciDeTurckSolutionAt gt (fun t => deTurckVectorField gt bg t) t₀ x` with the definitional unfolding lemma.
4. STATIC SANITY: with `gt = const g`, `bg = g`, the gauged-flow predicate at Ricci-flat static metrics reduces to the already-proven static flow clause (compose deliverable 2, the zero-field reduction iff from `Global/DeTurck.lean`, and `static_ricciFlat_flowClause`/`isClosedRicciFlowSolutionAt_const_of_ricciFlat`). CAREFUL: the reduction iff needs the FIELD to be zero — deliverable 2 gives exactly that for `bg = g`; note `funext` plumbing.
5. Report `harness/reports/M2-deturck-2_{done|blocked}.md`: final signatures + next decomposition (chart formula for the field; regularity of `deTurckVectorField` from metric smoothness — the `ClosedC2TangentField` discharge; then the Ricci–DeTurck equation with THIS field as the strict-parabolicity target).

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.DeTurckField` and report the actual result. Commit your work.
