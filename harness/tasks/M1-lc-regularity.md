Read harness/worker_contract.md first and obey it strictly.

# Task M1-lc-regularity: regularity of the canonical Levi-Civita connection

Context on main: `Poincare/Global/Curvature.lean` wraps the curvature layer for `g : ClosedSmoothRiemannianMetric n M` but must carry `[CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]` as a hypothesis, because no regularity theorem exists for the Koszul construction `CovariantDerivative.leviCivitaConnection` (Poincare/KoszulExistence.lean). Your goal: prove that instance from `g`'s smoothness.

Recommended path (verify against the actual code first):
1. Read the definition chain: `leviCivitaConnection` → `leviCivitaCovFun` → `leviCivitaValueAt` ← `koszulRHS` (KoszulExistence.lean) and the exact meaning of `CovariantDerivative.ContMDiffCovariantDerivative` (Mathlib CovariantDerivative/Basic.lean).
2. Check what regularity infrastructure the repo already has: `Poincare/LocalConnectionRegularity.lean`, `Poincare/Smoothability.lean`, `Poincare/ChartTransport.lean` (`chartLeviCivita_contMDiff` exists per earlier worker notes!), and any `contMDiff`-flavored lemmas inside KoszulExistence.lean itself. There may be a nearly-complete route already.
3. Target (in `Poincare/Global/LeviCivitaExistence.lean` or a new `Poincare/Global/LeviCivitaRegularity.lean` + root import):
   `instance/theorem closedLeviCivitaConnection_contMDiff (g : ClosedSmoothRiemannianMetric n M) : CovariantDerivative.ContMDiffCovariantDerivative (LeviCivitaExistence.closedLeviCivitaConnection g) 1`
   Prove the strongest order you can get cleanly (1 needed now; ∞ ideal). The mathematical content: the Koszul formula's value depends smoothly on the basepoint because g is smooth and the metric inverse of a smooth invertible bilinear form is smooth.
4. This may be genuinely hard. Decompose; commit each verified lemma separately; if blocked, commit partials + `harness/reports/M1-lc-regularity_blocked.md` with the precise obstruction and remaining sub-lemmas. Partial verified progress is a success outcome.

No sorry/axiom. `lake build`, commit, report declaration names.
