Read harness/worker_contract.md first and obey it strictly.

# Task M1-ricci-flow-wrapper: closed-manifold pointwise Ricci-flow solution wrapper

Context on main: read `harness/reports/manifold_assets.md` §"Live frontier" lemma 4 — this task is that lemma. `Poincare/RicciFlowEquation.lean` defines `CovariantDerivative.IsRicciFlowSolutionAt` (a genuine pointwise PDE: d/dt g_t(Z x, w) = -2·ricciTraceAt) and `Poincare/KoszulExistence.lean` has `isRicciFlowSolutionAt_of_metric`. `Poincare/Global/{RiemannianContext,LeviCivita,LeviCivitaExistence,Curvature}.lean` give `ClosedSmoothRiemannianMetric`, the canonical `g.leviCivita` (= `closedLeviCivitaConnection`), `g.ricciAt`, `g.scalarAt`.

Deliverable: NEW file `Poincare/Global/RicciFlow.lean` (+ root import):

1. `def IsClosedRicciFlowSolutionAt (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop` — the pointwise Ricci flow condition for a time-family of closed smooth metrics, using the canonical Levi-Civita connection of `gt t` at each time. Wire it to `CovariantDerivative.IsRicciFlowSolutionAt` (definitional or an iff lemma — whichever is cleanest and NON-OPAQUE; provide the unfolding lemma).
2. `theorem isClosedRicciFlowSolutionAt_of_metric` — the specialization of `KoszulExistence.isRicciFlowSolutionAt_of_metric` to this context: given the explicit flow equation hypothesis (deriv of `(gt t).inner x (Z x) w` = -2·ricciTraceAt of the canonical connection), conclude `IsClosedRicciFlowSolutionAt`. Discharge every dischargeable side condition (symmetry, nondegeneracy, pairing regularity) from `g`'s data as previous Global files did; document any that must be carried.
3. A static sanity instance: an Einstein or Ricci-flat closed metric family that is constant in time — specialize `isRicciFlowSolutionAt_const_of_ricciFlat` (RicciFlowEquation.lean) to `ClosedSmoothRiemannianMetric` if the hypotheses can be honestly stated (if it needs Ricci-flatness as hypothesis, that's fine — hypotheses must be genuine, conclusions genuine).
4. Blocked pieces → commit greens + `harness/reports/M1-ricci-flow-wrapper_blocked.md`.

No sorry/axiom. `lake build Poincare.Global.RicciFlow`, commit, report declaration names.
