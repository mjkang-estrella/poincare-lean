Read harness/worker_contract.md first and obey it strictly.

# Task M5-sphere-1: GOAL 7 opener — pinched limit → Einstein → constant scalar (survey items 1+2)

Read `harness/reports/M-frontier-survey.md` (the goal-7 shape, items 1-2 of 5). On main: the equality-iff-Einstein pinching lemma (`scalarAt_sq_le_nat_mul_ricciNormSqAt` + its equality case, RicciNorm.lean from goal 1's era), `tracelessRicciNormSqAt` + zero-iff-Einstein (ivey-1), the 3D decomposition theorem (`RiemannDeterminedByRicci3At_closedCurvature`), the contracted Bianchi machinery (goal 2), and the gradient/laplacian toolkit.

Deliverables (each its own commit):
1. **Global Einstein from vanishing traceless norm**: `tracelessRicciNormSqAt g x = 0` at every x ⟹ `g.ricciAt x u v = (scalarAt x / 3)·g.inner x u v` everywhere (the pointwise zero-iff-Einstein transported globally — mostly done pointwise; state the global Einstein predicate `IsEinstein3 g`).
2. **The global Schur bridge**: on a closed connected 3-manifold, `IsEinstein3 g ⟹ scalarAt is constant` — Schur's lemma: the contracted second Bianchi (`div Ric = ½ dR`, PROVEN on main from the goal-2/M4 campaigns) applied to Ric = (R/3)g gives `dR/3 = dR/2` ⟹ dR = 0 ⟹ (connectedness + vanishing differential) R constant. The vanishing-gradient-implies-constant step: Mathlib's `IsLocallyConstant`/`isPreconnected` machinery through the chart representative (extDerivFun = 0 everywhere ⟹ locally constant — check for the existing repo lemma; the model file may have it).
3. **Constant sectional curvature** (item 3): with Einstein + constant R, the 3D decomposition theorem collapses the curvature to the space-form Kulkarni–Nomizu form (`closedCurvatureFourLinearAt_spaceForm_coeff` was PROVEN as the space-form sanity check in pinch-4 — now derive its hypothesis from 1+2 rather than assuming it) → `HasConstantSectionalCurvature3 g (R/6)`-shape predicate + theorem.
4. Report + outlook (items 4-5: the space-form recognition interface and the conditional sphere theorem).

Standing protocols (pin new predicates on the space form + a non-example). No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
