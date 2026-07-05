Read harness/worker_contract.md first and obey it strictly.

# Task M5-sphere-4: goal-7 items 4+5 — the space-form interface + THE CONDITIONAL SPHERE THEOREM

Read `harness/reports/M-frontier-survey.md` (goal-7 shape items 4-5) and `M5-sphere-3_done.md`. On main: `HasConstantSectionalCurvature3` + the unconditional theorem from vanishing traceless Ricci; the repo's TOPOLOGY LAYER (Poincare/Global/Statement.lean: `PoincareConjecture`; the quotient-covering/simply-connected machinery the survey references — TopologyExtraction.lean etc.; explore what exists).

Deliverables (each its own commit):
1. **The narrow interface** (survey item 4): `structure/def PositiveConstantCurvatureSpaceForm3` — the honest Prop packaging what constant-curvature space-form recognition requires: a closed connected simply-connected 3-manifold with a metric of constant sectional curvature k > 0 is isometric/homeomorphic to the round S³. State it as the NAMED HYPOTHESIS interface (this is the genuinely-hard differential-geometry input — Killing–Hopf; do NOT attempt its proof); non-vacuity note: it is a true mathematical statement (cite in docstring), and the interface is Prop-valued consumed downstream. Falsifier check: the statement must NOT be provable-false (e.g. check it doesn't accidentally quantify wrongly — validate the shape on the round-sphere instance direction if cheap).
2. **THE CONDITIONAL SPHERE THEOREM** (survey item 5): `theorem sphere_of_pinched_limit`: [SimplyConnectedSpace M] + closed connected 3-manifold + `tracelessRicciNormSqAt ≡ 0` + `scalarAt > 0` somewhere + the interface ⟹ `Nonempty (M ≃ₜ ThreeSphere)` (match the exact sphere type used by `PoincareConjecture` in Statement.lean — READ it first and target the same codomain so the chain composes). Route: the unconditional constant-curvature theorem gives k = R₀/6 > 0; feed the interface.
3. **The statement-chain composition**: connect to the Statement layer — a theorem of the shape `PoincareConjecture`-conclusion-for-M under [flow-limit hypotheses + the two honest interfaces (Hamilton convergence upstream + space-form recognition)] — the first end-to-end conditional path from Ricci-flow estimates to the repo's Poincaré statement. Be explicit and honest about every named interface in the docstring.
4. Done-report + honest interface inventory.

Standing protocols. No sorry/axiom (interfaces are HYPOTHESES, never axioms). `lake build Poincare` (full project). Report names.
