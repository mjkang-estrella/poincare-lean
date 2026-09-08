# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/hamilton-front-mission`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files except to add one import line to
`Poincare.lean` (alphabetical among the Global imports); no vacuous definitions (a Prop-valued field that could
be `True` is forbidden); report actual command output; commit on the branch; report to
`harness/reports/hamilton-front-mission_{done|blocked}.md`.

# Task: register the Hamilton analytic front as machine-checked obligations

Read first: HANDOFF.md sections "2026-09-07 Boundary correction" and the older "2026-09-04 Formal Profile"
section; docs/PROOF_WORKFLOW.md; `harness/v2/missions/unit-recognition.json` (the model to copy);
`scripts/theorem_registry.py` and `scripts/tests/test_theorem_registry.py`;
`Poincare/Global/CartanTwoNeighborhoodDevelopment.lean` (how universal closed statements were written for
the Cartan boundary); `Poincare/Global/NormalizedFlowFormalProfilePositiveEinstein.lean` (the constructor
`NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl`
and its siblings), `Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean`
(`CompactReferenceMetricTensorFamilyData`), `Poincare/Global/EinsteinInterface.lean`
(`PositiveEinsteinMetric3`, `hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3`), and
`Poincare/Global/SphereTheorem.lean` (`HamiltonConvergencePinchedLimit3`).

Facts (verify each with `lake env lean` on a scratch file): the Hamilton front's remaining open inputs are the
hypotheses of that constructor — `reaction` (whose only producer chain needs `HamiltonPinchingCoreData3`, which
has no producer), `compactTensorReferenceControl : CompactReferenceMetricTensorFamilyData reaction.K reaction.metric`,
`hequicontinuous`, `hpointwiseCompact`, and `scalarSubordinateGeometry`. Find the exact chain from the
constructor's output to `PositiveEinsteinMetric3 M` and then to `HamiltonConvergencePinchedLimit3 M`.

Deliverables, in one new module `Poincare/Global/HamiltonFrontStatements.lean`:
1. A structure `HamiltonFrontInputs (M : Type u) [instances]` bundling exactly the constructor's open inputs
   with their exact types (no extra Prop fields), and a closed universal Prop
   `UniversalHamiltonFrontInputsStatement : Prop := ∀ (N : Type u) [instances], Nonempty (HamiltonFrontInputs N)`.
2. A closed universal Prop `UniversalHamiltonConvergenceStatement : Prop := ∀ (N : Type u) [instances],
   HamiltonConvergencePinchedLimit3 N` (the analytic wall's endpoint), and
   `UniversalPositiveEinsteinStatement` similarly.
3. Checked theorems: `positiveEinsteinMetric3_of_hamiltonFrontInputs : HamiltonFrontInputs M → PositiveEinsteinMetric3 M`
   (through the constructor and the existing chain), `universalPositiveEinstein_of_universalHamiltonFrontInputs`,
   `universalHamiltonConvergence_of_universalHamiltonFrontInputs`, and the composition with the existing
   `poincareConjecture_of_positiveEinstein_of_unitRecognition` or `poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods`
   to `PoincareConjecture.{u}` from the universal inputs statement plus the Cartan H1/H2 universal statements.
   Docstrings must say plainly that the inputs are open and what each means.
4. `harness/v2/missions/hamilton-front.json`, modeled on the unit-recognition mission: obligation
   `hamilton-front-inputs` (expected type symbol = the inputs statement), checked node = the universal
   reduction, endpoint obligation `Poincare.universal_hamilton_convergence` with type symbol
   `UniversalHamiltonConvergenceStatement`; fill `expected_statement_sha256` from
   `python3 scripts/theorem_registry.py fingerprint --mission harness/v2/missions/hamilton-front.json`
   after checking the statements; then `python3 scripts/theorem_registry.py graph --mission ... --require-closed`
   must exit 2 with the two obligations open and the reduction `checked_with_hypotheses`.
5. Add one paragraph to HANDOFF.md under the 2026-09-07 sections pointing at the mission, and a line in
   HARNESS_STATUS.md.

Acceptance (run and paste): `lake build Poincare.Global.HamiltonFrontStatements`; the forbidden-token grep on the
new file (must be empty); `#print axioms` for every new theorem (exactly propext, Classical.choice, Quot.sound);
`LEAN_NUM_THREADS=1 lake env lean Poincare.lean` after wiring the import; the registry commands above with
exit codes; `python3 -m unittest discover -s scripts/tests`.
