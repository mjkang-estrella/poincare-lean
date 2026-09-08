# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/curvature-transport`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/CurvatureInstanceTransport.lean`; no vacuous definitions; report actual command output; commit
each verified lemma on the branch; report to `harness/reports/curvature-transport_{done|blocked}.md`.
Stop conditions as in `harness/tasks/M5-glob-69.md` (proved, or strongest verified partial plus one exact
resisting `def` and a `target_of_<resisting>` theorem).

# Task: transport the Levi-Civita connection and constant sectional curvature across charted-space instances

Context. `harness/reports/M5-glob-72_statement_refutation.md` (why the Cartan development must run on a
controlled instance), `Poincare/Global/ControlledChartInstance.lean` (the controlled instance `inst'`, equal
maximal atlases, scalar smoothness transport), `Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean`
(read fully: `J`, `D`, `commonCharts`, `transport`, `transport_inner`, `tangentCoordinates_transport`,
`modelContMDiffAt_iff`). The metric is now transported; the chain also needs the curvature hypothesis.

Definitions to read: `ClosedSmoothRiemannianMetric.leviCivita` (`Poincare/Global/Curvature.lean`),
`levi_civita_unique` / `levi_civita_exists` (`Poincare/Global/LeviCivita.lean`, `LeviCivitaExistence.lean`),
`IsMetricCompatible`, Mathlib `CovariantDerivative` and `ContMDiffCovariantDerivative`,
`curvatureOp` / `HasConstantSectionalCurvature3` (`Poincare/Global/ScalarVariation.lean` near line 22319; find the
exact definition and every definition it unfolds to), and how vector fields `Π x, TangentSpace I x` and their
smoothness (`ContMDiff` of sections of the tangent bundle) enter.

Setting as in the transport module: `{M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
[IsManifold I ∞ M] (inst' : ChartedSpace E M) (h : inst'.atlas ⊆ maximalAtlas inst)`, with the `IsManifold`
instance for `inst'` from `ControlledChartInstance.isManifold_and_maximalAtlas_eq`, and
`g' := RiemannianMetricInstanceTransportGeometric.transport inst' h g`.

Targets (frozen), in order; commit each:
1. Vector-field transport: define `transportField (X : Π x, TangentSpace I x) : Π x, TangentSpace I x` for
   `inst'` by `x ↦ (J x).symm (X x)` (or the direction that makes the bundle trivializations match — derive it
   from `tangentCoordinates_transport`), and prove `ContMDiff` of a tangent-bundle section transfers between the
   instances under this map (generalize `modelContMDiffAt_iff` / `transportedInner_contMDiff` from the hom bundle
   to the tangent bundle).
2. Connection transport: define the conjugated covariant derivative `∇'_X Y := transportField (∇_{X'} Y')` with
   `X', Y'` the inverse transports, prove it is a `CovariantDerivative` for `inst'`, that it is torsion-free and
   `IsMetricCompatible g'`, hence by uniqueness `g'.leviCivita = ∇'` (state the exact equality the repository's
   `levi_civita_unique` gives).
3. Curvature transport: `HasConstantSectionalCurvature3 g' 1 ↔ HasConstantSectionalCurvature3 g 1` (or the one
   direction the chain needs: from `g` to `g'`).
4. Consumer: `UnitConstantCurvatureSphereRecognition3 M` for `inst` follows from the same statement for `inst'`
   (the conclusion `Nonempty (M ≃ₜ RoundSphere3)` is instance-independent; the hypothesis `g` with unit curvature
   transports to `g'` with unit curvature). State and prove
   `unitConstantCurvatureSphereRecognition3_of_controlled (hrec : @UnitConstantCurvatureSphereRecognition3 M _ _ _ inst' _ _ _ _) : UnitConstantCurvatureSphereRecognition3 M`
   with the instance arguments spelled out; combine with
   `ControlledChartInstance.exists_controlled_chartedSpace_of_compatibleMetric` so that the recognition problem for
   an arbitrary instance reduces to the recognition problem for some controlled instance.
If step 2 resists (for example the repository's covariant-derivative bundling needs smoothness data in a specific
form), deliver steps 1 and the exact resisting `def` with `target_of_<resisting>` for steps 2–4.
