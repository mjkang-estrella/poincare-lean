# Hamilton front mission worker result

Date: 2026-09-07. Base: `aa82826aec916ad9339e2da1049f80009cdf2c7a`.
Branch: `worker/hamilton-front-mission`. Worker implementation complete;
independent orchestrator acceptance and integration remain pending.

## Result and exact mathematical boundary

`Poincare/Global/HamiltonFrontStatements.lean` bundles exactly the five
constructor arguments with their original dependent types. The compact
parameter universe remains independent: `HamiltonFrontInputs.{u, v}` and
`UniversalHamiltonFrontInputsStatement.{u, v}`. The positive-Einstein and
Hamilton endpoint statements have only universe `u`. All three statements
are closed universal propositions, with no ambient manifold or instances.
The inputs statement quantifies compatible measurable and Borel instances;
the reductions choose the canonical Borel structure to remove these from
the endpoint hypotheses. No extra fields or unproved declarations were added.

The exact existing chain used by the new reduction is:

1. `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl`.
2. Its `positiveEinsteinMetric3` theorem calls `toFiniteTimePositiveEinsteinAnalyticData3`, which composes `toFiniteTracelessEnergyPositiveEinsteinAnalyticData3` with `NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.toFiniteTimePositiveEinsteinAnalyticData3`.
3. `NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3` yields `PositiveEinsteinMetric3 M`.
4. `hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3` yields `HamiltonConvergencePinchedLimit3 M`.
5. The new Poincare composition uses `poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods` with universal Cartan H1 and H2, reaching `PoincareConjecture.{u}` conditionally.

The reaction producer found by repository search is
`NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3`.
Its source record contains
`NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3` and a
positive pinching coefficient gap. The core contains normalized-flow existence,
compact parameterization, positive scalar/mean-scalar controls, and the Hamilton
Ricci eigenvalue floor. No unconditional core producer was found. The eventual
and quantitative near-round records are different, still conditional inputs.
The absence-of-producer claim is a source-search finding, not a Lean theorem of
nonexistence. Lean checked the constructor and producer signatures in the
scratch probe below. Each of the five arguments is retained as an open input;
this registration does not solve Hamilton analysis or Cartan H1/H2.

Only the requested new Lean module and one root import were added on the Lean
side. The mission pins the input and endpoint definitions. HANDOFF and
HARNESS_STATUS point to this worker result. No existing Lean definition or
proof was edited.

## Acceptance commands and actual output

Raw command logs, the scratch sources, complete registry JSON exports, and
source-search output are retained at `/private/tmp/hamilton-front-evidence`.
The build log contains replayed warnings from existing dependencies; the new
module's focused check emitted no diagnostics. The build output below is its
final two lines, not the full dependency-warning log.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonFrontStatements.lean
exit_code=0
(no output)

$ LEAN_NUM_THREADS=1 lake build Poincare.Global.HamiltonFrontStatements
✔ [3856/3856] Built Poincare.Global.HamiltonFrontStatements (14s)
Build completed successfully (3856 jobs).
exit_code=0

$ rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HamiltonFrontStatements.lean
exit_code=1
(no matches)

$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/hamilton-front-evidence/axioms.lean
'Poincare.positiveEinsteinMetric3_of_hamiltonFrontInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.universalPositiveEinstein_of_universalHamiltonFrontInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.universalHamiltonConvergence_of_universalHamiltonFrontInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.poincareConjecture_of_hamiltonFrontInputs_of_two_neighborhoods' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HamiltonFrontInputs.{u, v} (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] : Type (max u (v + 1))
Poincare.UniversalHamiltonFrontInputsStatement.{u, v} : Prop
Poincare.UniversalPositiveEinsteinStatement.{u} : Prop
Poincare.UniversalHamiltonConvergenceStatement.{u} : Prop
exit_code=0

$ LEAN_NUM_THREADS=1 lake env lean Poincare.lean
exit_code=0
(no output)

$ git diff --check
exit_code=0
(no output)
```

The axiom probe contains `#print axioms` for each of the four new theorems,
followed by `#check` for the structure and the three closed statements.
Every theorem has exactly `[propext, Classical.choice, Quot.sound]`.

```text
$ python3 scripts/theorem_registry.py fingerprint --mission harness/v2/missions/hamilton-front.json
exit_code=0
```

The `pins` member of the actual JSON output, copied to the mission after
checking the statement definitions:

```json
{
  "hamilton-front-inputs": "e1e11cd30496b37d3465bb42383c6b27b4366aa73183e5e695cf82051afe0303",
  "hamilton-convergence": "90dba5085f3a9bcc6bd6ef1746b920308ce135ef4ddaf8ddc2f196dd3cf0c700"
}
```

```text
$ python3 scripts/theorem_registry.py graph --mission harness/v2/missions/hamilton-front.json --require-closed
exit_code=2
```

Selected fields from the actual graph JSON:

```json
{
  "nodes": [
    {
      "id": "hamilton-front-inputs",
      "state": "open"
    },
    {
      "id": "hamilton-front-reduction",
      "state": "checked_with_hypotheses"
    },
    {
      "id": "hamilton-convergence",
      "state": "open"
    }
  ],
  "open_obligations": [
    "hamilton-front-inputs",
    "hamilton-convergence"
  ],
  "endpoint_verified": false,
  "project_complete": false
}
```

The checked reduction's exact exported type is:

```lean
∀ (hInputs : Poincare.UniversalHamiltonFrontInputsStatement.{u, v}), Poincare.UniversalHamiltonConvergenceStatement.{u}
```

The requested Python suite initially exposed an existing output-order flake:

```text
$ python3 -m unittest discover -s scripts/tests
..................F..........................
======================================================================
FAIL: test_agrees_with_real_ripgrep (test_rg_fallback.RgFallbackTest.test_agrees_with_real_ripgrep)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/private/tmp/poincare-workers/hamilton-front-mission/scripts/tests/test_rg_fallback.py", line 81, in test_agrees_with_real_ripgrep
    self.assertEqual(self.run_shim(*case), (real.returncode, real.stdout), case)
    ~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Tuples differ: (0, 't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n') != (0, 't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n')

First differing element 1:
't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n'
't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n'

- (0, 't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n')
+ (0, 't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n') : ['-n', 'alpha', 't1.txt', 't2.txt']

----------------------------------------------------------------------
Ran 45 tests in 11.148s

FAILED (failures=1)
exit_code=1
```

The fallback test and shim are byte-for-byte unchanged from the base commit.
Extracting those two files with `git show aa82826aec916ad9339e2da1049f80009cdf2c7a:<path>`
and running that base test reproduces the same failure:

```text
F......
======================================================================
FAIL: test_agrees_with_real_ripgrep (test_rg_fallback.RgFallbackTest.test_agrees_with_real_ripgrep)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "/private/tmp/hamilton-front-evidence/base/scripts/tests/test_rg_fallback.py", line 81, in test_agrees_with_real_ripgrep
    self.assertEqual(self.run_shim(*case), (real.returncode, real.stdout), case)
    ~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Tuples differ: (0, 't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n') != (0, 't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n')

First differing element 1:
't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n'
't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n'

- (0, 't1.txt:1:alpha one\nt1.txt:3:alpha three\nt2.txt:2:alpha four\n')
+ (0, 't2.txt:2:alpha four\nt1.txt:1:alpha one\nt1.txt:3:alpha three\n') : ['-n', 'alpha', 't1.txt', 't2.txt']

----------------------------------------------------------------------
Ran 7 tests in 0.605s

FAILED (failures=1)
exit_code=1
```

An unchanged rerun of the exact requested command passed:

```text
$ python3 -m unittest discover -s scripts/tests
.............................................
----------------------------------------------------------------------
Ran 45 tests in 11.161s

OK
exit_code=0
```

A supplementary run with a temporary ripgrep config containing `--threads=1`
also passed. No repository test or script was modified:

```text
$ RIPGREP_CONFIG_PATH=/private/tmp/hamilton-front-evidence/ripgrep.conf python3 -m unittest discover -s scripts/tests
.............................................
----------------------------------------------------------------------
Ran 45 tests in 11.366s

OK
exit_code=0
```

## Scratch signature probe

```text
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/hamilton-front-evidence/probe.lean
exit_code=0
```

Actual output:

```text
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl.{u,
    v}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M]
  [BorelSpace.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (reaction : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M)
  (compactTensorReferenceControl :
    Poincare.CompactReferenceMetricTensorFamilyData.{u, v}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.K.{u, v} reaction)
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.metric.{u, v} reaction))
  (hequicontinuous :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot.{u} 3 M),
      Equicontinuous.{0, 0, 0} fun t =>
        ⇑(Poincare.metricEntryThirdJetProfile.{u}
            (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.gt.{u, v} reaction ↑t)
            slot))
  (hpointwiseCompact :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot.{u} 3 M) (z : Poincare.ClosedSmoothModel 3),
      ∃ Q,
        And (IsCompact.{0} Q)
          (∀ (t : ↑(Set.Ici.{0} 0)),
            Membership.mem.{0, 0} Q
              ((Poincare.metricEntryThirdJetProfile.{u}
                  (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.gt.{u, v} reaction
                    ↑t)
                  slot)
                z)))
  (scalarSubordinateGeometry :
    (t : ↑(Set.Ici.{0} 0)) →
      Poincare.FiniteSubordinateHausdorffLaplacianGeometry.{u}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.gt.{u, v} reaction ↑t) fun y =>
        Poincare.ClosedSmoothRiemannianMetric.scalarAt.{u}
          (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.gt.{u, v} reaction ↑t) y) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v} M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.toFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u,
    v}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M]
  [BorelSpace.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v} M) :
  Poincare.NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v} M
Poincare.NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.toFiniteTimePositiveEinsteinAnalyticData3.{u,
    v}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M]
  [BorelSpace.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (data : Poincare.NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v} M) :
  Poincare.NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v} M
Poincare.NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3.{u, v} {M : Type u}
  [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M] [BorelSpace.{u} M]
  [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (data : Poincare.NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v} M) :
  Poincare.PositiveEinsteinMetric3.{u} M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.positiveEinsteinMetric3.{u,
    v}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M]
  [BorelSpace.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v} M) :
  Poincare.PositiveEinsteinMetric3.{u} M
Poincare.hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3.{u} {M : Type u} [TopologicalSpace.{u} M]
  [T2Space.{u} M] [SecondCountableTopology.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M] (h : Poincare.PositiveEinsteinMetric3.{u} M) :
  Poincare.HamiltonConvergencePinchedLimit3.{u} M
structure Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v} (M : Type u)
  [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M] [BorelSpace.{u} M]
  [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M] : Type (max u (v + 1))
number of parameters: 11
fields:
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.K.{u, v} : Type v
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.topologicalSpaceK.{u,
    v} : TopologicalSpace.{v}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.K.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.compactSpaceK.{u,
    v} : CompactSpace.{v} (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.K.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u,
    v} : Real → Poincare.ClosedSmoothRiemannianMetric.{u} 3 M
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.metric.{u,
    v} : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.K.{u, v} self →
      Poincare.ClosedSmoothRiemannianMetric.{u} 3 M
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.parameter.{u,
    v} : ↑(Set.Ici.{0} 0) → Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.K.{u, v} self
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.parameterContinuous.{u,
    v} : Continuous.{0, v}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.parameter.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.realizesFlow.{u,
    v} : ∀ (t : ↑(Set.Ici.{0} 0)),
      Eq.{u + 1}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.metric.{u, v} self
          (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.parameter.{u, v} self t))
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self ↑t)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.meanScalarFloor.{u, v} : Real
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.meanScalarFloor_pos.{u,
    v} : LT.lt.{0} 0
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.meanScalarFloor.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.meanScalarLower.{u,
    v} : ∀ (t : ↑(Set.Ici.{0} 0)),
      LE.le.{0}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.meanScalarFloor.{u, v} self)
        (Poincare.meanScalar.{u}
          (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self ↑t))
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.normalizedFlow.{u,
    v} : ∀ (t : Real),
      Membership.mem.{0, 0} (Set.Ici.{0} 0) t →
        ∀ (x : M),
          Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u}
            (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self) t x
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.compactFiniteAtlasChartFrameDensityData.{u,
    v} : Poincare.CompactFiniteAtlasChartFrameDensityData.{u}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.jointMetricEntries.{u,
    v} : ∀ (t : Real) (x : M),
      Poincare.MetricEntriesJointContDiffAt.{u}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self) t x 3
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon.{u, v} : Real
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon_pos.{u,
    v} : LT.lt.{0} 0
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon_le_one_third.{u,
    v} : LE.le.{0}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon.{u, v} self)
      (1 / 3)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta.{u, v} : Real
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta_nonneg.{u,
    v} : LE.le.{0} 0
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta_le_two.{u,
    v} : LE.le.{0}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta.{u, v} self) 2
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta_admissible.{u,
    v} : LE.le.{0}
      (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingDelta.{u, v} self)
      (Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon.{u, v} self))
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.scalarPositive.{u,
    v} : ∀ (t : Real),
      Membership.mem.{0, 0} (Set.Ici.{0} 0) t →
        ∀ (x : M),
          LT.lt.{0} 0
            (Poincare.ClosedSmoothRiemannianMetric.scalarAt.{u}
              (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self t) x)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.ricciEigenvalueFloor.{u,
    v} : ∀ (t : Real),
      Membership.mem.{0, 0} (Set.Ici.{0} 0) t →
        Poincare.GlobalRicciEigenvalueFloor3.{u}
          (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.gt.{u, v} self t)
          (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.pinchingEpsilon.{u, v} self)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.finiteVolumeMeasureContinuous.{u,
    v} : Continuous.{v, u} fun k =>
      Poincare.closedMetricFiniteVolumeMeasure.{u}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.metric.{u, v} self k)
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.scalarJointContinuous.{u,
    v} : Continuous.{max u v, 0} fun p =>
      Poincare.ClosedSmoothRiemannianMetric.scalarAt.{u}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.metric.{u, v} self p.1) p.2
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.tracelessRicciNormSqJointContinuous.{u,
    v} : Continuous.{max u v, 0} fun p =>
      Poincare.ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt.{u}
        (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.metric.{u, v} self p.1) p.2
constructor:
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.mk.{u, v} {M : Type u}
    [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M] [BorelSpace.{u} M]
    [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
    [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
    [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M] (K : Type v) (topologicalSpaceK : TopologicalSpace.{v} K)
    (compactSpaceK : CompactSpace.{v} K) (gt : Real → Poincare.ClosedSmoothRiemannianMetric.{u} 3 M)
    (metric : K → Poincare.ClosedSmoothRiemannianMetric.{u} 3 M) (parameter : ↑(Set.Ici.{0} 0) → K)
    (parameterContinuous : Continuous.{0, v} parameter)
    (realizesFlow : ∀ (t : ↑(Set.Ici.{0} 0)), Eq.{u + 1} (metric (parameter t)) (gt ↑t)) (meanScalarFloor : Real)
    (meanScalarFloor_pos : LT.lt.{0} 0 meanScalarFloor)
    (meanScalarLower : ∀ (t : ↑(Set.Ici.{0} 0)), LE.le.{0} meanScalarFloor (Poincare.meanScalar.{u} (gt ↑t)))
    (normalizedFlow :
      ∀ (t : Real),
        Membership.mem.{0, 0} (Set.Ici.{0} 0) t → ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} gt t x)
    (compactFiniteAtlasChartFrameDensityData : Poincare.CompactFiniteAtlasChartFrameDensityData.{u} gt)
    (jointMetricEntries : ∀ (t : Real) (x : M), Poincare.MetricEntriesJointContDiffAt.{u} gt t x 3)
    (pinchingEpsilon : Real) (pinchingEpsilon_pos : LT.lt.{0} 0 pinchingEpsilon)
    (pinchingEpsilon_le_one_third : LE.le.{0} pinchingEpsilon (1 / 3)) (pinchingDelta : Real)
    (pinchingDelta_nonneg : LE.le.{0} 0 pinchingDelta) (pinchingDelta_le_two : LE.le.{0} pinchingDelta 2)
    (pinchingDelta_admissible :
      LE.le.{0} pinchingDelta (Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 pinchingEpsilon))
    (scalarPositive :
      ∀ (t : Real),
        Membership.mem.{0, 0} (Set.Ici.{0} 0) t →
          ∀ (x : M), LT.lt.{0} 0 (Poincare.ClosedSmoothRiemannianMetric.scalarAt.{u} (gt t) x))
    (ricciEigenvalueFloor :
      ∀ (t : Real),
        Membership.mem.{0, 0} (Set.Ici.{0} 0) t → Poincare.GlobalRicciEigenvalueFloor3.{u} (gt t) pinchingEpsilon)
    (finiteVolumeMeasureContinuous : Continuous.{v, u} fun k => Poincare.closedMetricFiniteVolumeMeasure.{u} (metric k))
    (scalarJointContinuous :
      Continuous.{max u v, 0} fun p => Poincare.ClosedSmoothRiemannianMetric.scalarAt.{u} (metric p.1) p.2)
    (tracelessRicciNormSqJointContinuous :
      Continuous.{max u v, 0} fun p =>
        Poincare.ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt.{u} (metric p.1) p.2) :
    Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v} M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3.{u,
    v}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [SecondCountableTopology.{u} M] [MeasurableSpace.{u} M]
  [BorelSpace.{u} M] [ChartedSpace.{0, u} (Poincare.ClosedSmoothModel 3) M]
  [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners 3) (↑Top.top.{0}) M] [CompactSpace.{u} M]
  [ConnectedSpace.{u} M] [SimplyConnectedSpace.{u} M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.{u, v} M) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M

```

## Next action

Independently rerun the recorded task gates from the base plus this diff and
review the exact five fields before acceptance. The mission graph must still
exit 2 with both obligations open. No task was marked accepted or merged by
this worker.
