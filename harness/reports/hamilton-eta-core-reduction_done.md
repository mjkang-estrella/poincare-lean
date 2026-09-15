# Hamilton Eta core reduction: done

Date: 2026-09-15. Branch: `worker/hamilton-eta-core-reduction`.
Base: `8721fff786dbdff2037e69927addfb628f1a1462`.
Proof head: `7890e2d27f9c0d9303b00b57b5ed37ca393f8ee8`.

## Result

All three task items pass the worker gate. The one new Lean file is
`Poincare/Global/HamiltonEtaCoreReduction.lean`. Existing Lean sources,
`Poincare.lean`, and frozen contracts are unchanged.

`meanFloorFromEta` reproduces the survey's arithmetic theorem. Its sufficient
bound `d ≤ 2` includes the required `0 < d ≤ 1`. Nonnegativity of the Ricci
norm follows from the landed traceless norm decomposition; choosing one point
on each positive-scalar slice gives `eta ≤ (4/3) meanScalar` and hence the
positive floor `(3/4) eta` on the whole forward ray.

The landed `HamiltonReactionCore3InitialPinchingEta` still contains both
Stokes and variance-energy clauses, so it does not already solve this task.
The new `HamiltonReactionCore3Eta` is that definition with those two clauses
deleted. A text comparison also confirms that it is exactly the pinned NS
core after deleting C, energy, scalar comparison, and the coefficient gap,
and adding the requested existential Eta residual. All retained clauses,
including compact realization and admissibility, are unchanged.

`hamiltonReactionCore3Final_of_eta` derives pointwise scalar positivity from
initial positivity, derives the mean floor from Eta, and applies the landed
normalization-gap reaction theorem after initial pinching preservation. Its
witnesses are `c := (3/4) eta` and `rate := eta`. The endpoint and universal
consumer mirror the landed core. There are six new declarations, all with
exactly `[propext, Classical.choice, Quot.sound]`.

The uniform Eta residual and existence of the retained flow data remain open
inputs. This is a conditional reduction, not an unconditional convergence or
Poincare proof. No root integration gate or merge was performed. Independent
orchestrator review is still required.

## Verification notes

Appendix C6 was extracted verbatim to `/tmp/hamilton-eta-core-evidence/eta-only.lean`
and compiled successfully before editing. The pinned definitions were printed
from Lean. Each item was compiled, checked for forbidden tokens and whitespace,
and checked for foundational dependencies before its commit.

The first item-3 log parser assumed one-line dependency output and raised
`AssertionError` because Lean wrapped the longer names' dependency lists.
Both Lean runs in that attempt exited 0; no proof failed. The corrected parser
normalizes whitespace inside each bracketed dependency list. Its complete
rerun passed. The original output is retained below. No compiler failures
occurred in this attempt.

Dependency probes concatenate the exact current module source with a
`#print axioms` command for every `theorem` and `def`; they do not rely on a
stale generated object for the new module. The final print probe similarly
appends `#print` commands for the core and its final-core consumer.

First review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
```

## Actual command output

### Scratch replay

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/eta-only.lean
theorem HamiltonResidualSurvey.meanFloorFromEta.{u} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ),
  d ≤ 2 →
    0 < eta →
      (∀ t ∈ Ici 0, ∀ (x : M), 0 < (gt t).scalarAt x) →
        (∀ t ∈ Ici 0,
            ∀ (x : M),
              2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤ 4 / 3 * Poincare.meanScalar (gt t)) →
          0 < 3 / 4 * eta ∧ ∀ (t : ↑(Ici 0)), 3 / 4 * eta ≤ Poincare.meanScalar (gt ↑t) :=
⋯
'HamiltonResidualSurvey.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem HamiltonResidualSurvey.finalCoreOfEta.{u, v} : ∀ {M : Type u} [inst : TopologicalSpace M] [inst_1 : T2Space M]
  [inst_2 : SecondCountableTopology M] [inst_3 : MeasurableSpace M] [inst_4 : BorelSpace M]
  [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [inst_9 : SimplyConnectedSpace M] (K : Type v) [inst_10 : TopologicalSpace K]
  [CompactSpace K] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Ici 0) → K) (e d eta : ℝ),
  Continuous parameter →
    (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) →
      (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
          Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) →
        (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
          (∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) →
            (∀ (x : M), 0 < (gt 0).scalarAt x) →
              1 / 6 < e →
                e ≤ 1 / 3 →
                  Poincare.GlobalRicciEigenvalueFloor3 (gt 0) e →
                    0 < d →
                      d ≤ 1 →
                        d ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * e - 1 / 3) →
                          0 < eta →
                            (∀ t ∈ Ici 0,
                                ∀ (x : M),
                                  2 * (2 - d) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
                                    4 / 3 * Poincare.meanScalar (gt t)) →
                              Poincare.HamiltonReactionCore3Final M :=
⋯
'HamiltonResidualSurvey.finalCoreOfEta' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

### Pinned definition print

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/pinned.lean
def Poincare.HamiltonStokesFreeReactionCore.HamiltonReactionCore3InitialPinchingNS.{u, v} : (M : Type u) →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                [CompactSpace M] → [ConnectedSpace M] → [SimplyConnectedSpace M] → Prop :=
fun M [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] =>
  ∃ K topK,
    ∃ (_ : CompactSpace K),
      ∃ metric gt parameter epsilon delta C,
        Continuous parameter ∧
          (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) ∧
            (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
                Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) ∧
              (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) ∧
                (∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
                  (∀ (x : M), 0 < (gt 0).scalarAt x) ∧
                    1 / 6 < epsilon ∧
                      epsilon ≤ 1 / 3 ∧
                        Poincare.GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
                          0 < delta ∧
                            delta ≤ 1 ∧
                              delta ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1 / 3) ∧
                                (∀ (t : ↑(Set.Ici 0)),
                                    Poincare.normalizedFlowScalarVarianceTrack gt ↑t ≤
                                      6 * Poincare.normalizedFlowTracelessRicciEnergyTrack gt ↑t) ∧
                                  (∀ t ∈ Set.Ici 0, ∀ (x : M), (gt t).scalarAt x ≤ C * Poincare.meanScalar (gt t)) ∧
                                    0 < 4 / 3 - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon ^ 2) * C
def Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinchingEta.{u, v} : (M :
    Type u) →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                [CompactSpace M] → [ConnectedSpace M] → [SimplyConnectedSpace M] → Prop :=
fun M [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] =>
  ∃ K topK,
    ∃ (_ : CompactSpace K),
      ∃ metric gt parameter epsilon delta,
        Continuous parameter ∧
          (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) ∧
            (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
                Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) ∧
              (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) ∧
                (∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
                  (∀ (x : M), 0 < (gt 0).scalarAt x) ∧
                    1 / 6 < epsilon ∧
                      epsilon ≤ 1 / 3 ∧
                        Poincare.GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
                          0 < delta ∧
                            delta ≤ 1 ∧
                              delta ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1 / 3) ∧
                                (∀ t ∈ Set.Ici 0, Poincare.ClosedLaplacianStokes (gt t) fun x => (gt t).scalarAt x) ∧
                                  (∀ (t : ↑(Set.Ici 0)),
                                      Poincare.normalizedFlowScalarVarianceTrack gt ↑t ≤
                                        6 * Poincare.normalizedFlowTracelessRicciEnergyTrack gt ↑t) ∧
                                    ∃ eta,
                                      0 < eta ∧
                                        ∀ t ∈ Set.Ici 0,
                                          ∀ (x : M),
                                            2 * (2 - delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
                                              4 / 3 * Poincare.meanScalar (gt t)
[exit 0]
```

### Initial item-1 elaboration

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 0]
```

### names.log

```text
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:30:theorem scalarAt_pos_of_initial_scalar_pos
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:76:theorem initial_pinching_preserved
Poincare/Global/RicciNorm.lean:194:theorem tracelessRicciNormSqAt_eq (x : M) :
Poincare/Global/RicciNorm.lean:207:theorem tracelessRicciNormSqAt_eq_pinchingGapAt_div
Poincare/Global/RicciNorm.lean:221:theorem tracelessRicciNormSqAt_nonneg (x : M) (hn : 0 < (n : ℝ)) :
Poincare/Global/RicciNorm.lean:231:theorem tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:105:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
Poincare/Global/ScalarVariation.lean:24929:theorem tracelessRicciNormSqAt_eq_diagonal_of_ricciEndoAt_eigenbasis
Poincare/Global/HamiltonReactionCoreFinal.lean:27:def HamiltonReactionCore3Final (M : Type u)
Poincare/Global/HamiltonReactionCoreFinal.lean:82:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:86:def HamiltonReactionCore3InitialPinchingEta (M : Type u)
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:116:theorem hamiltonReactionCore3Final_of_initialPinchingEta
Poincare/Global/EinsteinNormalization.lean:42:theorem tracelessRicciNormSqAt_eq_zero_of_forall_isEinsteinAt
Poincare/Global/HamiltonStokesFreeReactionCore.lean:31:def HamiltonReactionCore3InitialPinchingNS (M : Type u)
Poincare/Global/SphereTheorem.lean:118:def HamiltonConvergencePinchedLimit3 (M : Type u)
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
Poincare/Global/PinchedLimitInterface.lean:31:def HamiltonConvergencePinchedLimit3Core (M : Type u)
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:97:def GlobalRicciEigenvalueFloor3
Poincare/Global/HamiltonFrontStatements.lean:83:def UniversalHamiltonConvergenceStatement : Prop :=
```

### shape.log

```text
Core text equals pinned NS after removing C, energy, comparison and coefficient gap, then appending exactly the specified Eta residual.
```

### item1-gate.log

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 0]
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 1]
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/item1-probe.lean
'Poincare.HamiltonEtaCoreReduction.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
$ git diff --check
[exit 0]
$ rg -n ^(theorem|def)  Poincare/Global/HamiltonEtaCoreReduction.lean
26:theorem meanFloorFromEta
[exit 0]
```

### item1-commit.log

```text
[worker/hamilton-eta-core-reduction 11a550a9] Prove the uniform mean scalar floor from Eta
 1 file changed, 49 insertions(+)
 create mode 100644 Poincare/Global/HamiltonEtaCoreReduction.lean
```

### item2-gate.log

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 0]
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 1]
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/item2-probe.lean
'Poincare.HamiltonEtaCoreReduction.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonEtaCoreReduction.HamiltonReactionCore3Eta' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
$ git diff --check
[exit 0]
$ rg -n ^(theorem|def)  Poincare/Global/HamiltonEtaCoreReduction.lean
26:theorem meanFloorFromEta
51:def HamiltonReactionCore3Eta (M : Type u)
[exit 0]
```

### item2-commit.log

```text
[worker/hamilton-eta-core-reduction d6a04c07] Define the Eta-only Hamilton reaction core
 1 file changed, 28 insertions(+)
```

### item3-gate.log

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 0]
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 1]
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/item3-probe.lean
'Poincare.HamiltonEtaCoreReduction.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonEtaCoreReduction.HamiltonReactionCore3Eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonEtaCoreReduction.hamiltonReactionCore3Final_of_eta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.UniversalHamiltonReactionCoreEtaStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.universalHamiltonConvergence_of_universalHamiltonReactionCoreEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[exit 0]
```

### item3-final-gate.log

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 0]
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonEtaCoreReduction.lean
[exit 1]
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/item3-final-probe.lean
'Poincare.HamiltonEtaCoreReduction.meanFloorFromEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonEtaCoreReduction.HamiltonReactionCore3Eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonEtaCoreReduction.hamiltonReactionCore3Final_of_eta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.UniversalHamiltonReactionCoreEtaStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonEtaCoreReduction.universalHamiltonConvergence_of_universalHamiltonReactionCoreEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[exit 0]
$ git diff --check
[exit 0]
$ rg -n ^(theorem|def)  Poincare/Global/HamiltonEtaCoreReduction.lean
26:theorem meanFloorFromEta
51:def HamiltonReactionCore3Eta (M : Type u)
78:theorem hamiltonReactionCore3Final_of_eta
99:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta
106:def UniversalHamiltonReactionCoreEtaStatement : Prop :=
115:theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEta
[exit 0]
```

### item3-commit.log

```text
[worker/hamilton-eta-core-reduction 7890e2d2] Derive final reaction core and Hamilton convergence from Eta
 1 file changed, 46 insertions(+)
```

### Final definition and consumer print

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-eta-core-evidence/final-print.lean
def Poincare.HamiltonEtaCoreReduction.HamiltonReactionCore3Eta.{u, v} : (M : Type u) →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] →
                [CompactSpace M] → [ConnectedSpace M] → [SimplyConnectedSpace M] → Prop :=
fun M [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] =>
  ∃ K topK,
    ∃ (_ : CompactSpace K),
      ∃ metric gt parameter epsilon delta,
        Continuous parameter ∧
          (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) ∧
            (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
                Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) ∧
              (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) ∧
                (∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
                  (∀ (x : M), 0 < (gt 0).scalarAt x) ∧
                    1 / 6 < epsilon ∧
                      epsilon ≤ 1 / 3 ∧
                        Poincare.GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
                          0 < delta ∧
                            delta ≤ 1 ∧
                              delta ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1 / 3) ∧
                                ∃ eta,
                                  0 < eta ∧
                                    ∀ t ∈ Ici 0,
                                      ∀ (x : M),
                                        2 * (2 - delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
                                          4 / 3 * Poincare.meanScalar (gt t)
theorem Poincare.HamiltonEtaCoreReduction.hamiltonReactionCore3Final_of_eta.{u, v} : ∀ {M : Type u}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [inst_2 : SecondCountableTopology M] [inst_3 : MeasurableSpace M]
  [inst_4 : BorelSpace M] [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [inst_7 : CompactSpace M]
  [inst_8 : ConnectedSpace M] [inst_9 : SimplyConnectedSpace M],
  Poincare.HamiltonEtaCoreReduction.HamiltonReactionCore3Eta M → Poincare.HamiltonReactionCore3Final M :=
fun {M} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] h =>
  Exists.casesOn h fun K h =>
    Exists.casesOn h fun topK h =>
      Exists.casesOn h fun compactK h =>
        Exists.casesOn h fun metric h =>
          Exists.casesOn h fun gt h =>
            Exists.casesOn h fun parameter h =>
              Exists.casesOn h fun epsilon h =>
                Exists.casesOn h fun delta h =>
                  And.casesOn h fun hparam right =>
                    And.casesOn right fun hreal right =>
                      And.casesOn right fun hjet right =>
                        And.casesOn right fun hjoint right =>
                          And.casesOn right fun hflow right =>
                            And.casesOn right fun hinit right =>
                              And.casesOn right fun hepos right =>
                                And.casesOn right fun hele right =>
                                  And.casesOn right fun hpin right =>
                                    And.casesOn right fun hdpos right =>
                                      And.casesOn right fun hdle right =>
                                        And.casesOn right fun hadm right =>
                                          Exists.casesOn right fun eta h =>
                                            And.casesOn h fun heta hgap =>
                                              have hpos :=
                                                Poincare.NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
                                                  gt hjoint hflow hinit;
                                              And.casesOn
                                                (Poincare.HamiltonEtaCoreReduction.meanFloorFromEta gt delta eta
                                                  (le_of_not_gt fun a => Mathlib.Tactic.Linarith.lt_irrefl ⋯) heta hpos
                                                  hgap)
                                                fun hc hmean =>
                                                have hpres :=
                                                  Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
                                                    gt epsilon hjoint hflow hinit hele hpin;
                                                Exists.intro K (Exists.intro topK ⋯)
[exit 0]
```

## Reproduced survey scratch source

```lean
import Poincare
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace HamiltonResidualSurvey
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem meanFloorFromEta
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
    (hd : d ≤ 2) (heta : 0 < eta)
    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
  classical
  constructor
  · positivity
  · intro t
    let x : M := Classical.choice (inferInstance : Nonempty M)
    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
      norm_num at hU
      exact (div_nonneg (by positivity) (by norm_num)).trans hU
    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
    have h := hgap t.1 t.2 x
    linarith

theorem finalCoreOfEta
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (e d eta : ℝ)
    (hparam : Continuous parameter)
    (hreal : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2))
    (hj : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hf : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hi : ∀ x, 0 < (gt 0).scalarAt x)
    (he : 1/6 < e) (he' : e ≤ 1/3) (hpin : GlobalRicciEigenvalueFloor3 (gt 0) e)
    (hd : 0 < d) (hd' : d ≤ 1)
    (ha : d ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2*e-1/3))
    (heta : 0 < eta)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    HamiltonReactionCore3Final.{u,v} M := by
  have hp := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos gt hj hf hi
  obtain ⟨hc, hmean⟩ := meanFloorFromEta gt d eta (by linarith) heta hp hgap
  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved gt e hj hf hi he' hpin
  refine ⟨K, inferInstance, inferInstance, gt, metric, parameter, (3/4 : ℝ)*eta, eta,
    hparam, hreal, hc, hmean, hf, hj, heta, ?_, hjet⟩
  intro t ht x
  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
    (gt t) x (by linarith) (by linarith) hd.le ha (hp t ht x) ((hpres t ht).1 x) (hgap t ht x)
end HamiltonResidualSurvey
set_option pp.proofs false
#print HamiltonResidualSurvey.meanFloorFromEta
#print axioms HamiltonResidualSurvey.meanFloorFromEta
#print HamiltonResidualSurvey.finalCoreOfEta
#print axioms HamiltonResidualSurvey.finalCoreOfEta
```

## Final proof diff against recorded base

```diff
diff --git a/Poincare/Global/HamiltonEtaCoreReduction.lean b/Poincare/Global/HamiltonEtaCoreReduction.lean
new file mode 100644
index 00000000..ea00df1c
--- /dev/null
+++ b/Poincare/Global/HamiltonEtaCoreReduction.lean
@@ -0,0 +1,123 @@
+import Poincare.Global.HamiltonInitialPinchingReactionCoreReduction
+import Poincare.Global.HamiltonStokesFreeReactionCore
+
+/-!
+# Hamilton convergence from a uniform normalization gap
+
+The gap supplies both the positive mean floor and the reaction rate.
+Existence of a flow and compact realization with this gap remains an input.
+-/
+
+set_option autoImplicit false
+set_option linter.unusedSectionVars false
+noncomputable section
+open Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+universe u v
+namespace Poincare.HamiltonEtaCoreReduction
+variable {M : Type u} [TopologicalSpace M] [T2Space M]
+  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+/-- Eta bounds the mean scalar from below on every positive-scalar slice.
+The arithmetic only needs `d ≤ 2`, hence applies to the core's `0 < d ≤ 1`. -/
+theorem meanFloorFromEta
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
+    (hd : d ≤ 2) (heta : 0 < eta)
+    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
+    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
+      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
+        (4/3 : ℝ)*meanScalar (gt t)) :
+    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
+  classical
+  constructor
+  · positivity
+  · intro t
+    let x : M := Classical.choice (inferInstance : Nonempty M)
+    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
+    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
+    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
+      norm_num at hU
+      exact (div_nonneg (by positivity) (by norm_num)).trans hU
+    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
+      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
+    have h := hgap t.1 t.2 x
+    linarith
+
+/-- The initial-pinching Eta core with the Stokes and variance-energy clauses
+removed. The uniform normalization gap is the sole residual estimate. -/
+def HamiltonReactionCore3Eta (M : Type u)
+    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+    [MeasurableSpace M] [BorelSpace M]
+    [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
+  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
+    (metric : K → ClosedSmoothRiemannianMetric 3 M)
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (parameter : Ici (0 : ℝ) → K) (epsilon delta : ℝ),
+      Continuous parameter ∧
+      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
+      (∀ slot : MetricEntryThirdJetSlot 3 M,
+        Continuous (fun p : K × ClosedSmoothModel 3 ↦
+          metricEntryThirdJetProfile (metric p.1) slot p.2)) ∧
+      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
+      (∀ x, 0 < (gt 0).scalarAt x) ∧
+      1/6 < epsilon ∧ epsilon ≤ 1/3 ∧
+      GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
+      0 < delta ∧ delta ≤ 1 ∧
+      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) ∧
+      (∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
+        2 * (2-delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
+          (4/3 : ℝ) * meanScalar (gt t))
+
+/-- Eta supplies the final core with mean floor `3 * eta / 4` and rate `eta`. -/
+theorem hamiltonReactionCore3Final_of_eta
+    (h : HamiltonReactionCore3Eta.{u, v} M) :
+    HamiltonReactionCore3Final.{u, v} M := by
+  rcases h with ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta,
+    hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
+    hdpos, hdle, hadm, eta, heta, hgap⟩
+  letI : TopologicalSpace K := topK
+  haveI : CompactSpace K := compactK
+  have hpos := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
+    gt hjoint hflow hinit
+  obtain ⟨hc, hmean⟩ := meanFloorFromEta gt delta eta (by linarith) heta hpos hgap
+  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
+    gt epsilon hjoint hflow hinit hele hpin
+  refine ⟨K, topK, compactK, gt, metric, parameter, (3/4 : ℝ) * eta, eta,
+    hparam, hreal, hc, hmean, hflow, hjoint, heta, ?_, hjet⟩
+  intro t ht x
+  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
+    (gt t) x (by linarith) (by linarith) hdpos.le hadm (hpos t ht x)
+    ((hpres t ht).1 x) (hgap t ht x)
+
+/-- The Eta-only core reaches the Hamilton pinched-limit endpoint. -/
+theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta
+    (h : HamiltonReactionCore3Eta.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
+  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
+    (hamiltonReactionCore3Final_of_eta h)
+
+/-- Open existence obligation for Eta-only cores on closed simply connected
+smooth three-manifolds with compatible Borel structures. -/
+def UniversalHamiltonReactionCoreEtaStatement : Prop :=
+  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
+    [MeasurableSpace N] [BorelSpace N]
+    [ChartedSpace (ClosedSmoothModel 3) N]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
+      HamiltonReactionCore3Eta.{u, v} N
+
+/-- Universal Eta-only cores imply universal Hamilton convergence. -/
+theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEta
+    (h : UniversalHamiltonReactionCoreEtaStatement.{u, v}) :
+    UniversalHamiltonConvergenceStatement.{u} := by
+  intro N _ _ _ _ _ _ _ _
+  letI : MeasurableSpace N := borel N
+  letI : BorelSpace N := ⟨rfl⟩
+  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta (h N)
+
+end Poincare.HamiltonEtaCoreReduction
```
