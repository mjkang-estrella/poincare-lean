# Reaction record decomposition

Date: 2026-09-08. Base: `5a3dab3991e9e09d01a2f60957aa16b1110f0277`.
Branch: `worker/reaction-record-decomposition`.

The audit is complete and the analytic reduction is partial. The new module proves density integrability and density-derivative measurability, then reconstructs the chart-frame record using only joint metric regularity and a local integrable bound. It defines `Poincare.HamiltonReactionCore3`, reconstructs the reaction record, and proves its finite-energy, Hamilton, and universal Hamilton consequences. It does not construct a flow or discharge a mission.

The whole chart-density record is **not** proved from joint C³ entries alone. The neighborhood and integrable dominating function remain explicit. The three compact-family continuity assumptions and the positive mean-scalar floor also remain explicit. This core reduces the reaction record's internal inputs; it is not smaller than the already landed finite-energy interface in every respect.

Only `Poincare/Global/HamiltonReactionCoreReduction.lean` and this report are changed. The specific worker contract overrides the general branch-prefix and HANDOFF-edit instructions. Existing Lean files, frozen contracts, root imports, audits, missions, ledgers, and HANDOFF are unchanged. The worktree was clean at the recorded base; `git status --short --branch`, `git worktree list --porcelain`, and `git rev-parse HEAD` confirmed the isolated branch. Mathlib is `7175569c842f9164564bd76ff8b207e7b4705522`; the toolchain file reads `leanprover/lean4:v4.30.0-rc2`.

I read HANDOFF's top section and the prior decomposition first, then README, PROJECT_MAP, the supplied task, its named Lean context and parent records, the plan-3 style reference, the missions, and the relevant v2 contract. Lean probes, not the older prose classifications, determine the results below.

## 1. Evidence and classification conventions

A means a proved derivation from the retained inputs, including existing producers reused by the new constructor. B means the coherent existence/estimate obligation still requires analysis not produced by the audited interfaces. C means the candidate implication has not been proved; no logical independence or counterexample is claimed. A classification of a data witness concerns its compatibility with the other fields: choosing an arbitrary type, real number, or constant map would not solve the coupled record.

Source anchors, all checked by `rg` and scratch Lean probes:

| ID | Location and checked declarations | Meaning |
| --- | --- | --- |
| S1 | `HausdorffFiniteAtlasChartFrameReduction.lean`: `exists_finiteExtendedChartCover`, `compactFiniteExtendedChartCover`, `FiniteExtendedChartCover.hasDerivAt_inverseChartDensity`; the three chart-frame record definitions | Genuine finite cover, exact density first variation, actual field types. |
| S2 | `HausdorffFiniteAtlasRestrictedAreaFormula.lean`: `FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula`, `FiniteExtendedChartCover.hausdorffChartDensityEquality`, `FiniteExtendedChartFrameMeasureData.ofDensityIntegrable` | Area formulas and chart measure equality are landed, not assumptions still requiring proof. |
| S3 | `HausdorffInverseChartGramContinuity.lean`: `continuous_inverseChartPullbackVolumeDensity`; `VolumeFinitenessComparison.lean`: `volumeMeasure_isFiniteMeasure` | Spatial density continuity and finite metric volume. |
| S4 | `MetricFlowJointRegularity.lean`: `MetricEntriesJointContDiffAt.of_le`, `timeDifferentiableAt_of_metricEntriesJointContDiffAt_one` | Joint C³ implies the pointwise time differentiability needed by density variation. |
| S5 | `NormalizedFlowCompactMeanEnergyMeasureContinuity.lean`: `continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint` | Weak finite-measure continuity and the two joint integrand continuities imply invariant-pair continuity. It does not assume compactness of K; spatial compactness supplies the integration control. |
| S6 | `NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean`: `normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici` | Reaction domination, the actual normalized equation, joint entries, moving-volume variation, and energy measurability give finite forward energy. |
| S7 | `HamiltonFiniteEnergyFlowInterface.lean`: `finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3`, `hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3` | Landed conditional adapters, reused after reconstructing the smaller core's missing fields. |
| S8 | `NormalizedFlowInvariantPairJointContinuity.lean`: `continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three` | Joint curvature continuity on **ℝ × M for gt**, not on arbitrary K × M. |
| S9 | `NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean`: `meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack` | Requires moving total-scalar and volume derivatives and the extra inequality V ≤ 6E. |
| S10 | `NormalizedFlowScalarLowerProfile.lean`: `exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove` | A genuine maximum-principle floor theorem, requiring pointwise initial positivity and a bounded normalization primitive, plus the printed regularity/evolution inputs. |

Mathlib supplies `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`, `MeasureTheory.integrable_const_mul_iff`, `MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure`, `measurable_of_tendsto_metrizable`, `HasDerivAt.tendsto_slope_zero_right`, and `tendsto_one_div_add_atTop_nhds_zero_nat`. These are general measure/calculus results, not a normalized Ricci-flow existence or mean-positivity theorem. The additive Haar name is generated by Mathlib's additive translation; its source annotation and uses, as well as its Lean signature, were checked.

“Absent” below means no producer found in the searched repository and pinned Mathlib, not a mathematical nonexistence theorem. Exact project domain-name searches in Mathlib returned no matches. No external library version or web claim is used.

## 2. Every reaction-record field

The immediate field list comes from the actual constructor in the base probe, reproduced in the evidence appendix. The temporal domains are preserved: normalized flow and reaction domination are forward-time; joint entries and chart-density bounds are required at every real time.

| Field | Class | Dependency finding |
| --- | --- | --- |
| `K` | B, coupled realization | A compact parameter family realizing a suitable long-time flow is still unproduced. Arbitrarily choosing a carrier does not establish the later fields. |
| `topologicalSpaceK` | B, coupled realization | Choosing a topology alone is elementary; a topology satisfying compactness and the required invariant continuity is part of the unproduced realization. |
| `compactSpaceK` | B | No compactness theorem for the required realized smooth family follows from the other retained raw maps. |
| `gt` | B | No suitable global normalized flow is constructed. |
| `metric` | B | No smooth compact limit family realizing the orbit is constructed. |
| `parameter` | B, coupled realization | Remains part of the orbit realization witness. |
| `parameterContinuous` | C | Neither a topology on metric-valued maps nor an inverse/quotient property is supplied. The other raw maps do not give a checked continuity producer. Retained. |
| `realizesFlow` | B, coupled realization | Exact metric equality along forward times remains an input, not merely equality of scalar invariants. |
| `meanScalarFloor` | B, coupled lower bound | The compatible positive floor is unproduced; choosing an arbitrary real number does not solve this field together with its inequalities. |
| `meanScalarFloor_pos` | B | Retained positivity. It does not follow from a possibly negative lower bound. |
| `meanScalarLower` | B; C for the positive-initial-mean candidate | S9 and S10 have extra hypotheses, detailed below. Neither supplies the requested floor from positive initial mean alone. |
| `normalizedFlow` | B | The section-tested normalized PDE remains an input on all forward times. Neither joint regularity nor reaction inequalities state that PDE. |
| `compactFiniteAtlasChartFrameDensityData` | C as a whole; A for removed subfields | The new constructor derives it from joint entries and the exact local integrable-bound clause below. No density integrability, area formula, derivative measurability, or time differentiability is retained as input. |
| `jointMetricEntries` | B for the unknown global flow | All-real-time joint C³ regularity remains an input. S4 and S8 derive consequences, not this existence/regularity premise. |
| `reactionDecayRate` | B, coupled estimate | No compatible coercive rate is produced. |
| `reactionDecayRate_pos` | B | A strictly positive uniform rate is still required. |
| `actualReactionDomination` | B | The geometric reaction estimate is not derived from normalized flow and joint regularity alone. S6 consumes it. |
| `finiteVolumeMeasureContinuous` | C | Retained on K. Compactness of K and continuity of `parameter` do not provide a metric-family continuity hypothesis. |
| `scalarJointContinuous` | C on K; A on the time family | S8 proves continuity for gt on ℝ × M. It does not extend that function to arbitrary extra points of K or control the supplied metric map there. |
| `tracelessRicciNormSqJointContinuous` | C on K; A on the time family | Same domain distinction as the scalar field. Retained on K. |

### 2.1 Inside the chart-density record

| Component | Class | Exact finding |
| --- | --- | --- |
| Finite genuine chart cover, measurable pieces and inverse charts | A, landed | S1 chooses the cover from compactness, with the existing measurable bookkeeping. No cover witness is added to the core. |
| `measureData.areaFormula` | A, landed | S2 supplies it for every metric/time, including negative times. |
| `measureData.density_integrable` | A, new proof | `HamiltonReactionCoreReduction.inverseChartDensity_integrable` uses S2/S3 and finite weighted mass. It works in every dimension n, and does not assume compact coordinate pieces or bounded coordinate density. |
| `domination.densityDerivative_aestronglyMeasurable_at` | A, new proof | `HamiltonReactionCoreReduction.densityDerivative_measurable` gives full measurability. The constructor obtains AE strong measurability from it. Difference quotients at steps 1/(k+1) are measurable by S3 and converge pointwise by S1/S4. |
| `domination.timeDifferentiable` | A, landed derivation installed in new constructor | S4 applied at each inverse-chart point, lowering order 3 to 1. No separate time-differentiability assumption remains. |
| `timeSet`, `domination.timeSet_mem` | C as coupled bound selection | A neighborhood by itself is trivial, but one compatible with the uniform chartwise bound is unproved. The residual existential retains this choice explicitly. |
| `domination.dominatingFunction` | C | An integrable function valid throughout one time neighborhood and across a whole coordinate piece remains unproduced. |
| `domination.dominatingFunction_integrable` | C | Retained for that bound. It is distinct from the now-proved integrability of the density itself. |
| `domination.densityDerivative_bound` | C | Retained with the original order ∀ t, ∃ neighborhood, ∃ bound, ∀ i, AE z, ∀ τ in the neighborhood. No point-dependent neighborhood is substituted. |

`HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound` constructs both parent records and the full compact chart-frame record from the residual bound. Every class-A subfield above is actually installed in that proof. Existing S1/S2/S4/S5 results were reused rather than copied into alias theorems.

The attempted route to remove the last bound is a compact-time-strip bound for the intrinsic trace of the metric time variation, followed by comparison of the moving density with its density at the base time. Joint local smoothness is promising, but I did not prove the global comparison and integrable envelope. A finite genuine chart cover does not say that every disjointized coordinate domain is compact. Bounding a continuous density by a constant on such a domain is not a justified shortcut. The report retains this as C, not as a claimed missing parabolic-existence theorem.

### 2.2 Parent-record and finite-energy interface audit

The reaction-to-measure parent produces finite energy through S6. The measure-to-compact-mean parent derives pair continuity through S5. The other parent fields are the same witnesses, equalities and lower bounds; their propagation is not an existence result.

| Conjunct of `HamiltonFiniteEnergyFlowExistence3` | Class | Finding |
| --- | --- | --- |
| Forward normalized PDE | B | Retained, then copied from the reconstructed reaction record. The landed Hamilton consumer does not use this conjunct, but this task preserves the flow-existence meaning of the interface. |
| Forward integrability of total traceless energy | A from the reaction core; B from a bare arbitrary flow | S6 and the reconstructed chart record give volume variation; the retained parameter/measure/integrand continuity gives energy measurability. No finite-energy hypothesis is added to the core. |
| Exact forward metric realization | B | Same unproduced compatible realization, preserved by the adapter. |
| Continuous mean-energy pair on K | A from S5's three retained continuities; C from compactness plus a raw metric family | Compactness alone says nothing about continuity of an arbitrary map into invariants. S5 supplies the derivation with its actual hypotheses. |
| `0 < c` | B | Same retained positive floor. |
| Uniform forward lower bound for the mean | B; positive-initial-mean candidate C | Same retained lower bound. Neither finite energy nor raw compactness directly gives strict positivity of all limiting means. |

The existential witnesses `gt`, `K`, its topology/compactness, `metric`, `parameter`, and `c` have the corresponding classifications in the reaction table. This finite-energy interface does not itself require `parameterContinuous`.

### 2.3 Positive initial mean and the maximum principle

The search found real results, but no producer for the requested implication from positive initial **mean** scalar alone. S9 assumes both moving integral derivatives and V ≤ 6E. Its proof uses the mean derivative numerator `2 * E - (1 / 3) * V`; positivity of the current or initial mean does not assign a sign to that numerator. Other inspected monotonicity routes accept a monotonicity/derivative-sign assumption.

S10 is a different sufficient route. It requires scalar curvature positive at every initial point, together with a normalization primitive whose increments have a uniform upper bound. A positive average is not that pointwise premise, and the bounded primitive is also extra. The exact signatures of both results are printed below. I do not infer either additional hypothesis from the core, and do not assert that the weaker candidate is false.

## 3. Exact residual core and proved consequences

The source definition below is the literal new core. It retains all three K-continuity assumptions and the original mean-scalar floor. It does not hide the removed fields behind another whole-record hypothesis.

```lean
def HamiltonReactionCore3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (c rate : ℝ),
      Continuous parameter ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
      0 < rate ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
          -rate * (gt t).tracelessRicciNormSqAt x) ∧
      Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) ∧
      Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
      Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2) ∧
      (let C := compactFiniteExtendedChartCover (n := 3) (M := M)
       ∀ t : ℝ, ∃ s ∈ 𝓝 t,
         ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
           (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
           (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
             ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z))
```

The proved consequences are the reaction-record existence theorem, `finiteEnergyFlowExistence3_of_hamiltonReactionCore3`, `hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3`, and `universalHamiltonConvergence_of_universalHamiltonReactionCore`. `UniversalHamiltonReactionCoreStatement` universally quantifies the core with the same independent universes u and v and compatible Borel structures. The last theorem installs the canonical Borel structure when passing to the measurable-free Hamilton endpoint. All remain conditional implications.

## 4. Numbered next-reduction plan

These are proposed tasks, not accepted jobs. Their statement probes establish well-typed targets, not proofs. Freeze an independently accepted commit containing this module before dispatch. The proof head recorded in section 5 is the concrete current candidate base; do not infer that it has been merged. Each task owns only its proposed new module and report. Existing sources, frozen definitions, root imports, audit wiring, missions and ledgers remain forbidden.

### 1. Local integrable domination

Module: `Poincare/Global/HamiltonChartDensityLocalDomination.lean`.
Namespace: `Poincare.HamiltonChartDensityLocalDomination`.
Imports: `Poincare.Global.HamiltonReactionCoreReduction`.

Objective: prove the first displayed target proposition below. Produce the neighborhood and a chartwise integrable envelope from the same all-real-time joint C³ metric entries and compact manifold. A plausible route is a uniform intrinsic trace bound on a compact time strip, then a density comparison against the already-integrable density at its central time. Prove the chart-transition and global uniformity steps; do not assume compactness of a coordinate piece.

Gate: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean`, empty forbidden-token scan, standard axiom closures of every declaration, scratch signature probe, `git diff --check`.

Exact stop: either the original local-bound quantifier order is proved without new analytic assumptions, or a blocked report displays the exact resisting uniform comparison type and its strongest compiled partial result. A per-point neighborhood or an assumed integrable bound does not close this task.

### 2. Compact metric-family invariant continuity

Module: `Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean`.
Namespace: `Poincare.HamiltonCompactFamilyInvariantContinuity`.
Imports: `Poincare.Global.ClosedMetricThirdJetTopology`, `Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity`, `Poincare.Global.HamiltonReactionCoreReduction`.

Objective: investigate and prove the second displayed target proposition. It explicitly adds joint continuity of every scalar third-jet profile for the supplied family, then asks for weak volume-measure and joint curvature continuity. This is a proposed sufficient regularity interface, not a theorem that `parameterContinuous` implies those jet hypotheses. The metric-family realization/regularity obligation would remain to be produced by the Hamilton existence campaign. Use local coordinate curvature identities and a finite spatial cover for the moving measure.

Gate: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean`, empty forbidden-token scan, standard axiom closures, scratch signature probe, `git diff --check`.

Exact stop: all three conclusions follow from exactly the displayed family hypothesis, or the report identifies an exact missing coordinate-to-intrinsic/measure-continuity implication. Continuity only along the time orbit, or assuming the three conclusions as new fields, does not close it. Any eventual replacement of the core's three fields by family jet continuity requires a separate reviewed change of the existence interface.

The following complete scratch program displays and probes both proposed Lean signatures as proposition definitions. Its namespace exists only in `/tmp`; the two propositions are not repository theorems.

```lean
import Poincare.Global.HamiltonReactionEndpoint
import Poincare.Global.HausdorffInverseChartGramContinuity
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare
namespace ReactionRecordNextTargets
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
-- Proposed target propositions only; no proof of these implications is asserted.
def localBoundTarget : Prop :=
  ∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M),
    (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z)

def compactFamilyContinuityTarget : Prop :=
  ∀ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (metric : K → ClosedSmoothRiemannianMetric 3 M),
      (∀ slot : MetricEntryThirdJetSlot 3 M,
        Continuous (fun p : K × ClosedSmoothModel 3 ↦
          metricEntryThirdJetProfile (metric p.1) slot p.2)) →
      Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) ∧
      Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
      Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
end ReactionRecordNextTargets
end Poincare
#print Poincare.ReactionRecordNextTargets.localBoundTarget
#print Poincare.ReactionRecordNextTargets.compactFamilyContinuityTarget
```

Actual command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/plan.lean`. Exit 0. Actual output:

```text
def Poincare.ReactionRecordNextTargets.localBoundTarget.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] →
                [CompactSpace M] → [ConnectedSpace M] → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] =>
  ∀ (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M),
    (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
      let C := Poincare.compactFiniteExtendedChartCover;
      ∀ (t : ℝ),
        ∃ s ∈ 𝓝 t,
          ∃ B,
            (∀ (i : Fin C.chartCount), Integrable (B i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
              ∀ (i : Fin C.chartCount),
                ∀ᵐ (z : ↑(C.coordinateDomain i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
                  ∀ τ ∈ s, ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z
def Poincare.ReactionRecordNextTargets.compactFamilyContinuityTarget.{u, v} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : MeasurableSpace M] →
        [BorelSpace M] →
          [inst_4 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
            [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] → [CompactSpace M] → [ConnectedSpace M] → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] =>
  ∀ (K : Type v) (topK : TopologicalSpace K),
    CompactSpace K →
      ∀ (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M),
        (∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
            Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) →
          (Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k)) ∧
            (Continuous fun p => (metric p.1).scalarAt p.2) ∧
              Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2
```

No positive-initial-mean replacement is ready for theorem dispatch. First resolve the missing derivative sign or the extra pointwise/normalization hypotheses of S9/S10. A task assuming monotonicity while claiming to derive it from positive initial mean would misstate the current boundary.

## 5. Verification and handoff

Proof head: `e1d4c39adcc488db8c8827e5e671c718637188dc`. Seven theorem commits, each after a direct module check, scratch signature/axiom check, empty forbidden-token scan and `git diff --check`:

```text
1d721ab5 Prove finite-atlas inverse-chart density integrability
7ba5e478 Derive chart density derivative measurability from joint metric regularity
8613ea9d Reduce chart-frame density data to joint regularity and local integrable bounds
92d1c6bf State residual Hamilton reaction core and reconstruct its reaction record
ca2c6746 Derive finite-energy flow existence from the reduced reaction core
69dc0c86 Derive the Hamilton endpoint from the residual reaction core
e1d4c39a Lift the residual reaction core reduction to universal Hamilton convergence
```

Every direct module command was `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionCoreReduction.lean`. The successful logs, in commit order, are `lemma1-03.log`, `lemma2-gate.log`, `lemma3-gate.log`, `core-gate.log`, `energy-gate.log`, `endpoint-gate.log`, and `universal-gate.log`. Each exited 0 with empty compiler output. The first three proof probes and the core probe are also preserved; the final probe reproduces every signature and footprint at the final proof head.

The scan command was `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonReactionCoreReduction.lean`: exit 1, no matches. `git diff --check`: exit 0, no output. No added declaration is excluded from the axiom gate: the final probe contains all seven theorems and both definitions, and every closure is exactly `[propext, Classical.choice, Quot.sound]`. No new structure with unchecked generated declarations is introduced.

The final proof diff is retained at `/tmp/reaction-record-decomposition-evidence/final.diff`; the commits preserve it durably. Failed compiler outputs, scratch sources, successful probes and source searches remain in the same evidence directory. Relevant outputs are embedded below so the report does not depend solely on temporary logs. The report itself is committed after the proof commits.


Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionCoreReduction.lean
```

Then reproduce the final scratch signature/axiom probe and compare the two-file diff against the recorded base. No root build or mission acceptance is claimed; those belong to the orchestrator's integration checkpoint. This worker does not merge or mark a mission/task accepted.

## Appendix A. Actual signature and axiom output

Every command in this appendix ran in the isolated worktree with `LEAN_NUM_THREADS=1`. Probe files are under `/tmp/reaction-record-decomposition-evidence`. For new declarations, probes concatenate the exact then-current module source with the shown `#check`, `#print` or `#print axioms` commands; they do not rely on a stale olean of the new module. The final probe covers every new declaration in one process.

### base-02

Probe directives:

```lean
import Poincare.Global.HamiltonReactionEndpoint
import Poincare.Global.HamiltonFiniteEnergyFlowInterface
import Poincare.Global.HausdorffInverseChartGramContinuity
#check Poincare.FiniteExtendedChartCover.hausdorffChartDensityEquality
#check Poincare.continuous_inverseChartPullbackVolumeDensity
#check MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
#check MeasureTheory.integrable_const_mul_iff
#check MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
#check MeasureTheory.Measure.map_apply
#check MeasureTheory.withDensity_apply
#check Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
#check Poincare.MetricEntriesJointContDiffAt.of_le
#print Poincare.HamiltonFiniteEnergyFlowExistence3
#print Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.mk

#check measurable_of_tendsto_metrizable
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check HasDerivAt.tendsto_slope_zero_right
#check tendsto_nhdsWithin_iff
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/base-02.lean`. Exit 0. Actual output:

```text
Poincare.FiniteExtendedChartCover.hausdorffChartDensityEquality.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  Poincare.HausdorffChartDensityEquality g (C.coordinateDomain i) (C.inverseChart i) (C.manifoldPiece i)
    (C.inverseChartDensity g i)
Poincare.continuous_inverseChartPullbackVolumeDensity.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (x₀ : M) : Continuous fun z => Poincare.inverseChartPullbackVolumeDensity g x₀ z
MeasureTheory.lintegral_ofReal_ne_top_iff_integrable.{u_1} {α : Type u_1} {m : MeasurableSpace α}
  {μ : MeasureTheory.Measure α} {f : α → ℝ} (hfm : MeasureTheory.AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
  ∫⁻ (a : α), ENNReal.ofReal (f a) ∂μ ≠ ⊤ ↔ MeasureTheory.Integrable f μ
MeasureTheory.integrable_const_mul_iff.{u_1, u_8} {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
  {𝕜 : Type u_8} [NormedRing 𝕜] {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
  MeasureTheory.Integrable (fun x => c * f x) μ ↔ MeasureTheory.Integrable f μ
MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure.{u_1} {G : Type u_1} [TopologicalSpace G] [AddGroup G]
  [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ' μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
  [μ'.IsAddHaarMeasure] : 0 < μ'.addHaarScalarFactor μ
MeasureTheory.Measure.map_apply.{u_1, u_2} {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α} {f : α → β} (hf : Measurable f) {s : Set β}
  (hs : MeasurableSet s) : (MeasureTheory.Measure.map f μ) s = μ (f ⁻¹' s)
MeasureTheory.withDensity_apply.{u_1} {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}
  (f : α → ENNReal) {s : Set α} (hs : MeasurableSet s) : (μ.withDensity f) s = ∫⁻ (a : α) in s, f a ∂μ
Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hJoint : Poincare.MetricEntriesJointContDiffAt gt t₀ x 1) : Poincare.TimeDifferentiableAt gt t₀ x
Poincare.MetricEntriesJointContDiffAt.of_le.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} {k l : WithTop ℕ∞}
  (h : Poincare.MetricEntriesJointContDiffAt gt t₀ x l) (hkl : k ≤ l) : Poincare.MetricEntriesJointContDiffAt gt t₀ x k
def Poincare.HamiltonFiniteEnergyFlowExistence3.{u, v} : (M : Type u) →
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
  ∃ gt K topK,
    ∃ (_ : CompactSpace K),
      ∃ metric parameter c,
        (∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
          MeasureTheory.IntegrableOn (Poincare.normalizedFlowTracelessRicciEnergyTrack gt) (Set.Ici 0)
              MeasureTheory.volume ∧
            (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) ∧
              (Continuous fun k => Poincare.closedMetricMeanTracelessEnergyPair (metric k)) ∧
                0 < c ∧ ∀ (t : ↑(Set.Ici 0)), c ≤ Poincare.meanScalar (gt ↑t)
constructor Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.mk.{u, v} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [inst_1 : T2Space M] →
      [inst_2 : SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [inst_4 : BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                [inst_7 : CompactSpace M] →
                  [inst_8 : ConnectedSpace M] →
                    [inst_9 : SimplyConnectedSpace M] →
                      (K : Type v) →
                        (topologicalSpaceK : TopologicalSpace K) →
                          CompactSpace K →
                            (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                              (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                                (parameter : ↑(Set.Ici 0) → K) →
                                  Continuous parameter →
                                    (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) →
                                      (meanScalarFloor : ℝ) →
                                        0 < meanScalarFloor →
                                          (∀ (t : ↑(Set.Ici 0)), meanScalarFloor ≤ Poincare.meanScalar (gt ↑t)) →
                                            (∀ t ∈ Set.Ici 0,
                                                ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) →
                                              Poincare.CompactFiniteAtlasChartFrameDensityData gt →
                                                (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
                                                  (reactionDecayRate : ℝ) →
                                                    0 < reactionDecayRate →
                                                      (∀ t ∈ Set.Ici 0,
                                                          ∀ (x : M),
                                                            Poincare.normalizedTracelessRicciEvolutionReactionAt (gt t)
                                                                x ≤
                                                              -reactionDecayRate * (gt t).tracelessRicciNormSqAt x) →
                                                        (Continuous fun k =>
                                                            Poincare.closedMetricFiniteVolumeMeasure (metric k)) →
                                                          (Continuous fun p => (metric p.1).scalarAt p.2) →
                                                            (Continuous fun p =>
                                                                (metric p.1).tracelessRicciNormSqAt p.2) →
                                                              Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3
                                                                M
measurable_of_tendsto_metrizable.{u_1, u_2} {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [TopologicalSpace β]
  [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {f : ℕ → α → β} {g : α → β}
  (hf : ∀ (i : ℕ), Measurable (f i)) (lim : Filter.Tendsto f Filter.atTop (nhds g)) : Measurable g
tendsto_one_div_add_atTop_nhds_zero_nat.{u_4} {𝕜 : Type u_4} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜]
  [ContinuousSMul ℚ≥0 𝕜] : Filter.Tendsto (fun n => 1 / (↑n + 1)) Filter.atTop (nhds 0)
HasDerivAt.tendsto_slope_zero_right.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} [Preorder 𝕜] (h : HasDerivAt f f' x) :
  Filter.Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds f')
tendsto_nhdsWithin_iff.{u_1, u_2} {α : Type u_1} {β : Type u_2} [TopologicalSpace α] {a : α} {l : Filter β} {s : Set α}
  {f : β → α} : Filter.Tendsto f l (nhdsWithin a s) ↔ Filter.Tendsto f l (nhds a) ∧ ∀ᶠ (n : β) in l, f n ∈ s
```

### support

Probe directives:

```lean
import Poincare.Global.HamiltonReactionEndpoint
import Poincare.Global.HamiltonFiniteEnergyFlowInterface
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
#check Poincare.exists_finiteExtendedChartCover
#check Poincare.FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula
#check Poincare.volumeMeasure_isFiniteMeasure
#check Poincare.continuous_inverseChartPullbackVolumeDensity
#check Poincare.FiniteExtendedChartCover.hasDerivAt_inverseChartDensity
#check Poincare.FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
#check Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
#check Poincare.MetricEntriesJointContDiffAt.of_le
#check Poincare.continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
#check Poincare.normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
#check Poincare.meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
#check Poincare.finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3
#check Poincare.hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3
#check Poincare.universalHamiltonConvergence_of_universalFiniteEnergyFlowExistence
#check Poincare.metricEntryThirdJetProfile
#check Poincare.MetricEntryThirdJetSlot
#check Poincare.normalizedMeanScalarEnergyNumerator
#print Poincare.FiniteExtendedChartFrameDensityDominationAt.mk
#print Poincare.GlobalFiniteExtendedChartFrameDensityData.mk
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/support.lean`. Exit 0. Actual output:

```text
Poincare.exists_finiteExtendedChartCover.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] :
  Nonempty Poincare.FiniteExtendedChartCover
Poincare.FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (C : Poincare.FiniteExtendedChartCover)
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  C.RestrictedInverseChartPullbackHausdorffAreaFormula g i
Poincare.volumeMeasure_isFiniteMeasure.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M) :
  MeasureTheory.IsFiniteMeasure (Poincare.volumeMeasure g)
Poincare.continuous_inverseChartPullbackVolumeDensity.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (x₀ : M) : Continuous fun z => Poincare.inverseChartPullbackVolumeDensity g x₀ z
Poincare.FiniteExtendedChartCover.hasDerivAt_inverseChartDensity.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
  (i : Fin C.chartCount) (z : ↑(C.coordinateDomain i))
  (hgt : Poincare.TimeDifferentiableAt gt t₀ (C.inverseChart i z)) :
  HasDerivAt (fun t => C.inverseChartDensity (gt t) i z)
    (1 / 2 * C.inverseChartDensity (gt t₀) i z *
      Poincare.traceMetricVariationAt (gt t₀) (Poincare.timeDerivAt gt t₀) (C.inverseChart i z))
    t₀
Poincare.FiniteExtendedChartFrameMeasureData.ofDensityIntegrable.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (s : Set ℝ)
  (hDensity :
    ∀ t ∈ s,
      ∀ (i : Fin C.chartCount),
        MeasureTheory.Integrable (C.inverseChartDensity (gt t) i)
          (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) :
  Poincare.FiniteExtendedChartFrameMeasureData C gt s
Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hJoint : Poincare.MetricEntriesJointContDiffAt gt t₀ x 1) : Poincare.TimeDifferentiableAt gt t₀ x
Poincare.MetricEntriesJointContDiffAt.of_le.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} {k l : WithTop ℕ∞}
  (h : Poincare.MetricEntriesJointContDiffAt gt t₀ x l) (hkl : k ≤ l) : Poincare.MetricEntriesJointContDiffAt gt t₀ x k
Poincare.continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {K : Type v} [TopologicalSpace K] [Nonempty M] (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hMeasure : Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k))
  (hScalar : Continuous fun p => (metric p.1).scalarAt p.2)
  (hTracelessRicci : Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2) :
  Continuous fun k => Poincare.closedMetricMeanTracelessEnergyPair (metric k)
Poincare.normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1]
  (hFlow : ∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hVolumeVariation :
    ∀ t ∈ Set.Ici 0,
      HasDerivAt (fun s => Poincare.totalVolume (gt s))
        (Poincare.totalVolumeFirstVariation (gt t) (Poincare.timeDerivAt gt t)) t)
  (hMeasurable :
    MeasureTheory.AEStronglyMeasurable (Poincare.normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Set.Ici 0)))
  (hJointMetricEntries : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) {rate : ℝ}
  (hrate : 0 < rate)
  (hReaction :
    ∀ t ∈ Set.Ici 0,
      ∀ (x : M),
        Poincare.normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x) :
  MeasureTheory.IntegrableOn (Poincare.normalizedFlowTracelessRicciEnergyTrack gt) (Set.Ici 0) MeasureTheory.volume
Poincare.meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [Nonempty M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hFlow : ∀ (t : ↑(Set.Ici 0)) (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt (↑t) x)
  (hDifferentiateMovingTotalScalar :
    ∀ (t : ↑(Set.Ici 0)),
      HasDerivAt (fun s => Poincare.totalScalar (gt s)) (Poincare.normalizedMeanScalarEnergyNumerator (gt ↑t)) ↑t)
  (hDifferentiateMovingVolume :
    ∀ (t : ↑(Set.Ici 0)),
      HasDerivAt (fun s => Poincare.totalVolume (gt s))
        (Poincare.totalVolumeFirstVariation (gt ↑t) (Poincare.timeDerivAt gt ↑t)) ↑t)
  (hEnergyDomination :
    ∀ (t : ↑(Set.Ici 0)),
      Poincare.normalizedFlowScalarVarianceTrack gt ↑t ≤ 6 * Poincare.normalizedFlowTracelessRicciEnergyTrack gt ↑t)
  (t : ↑(Set.Ici 0)) : 0 ≤ deriv (fun s => Poincare.meanScalar (gt s)) ↑t
Poincare.finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (r : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M) :
  Poincare.HamiltonFiniteEnergyFlowExistence3 M
Poincare.hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (h : Poincare.HamiltonFiniteEnergyFlowExistence3 M) :
  Poincare.HamiltonConvergencePinchedLimit3 M
Poincare.universalHamiltonConvergence_of_universalFiniteEnergyFlowExistence.{u, v}
  (h : Poincare.UniversalHamiltonFiniteEnergyFlowExistenceStatement) : Poincare.UniversalHamiltonConvergenceStatement
Poincare.metricEntryThirdJetProfile.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) : Poincare.MetricEntryThirdJetProfileTarget n M
Poincare.MetricEntryThirdJetSlot.{u} (n : ℕ) (M : Type u) : Type u
Poincare.normalizedMeanScalarEnergyNumerator.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M) : ℝ
constructor Poincare.FiniteExtendedChartFrameDensityDominationAt.mk.{u} : {n : ℕ} →
  {M : Type u} →
    [inst : TopologicalSpace M] →
      [inst_1 : T2Space M] →
        [inst_2 : SecondCountableTopology M] →
          [inst_3 : CompactSpace M] →
            [inst_4 : ConnectedSpace M] →
              [inst_5 : MeasurableSpace M] →
                [inst_6 : BorelSpace M] →
                  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel n) M] →
                    [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] →
                      {C : Poincare.FiniteExtendedChartCover} →
                        {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} →
                          {s : Set ℝ} →
                            {t₀ : ℝ} →
                              s ∈ nhds t₀ →
                                (∀ (i : Fin C.chartCount),
                                    MeasureTheory.AEStronglyMeasurable
                                      (Poincare.finiteExtendedChartFrameDensityDerivative C gt t₀ i)
                                      (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) →
                                  (dominatingFunction : (i : Fin C.chartCount) → ↑(C.coordinateDomain i) → ℝ) →
                                    (∀ (i : Fin C.chartCount),
                                        MeasureTheory.Integrable (dominatingFunction i)
                                          (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) →
                                      (∀ (i : Fin C.chartCount),
                                          ∀ᵐ (z :
                                            ↑(C.coordinateDomain
                                                i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
                                            ∀ t ∈ s,
                                              ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt t i z‖ ≤
                                                dominatingFunction i z) →
                                        (∀ (i : Fin C.chartCount) (z : ↑(C.coordinateDomain i)),
                                            ∀ t ∈ s, Poincare.TimeDifferentiableAt gt t (C.inverseChart i z)) →
                                          Poincare.FiniteExtendedChartFrameDensityDominationAt C gt s t₀
constructor Poincare.GlobalFiniteExtendedChartFrameDensityData.mk.{u} : {n : ℕ} →
  {M : Type u} →
    [inst : TopologicalSpace M] →
      [inst_1 : T2Space M] →
        [inst_2 : SecondCountableTopology M] →
          [inst_3 : CompactSpace M] →
            [inst_4 : ConnectedSpace M] →
              [inst_5 : MeasurableSpace M] →
                [inst_6 : BorelSpace M] →
                  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel n) M] →
                    [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] →
                      {C : Poincare.FiniteExtendedChartCover} →
                        {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} →
                          (timeSet : ℝ → Set ℝ) →
                            (∀ (t : ℝ), Poincare.FiniteExtendedChartFrameMeasureData C gt (timeSet t)) →
                              ((t : ℝ) → Poincare.FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t) →
                                Poincare.GlobalFiniteExtendedChartFrameDensityData C gt
```

### extra-support

Probe directives:

```lean
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity
#check Poincare.exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
#check Poincare.continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/extra-support.lean`. Exit 0. Actual output:

```text
Poincare.exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t0 C : ℝ}
  [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1]
  (hScalarContinuous : Continuous ↿fun tau x => (gt (t0 + tau)).scalarAt x)
  (hScalarEvolution :
    ∀ tau ∈ Set.Ici 0, ∀ (x : M), Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
  (hScalarTwo :
    ∀ tau ∈ Set.Ici 0,
      ∀ (x : M),
        ContMDiffAt (Poincare.closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2
          (fun y => (gt (t0 + tau)).scalarAt y) x)
  (normalizationPrimitive : ℝ → ℝ) (hPrimitiveContinuous : Continuous normalizationPrimitive)
  (hPrimitiveDerivative :
    ∀ tau ∈ Set.Ici 0, HasDerivAt normalizationPrimitive (2 / 3 * Poincare.meanScalar (gt (t0 + tau))) tau)
  (hPrimitiveUpper : ∀ tau ∈ Set.Ici 0, normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
  (hInitialPos : ∀ (x : M), 0 < (gt t0).scalarAt x) :
  ∃ rhoFloor, 0 < rhoFloor ∧ ∀ tau ∈ Set.Ici 0, ∀ (x : M), rhoFloor ≤ (gt (t0 + tau)).scalarAt x
Poincare.continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hJoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) :
  (Continuous ↿fun t x => (gt t).scalarAt x) ∧ Continuous ↿fun t x => (gt t).tracelessRicciNormSqAt x
```

### final-probe

Probe directives appended to the exact final module source:

```lean
#print Poincare.HamiltonReactionCore3
#check Poincare.HamiltonReactionCoreReduction.inverseChartDensity_integrable
#print axioms Poincare.HamiltonReactionCoreReduction.inverseChartDensity_integrable
#check Poincare.HamiltonReactionCoreReduction.densityDerivative_measurable
#print axioms Poincare.HamiltonReactionCoreReduction.densityDerivative_measurable
#check Poincare.HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
#print axioms Poincare.HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
#check Poincare.HamiltonReactionCore3
#print axioms Poincare.HamiltonReactionCore3
#check Poincare.reactionDecayAnalyticData3_of_hamiltonReactionCore3
#print axioms Poincare.reactionDecayAnalyticData3_of_hamiltonReactionCore3
#check Poincare.finiteEnergyFlowExistence3_of_hamiltonReactionCore3
#print axioms Poincare.finiteEnergyFlowExistence3_of_hamiltonReactionCore3
#check Poincare.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3
#print axioms Poincare.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3
#check Poincare.UniversalHamiltonReactionCoreStatement
#print axioms Poincare.UniversalHamiltonReactionCoreStatement
#check Poincare.universalHamiltonConvergence_of_universalHamiltonReactionCore
#print axioms Poincare.universalHamiltonConvergence_of_universalHamiltonReactionCore
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/final-probe.lean`. Exit 0. Actual output:

```text
def Poincare.HamiltonReactionCore3.{u, v} : (M : Type u) →
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
      ∃ gt metric parameter c rate,
        Continuous parameter ∧
          (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) ∧
            0 < c ∧
              (∀ (t : ↑(Ici 0)), c ≤ Poincare.meanScalar (gt ↑t)) ∧
                (∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
                  (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) ∧
                    0 < rate ∧
                      (∀ t ∈ Ici 0,
                          ∀ (x : M),
                            Poincare.normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
                              -rate * (gt t).tracelessRicciNormSqAt x) ∧
                        (Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k)) ∧
                          (Continuous fun p => (metric p.1).scalarAt p.2) ∧
                            (Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2) ∧
                              let C := Poincare.compactFiniteExtendedChartCover;
                              ∀ (t : ℝ),
                                ∃ s ∈ 𝓝 t,
                                  ∃ B,
                                    (∀ (i : Fin C.chartCount),
                                        Integrable (B i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
                                      ∀ (i : Fin C.chartCount),
                                        ∀ᵐ (z :
                                          ↑(C.coordinateDomain
                                              i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
                                          ∀ τ ∈ s,
                                            ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z
Poincare.HamiltonReactionCoreReduction.inverseChartDensity_integrable.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  [CompactSpace M] [ConnectedSpace M] (C : Poincare.FiniteExtendedChartCover)
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  Integrable (C.inverseChartDensity g i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))
'Poincare.HamiltonReactionCoreReduction.inverseChartDensity_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HamiltonReactionCoreReduction.densityDerivative_measurable.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  [CompactSpace M] [ConnectedSpace M] (C : Poincare.FiniteExtendedChartCover)
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (hJoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) (t : ℝ) (i : Fin C.chartCount) :
  Measurable (Poincare.finiteExtendedChartFrameDensityDerivative C gt t i)
'Poincare.HamiltonReactionCoreReduction.densityDerivative_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) ∞ M]
  [CompactSpace M] [ConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (hJoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3)
  (hBound :
    have C := Poincare.compactFiniteExtendedChartCover;
    ∀ (t : ℝ),
      ∃ s ∈ 𝓝 t,
        ∃ B,
          (∀ (i : Fin C.chartCount), Integrable (B i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
            ∀ (i : Fin C.chartCount),
              ∀ᵐ (z : ↑(C.coordinateDomain i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
                ∀ τ ∈ s, ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z) :
  Nonempty (Poincare.CompactFiniteAtlasChartFrameDensityData gt)
'Poincare.HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HamiltonReactionCore3.{u, v} (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] : Prop
'Poincare.HamiltonReactionCore3' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.reactionDecayAnalyticData3_of_hamiltonReactionCore3.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (h : Poincare.HamiltonReactionCore3 M) :
  Nonempty (Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M)
'Poincare.reactionDecayAnalyticData3_of_hamiltonReactionCore3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.finiteEnergyFlowExistence3_of_hamiltonReactionCore3.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (h : Poincare.HamiltonReactionCore3 M) : Poincare.HamiltonFiniteEnergyFlowExistence3 M
'Poincare.finiteEnergyFlowExistence3_of_hamiltonReactionCore3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (h : Poincare.HamiltonReactionCore3 M) : Poincare.HamiltonConvergencePinchedLimit3 M
'Poincare.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.UniversalHamiltonReactionCoreStatement.{u, v} : Prop
'Poincare.UniversalHamiltonReactionCoreStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.universalHamiltonConvergence_of_universalHamiltonReactionCore.{u, v}
  (h : Poincare.UniversalHamiltonReactionCoreStatement) : Poincare.UniversalHamiltonConvergenceStatement
'Poincare.universalHamiltonConvergence_of_universalHamiltonReactionCore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```


## Appendix B. Compiler failures retained as evidence

These are the failed attempts before the successful checks above. No failed source is part of the new module. The diagnostics are reproduced verbatim; the logs and scratch sources remain under the evidence directory.

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/base.lean`. Exit 1. Log `base.log`. The with-density lemma is in `MeasureTheory`, not `MeasureTheory.Measure`. The corrected base-02 probe passes.

```text
Poincare.FiniteExtendedChartCover.hausdorffChartDensityEquality.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  Poincare.HausdorffChartDensityEquality g (C.coordinateDomain i) (C.inverseChart i) (C.manifoldPiece i)
    (C.inverseChartDensity g i)
Poincare.continuous_inverseChartPullbackVolumeDensity.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (x₀ : M) : Continuous fun z => Poincare.inverseChartPullbackVolumeDensity g x₀ z
MeasureTheory.lintegral_ofReal_ne_top_iff_integrable.{u_1} {α : Type u_1} {m : MeasurableSpace α}
  {μ : MeasureTheory.Measure α} {f : α → ℝ} (hfm : MeasureTheory.AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
  ∫⁻ (a : α), ENNReal.ofReal (f a) ∂μ ≠ ⊤ ↔ MeasureTheory.Integrable f μ
MeasureTheory.integrable_const_mul_iff.{u_1, u_8} {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
  {𝕜 : Type u_8} [NormedRing 𝕜] {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
  MeasureTheory.Integrable (fun x => c * f x) μ ↔ MeasureTheory.Integrable f μ
MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure.{u_1} {G : Type u_1} [TopologicalSpace G] [AddGroup G]
  [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ' μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
  [μ'.IsAddHaarMeasure] : 0 < μ'.addHaarScalarFactor μ
MeasureTheory.Measure.map_apply.{u_1, u_2} {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α} {f : α → β} (hf : Measurable f) {s : Set β}
  (hs : MeasurableSet s) : (MeasureTheory.Measure.map f μ) s = μ (f ⁻¹' s)
/tmp/reaction-record-decomposition-evidence/base.lean:10:7: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.withDensity_apply`
Poincare.timeDifferentiableAt_of_metricEntriesJointContDiffAt_one.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hJoint : Poincare.MetricEntriesJointContDiffAt gt t₀ x 1) : Poincare.TimeDifferentiableAt gt t₀ x
Poincare.MetricEntriesJointContDiffAt.of_le.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} {k l : WithTop ℕ∞}
  (h : Poincare.MetricEntriesJointContDiffAt gt t₀ x l) (hkl : k ≤ l) : Poincare.MetricEntriesJointContDiffAt gt t₀ x k
def Poincare.HamiltonFiniteEnergyFlowExistence3.{u, v} : (M : Type u) →
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
  ∃ gt K topK,
    ∃ (_ : CompactSpace K),
      ∃ metric parameter c,
        (∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
          MeasureTheory.IntegrableOn (Poincare.normalizedFlowTracelessRicciEnergyTrack gt) (Set.Ici 0)
              MeasureTheory.volume ∧
            (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) ∧
              (Continuous fun k => Poincare.closedMetricMeanTracelessEnergyPair (metric k)) ∧
                0 < c ∧ ∀ (t : ↑(Set.Ici 0)), c ≤ Poincare.meanScalar (gt ↑t)
constructor Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.mk.{u, v} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [inst_1 : T2Space M] →
      [inst_2 : SecondCountableTopology M] →
        [inst_3 : MeasurableSpace M] →
          [inst_4 : BorelSpace M] →
            [inst_5 : ChartedSpace (Poincare.ClosedSmoothModel 3) M] →
              [inst_6 : IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] →
                [inst_7 : CompactSpace M] →
                  [inst_8 : ConnectedSpace M] →
                    [inst_9 : SimplyConnectedSpace M] →
                      (K : Type v) →
                        (topologicalSpaceK : TopologicalSpace K) →
                          CompactSpace K →
                            (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                              (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) →
                                (parameter : ↑(Set.Ici 0) → K) →
                                  Continuous parameter →
                                    (∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t) →
                                      (meanScalarFloor : ℝ) →
                                        0 < meanScalarFloor →
                                          (∀ (t : ↑(Set.Ici 0)), meanScalarFloor ≤ Poincare.meanScalar (gt ↑t)) →
                                            (∀ t ∈ Set.Ici 0,
                                                ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x) →
                                              Poincare.CompactFiniteAtlasChartFrameDensityData gt →
                                                (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
                                                  (reactionDecayRate : ℝ) →
                                                    0 < reactionDecayRate →
                                                      (∀ t ∈ Set.Ici 0,
                                                          ∀ (x : M),
                                                            Poincare.normalizedTracelessRicciEvolutionReactionAt (gt t)
                                                                x ≤
                                                              -reactionDecayRate * (gt t).tracelessRicciNormSqAt x) →
                                                        (Continuous fun k =>
                                                            Poincare.closedMetricFiniteVolumeMeasure (metric k)) →
                                                          (Continuous fun p => (metric p.1).scalarAt p.2) →
                                                            (Continuous fun p =>
                                                                (metric p.1).tracelessRicciNormSqAt p.2) →
                                                              Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3
                                                                M
```

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionCoreReduction.lean`. Exit 1. Log `lemma1-01.log`. Reduced the application of the measure-evaluation lambda before rewriting.

```text
Poincare/Global/HamiltonReactionCoreReduction.lean:46:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (Measure.map (C.inverseChart i) ?m.166) univ
in the target expression
  (fun μ => μ univ)
      (Measure.map (C.inverseChart i)
        (rawHausdorffCoordinateDensityMeasure (C.coordinateDomain i) (C.inverseChartDensity g i))) =
    (fun μ => μ univ) ((volumeMeasure g).restrict (C.manifoldPiece i))

n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : SecondCountableTopology M
inst✝⁵ : MeasurableSpace M
inst✝⁴ : BorelSpace M
inst✝³ : ChartedSpace (ClosedSmoothModel n) M
inst✝² : IsManifold (closedSmoothModelWithCorners n) ∞ M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
C : FiniteExtendedChartCover
g : ClosedSmoothRiemannianMetric n M
i : Fin C.chartCount
hcont : Continuous (C.inverseChartDensity g i)
hscale : 0 < ↑(rawHausdorffLebesgueScale n)
hmass :
  (fun μ => μ univ)
      (Measure.map (C.inverseChart i)
        (rawHausdorffCoordinateDensityMeasure (C.coordinateDomain i) (C.inverseChartDensity g i))) =
    (fun μ => μ univ) ((volumeMeasure g).restrict (C.manifoldPiece i))
⊢ Integrable (C.inverseChartDensity g i) (coordinateLebesgueMeasure (C.coordinateDomain i))
```

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionCoreReduction.lean`. Exit 1. Log `lemma1-02.log`. Typed the ENNReal top explicitly and installed the existing finite-volume theorem as a local instance.

```text
Poincare/Global/HamiltonReactionCoreReduction.lean:52:62: error: Ambiguous term
  ∞
Possible interpretations:
  ∞ : ℝ≥0∞

  ∞ : ℕ∞ω
Poincare/Global/HamiltonReactionCoreReduction.lean:56:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsFiniteMeasure (volumeMeasure g)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/reaction-record-decomposition-evidence/lemma2.lean`. Exit 1. Log `lemma2-01.log`. Changed the neighborhood membership goal to the explicit positive real inequality before invoking positivity.

```text
/tmp/reaction-record-decomposition-evidence/lemma2.lean:78:52: error: not a positivity goal
```


## Appendix C. Source searches and negative findings

Source-backed declaration lookup commands and actual matches follow. Results are truncated to the first four matches for each name; the matching command's exit is recorded. Constructors were probed under their generated `.mk` names after locating the corresponding source structure, rather than treated as independently written producers. The two proposed plan-target names are deliberately scratch-only proposition definitions, not purported repository declarations.

```text
$ rg -n -F inverseChartDensity_integrable Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:31:theorem inverseChartDensity_integrable
Poincare/Global/HamiltonReactionCoreReduction.lean:114:      C gt (s t) (fun τ _ i ↦ inverseChartDensity_integrable C (gt τ) i)
exit=0; first four matches shown

$ rg -n -F densityDerivative_measurable Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:66:theorem densityDerivative_measurable
Poincare/Global/HamiltonReactionCoreReduction.lean:118:        (densityDerivative_measurable C gt hJoint t i).aestronglyMeasurable
exit=0; first four matches shown

$ rg -n -F chartFrameDensityData_of_joint_of_local_bound Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:93:theorem chartFrameDensityData_of_joint_of_local_bound
Poincare/Global/HamiltonReactionCoreReduction.lean:177:    HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound gt hjoint hbound
exit=0; first four matches shown

$ rg -n -F HamiltonReactionCore3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:132:def HamiltonReactionCore3 (M : Type u)
Poincare/Global/HamiltonReactionCoreReduction.lean:171:    (h : HamiltonReactionCore3.{u, v} M) :
Poincare/Global/HamiltonReactionCoreReduction.lean:202:    (h : HamiltonReactionCore3.{u, v} M) :
Poincare/Global/HamiltonReactionCoreReduction.lean:209:    (h : HamiltonReactionCore3.{u, v} M) :
exit=0; first four matches shown

$ rg -n -F reactionDecayAnalyticData3_of_hamiltonReactionCore3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:170:theorem reactionDecayAnalyticData3_of_hamiltonReactionCore3
Poincare/Global/HamiltonReactionCoreReduction.lean:204:  obtain ⟨r⟩ := reactionDecayAnalyticData3_of_hamiltonReactionCore3 h
exit=0; first four matches shown

$ rg -n -F finiteEnergyFlowExistence3_of_hamiltonReactionCore3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:201:theorem finiteEnergyFlowExistence3_of_hamiltonReactionCore3
Poincare/Global/HamiltonReactionCoreReduction.lean:212:    (finiteEnergyFlowExistence3_of_hamiltonReactionCore3 h)
exit=0; first four matches shown

$ rg -n -F hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:208:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3
Poincare/Global/HamiltonReactionCoreReduction.lean:232:  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3 (h N)
exit=0; first four matches shown

$ rg -n -F UniversalHamiltonReactionCoreStatement Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:216:def UniversalHamiltonReactionCoreStatement : Prop :=
Poincare/Global/HamiltonReactionCoreReduction.lean:227:    (h : UniversalHamiltonReactionCoreStatement.{u, v}) :
exit=0; first four matches shown

$ rg -n -F universalHamiltonConvergence_of_universalHamiltonReactionCore Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:226:theorem universalHamiltonConvergence_of_universalHamiltonReactionCore
exit=0; first four matches shown

$ rg -n -F exists_finiteExtendedChartCover Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:62:theorem exists_finiteExtendedChartCover :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:87:  Classical.choice exists_finiteExtendedChartCover
exit=0; first four matches shown

$ rg -n -F restrictedInverseChartPullbackHausdorffAreaFormula Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:38:theorem restrictedInverseChartPullbackHausdorffAreaFormula
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:120:    C.restrictedInverseChartPullbackHausdorffAreaFormula (gt t) i
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:132:    (C.restrictedInverseChartPullbackHausdorffAreaFormula g i)
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:138:    C.restrictedInverseChartPullbackHausdorffAreaFormula g i
exit=0; first four matches shown

$ rg -n -F volumeMeasure_isFiniteMeasure Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:69:      volumeMeasure_isFiniteMeasure (g i)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:140:    volumeMeasure_isFiniteMeasure g
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:196:    volumeMeasure_isFiniteMeasure g
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:231:    volumeMeasure_isFiniteMeasure g
exit=0; first four matches shown

$ rg -n -F continuous_inverseChartPullbackVolumeDensity Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffInverseChartGramContinuity.lean:124:theorem continuous_inverseChartPullbackVolumeDensity
Poincare/Global/HausdorffInverseChartGramContinuity.lean:184:    (continuous_inverseChartPullbackVolumeDensity g x₀).continuousAt
Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean:146:      continuous_inverseChartPullbackVolumeDensity gref x₀
Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean:149:      continuous_inverseChartPullbackVolumeDensity g x₀
exit=0; first four matches shown

$ rg -n -F hasDerivAt_inverseChartDensity Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:285:theorem hasDerivAt_inverseChartDensity
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:387:    C.hasDerivAt_inverseChartDensity i z (A.timeDifferentiable i z t ht)
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:414:    exact C.hasDerivAt_inverseChartDensity i z
Poincare/Global/HamiltonReactionCoreReduction.lean:89:    exact (C.hasDerivAt_inverseChartDensity i z htime).tendsto_slope_zero_right.comp hstep
exit=0; first four matches shown

$ rg -n -F ofDensityIntegrable Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:111:def FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:137:def GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:151:    FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:186:    fun t ↦ FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
exit=0; first four matches shown

$ rg -n -F timeDifferentiableAt_of_metricEntriesJointContDiffAt_one Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:169:    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:159:    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
Poincare/Global/MetricFlowJointRicciTensorEvolution.lean:57:    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
Poincare/Global/MetricFlowJointRegularity.lean:276:theorem timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
exit=0; first four matches shown

$ rg -n -F of_le Poincare .lake/packages/mathlib/Mathlib
Poincare/ProofProgress/CompletionBlockerLedger.lean:14405:theorem completion_frontier_topology_extinction_one_point_canonical_map_selection_forward_inverse_law_data_after_map_selection_data_statement_of_left_right_inverse_law_data_current_interface
Poincare/ProofProgress/CompletionBlockerLedger.lean:14416:  extinctionOnePointThreeSpaceCanonicalMapSelectionForwardInverseLawDataAfterMapSelectionDataStatement_of_leftRightInverseLawData
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:223:theorem contsAux_eq_contsAux_squashGCF_of_le {m : ℕ} :
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:305:            (contsAux_eq_contsAux_squashGCF_of_le <| le_refl <| n' + 1).symm,
exit=0; first four matches shown

$ rg -n -F continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:245:theorem continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureSelectedSmoothAtlasPoincare.lean:88:    continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
exit=0; first four matches shown

$ rg -n -F normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:605:    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare.lean:145:        normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:310:    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
exit=0; first four matches shown

$ rg -n -F meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:43:theorem meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:120:    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:319:    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
exit=0; first four matches shown

$ rg -n -F finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:205:  exact finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3 r
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:59:theorem finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3
exit=0; first four matches shown

$ rg -n -F hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:48:theorem hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:85:  exact hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3 (h N)
Poincare/Global/HamiltonReactionCoreReduction.lean:211:  hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3
exit=0; first four matches shown

$ rg -n -F universalHamiltonConvergence_of_universalFiniteEnergyFlowExistence Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:79:theorem universalHamiltonConvergence_of_universalFiniteEnergyFlowExistence
exit=0; first four matches shown

$ rg -n -F metricEntryThirdJetProfile Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:52:@[simp] theorem profileAnchorMetricValue_metricEntryThirdJetProfile
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:54:    profileAnchorMetricValue (metricEntryThirdJetProfile g) x i j =
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:56:  metricEntryThirdJetProfile_value_anchor g x i j
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:69:    (hEq : ∀ t, F (metricEntryThirdJetProfile (gt t)) =
exit=0; first four matches shown

$ rg -n -F MetricEntryThirdJetSlot Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:48:    (continuous_apply (MetricEntryThirdJetSlot.value x i j))
Poincare/Global/ClosedMetricThirdJetTopology.lean:38:inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
Poincare/Global/ClosedMetricThirdJetTopology.lean:47:  MetricEntryThirdJetSlot n M → C(ClosedSmoothModel n, ℝ)
Poincare/Global/ClosedMetricThirdJetTopology.lean:174:  ∀ slot : MetricEntryThirdJetSlot n M,
exit=0; first four matches shown

$ rg -n -F normalizedMeanScalarEnergyNumerator Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:51:        (normalizedMeanScalarEnergyNumerator (gt t)) t)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:165:        (normalizedMeanScalarEnergyNumerator (gt t)) t)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:205:    (normalizedMeanScalarEnergyNumerator (gt t)) t)
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradientSphere.lean:50:    (normalizedMeanScalarEnergyNumerator (gt t)) t)
exit=0; first four matches shown

$ rg -n -F exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:337:theorem exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:395:    exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
exit=0; first four matches shown

$ rg -n -F continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:41:theorem continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:174:    continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:216:    continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
exit=0; first four matches shown

$ rg -n -F hausdorffChartDensityEquality Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:124:theorem FiniteExtendedChartCover.hausdorffChartDensityEquality
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:131:  C.hausdorffChartDensityEquality_of_restrictedAreaFormula g i
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:270:theorem hausdorffChartDensityEquality_of_restrictedAreaFormula
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:278:  exact hausdorffChartDensityEquality_of_pullbackMetricFormula
exit=0; first four matches shown

$ rg -n -F lintegral_ofReal_ne_top_iff_integrable Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:58:  have hint := (lintegral_ofReal_ne_top_iff_integrable
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:932:lemma lintegral_ofReal_ne_top_iff_integrable {f : α → ℝ}
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/Basic.lean:124:  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
exit=0; first four matches shown

$ rg -n -F integrable_const_mul_iff Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:62:  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1054:theorem integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α → 𝕜) :
exit=0; first four matches shown

$ rg -n -F addHaarScalarFactor_pos_of_isAddHaarMeasure Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Disintegration.lean:94:      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map M.symm) (μS.prod μT)).ne'
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Disintegration.lean:102:      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μT.map L') ν).ne'
Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean:171:    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
Poincare/Global/HamiltonReactionCoreReduction.lean:40:    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
exit=0; first four matches shown

$ rg -n -F map_apply Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean:124:        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean:127:      rw [← hy, comm_comp_map_apply, ← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:164:  ext; rw [map_apply, Real.norm_eq_abs, abs_of_nonneg]; exact le_max_right _ _
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:258:  simp only [← map_apply g f, lintegral_eq_lintegral]
exit=0; first four matches shown

$ rg -n -F withDensity_apply Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffInverseChartMeasureTransport.lean:38:  rw [withDensity_apply _ (hs.preimage hf.measurable),
Poincare/Global/HausdorffInverseChartMeasureTransport.lean:39:    withDensity_apply _ hs]
Poincare/Global/ContinuousWithDensityOrder.lean:49:    rw [← withDensity_apply f hs, ← withDensity_apply g hs]
Poincare/Global/HausdorffCoordinateDensityVariation.lean:139:  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
exit=0; first four matches shown

$ rg -n -F HamiltonFiniteEnergyFlowExistence3 Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:24:def HamiltonFiniteEnergyFlowExistence3 (M : Type u)
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:49:    (h : HamiltonFiniteEnergyFlowExistence3.{u, v} M) :
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:61:    HamiltonFiniteEnergyFlowExistence3.{u, v} M := by
Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean:76:      HamiltonFiniteEnergyFlowExistence3.{u, v} N
exit=0; first four matches shown

$ rg -n -F measurable_of_tendsto_metrizable Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/LevyConvergence.lean:138:      refine measurable_of_tendsto_metrizable (f := fun n t ↦ charFun (μ n) t) (by fun_prop) ?_
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:398:  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDense.lean:259:  apply measurable_of_tendsto_metrizable (fun n ↦ (g n).measurable) (tendsto_pi_nhds.2 A)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:646:  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).aemeasurable) lim
exit=0; first four matches shown

$ rg -n -F tendsto_one_div_add_atTop_nhds_zero_nat Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:77:    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
.lake/packages/mathlib/Mathlib/MeasureTheory/Covering/LiminfLimsup.lean:210:      ⟨Tendsto.if' hr tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun i => ?_⟩
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:227:              (fun _ ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat F
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean:682:      (fun _ ↦ by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
exit=0; first four matches shown

$ rg -n -F tendsto_slope_zero_right Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HeatSemigroupBUCGeneratorCore.lean:152:    hP0.tendsto_slope_zero_right
Poincare/Global/HamiltonReactionCoreReduction.lean:89:    exact (C.hasDerivAt_inverseChartDensity i z htime).tendsto_slope_zero_right.comp hstep
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:125:    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:167:    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds
exit=0; first four matches shown

$ rg -n -F tendsto_nhdsWithin_iff Poincare .lake/packages/mathlib/Mathlib
Poincare/CurvatureConditions.lean:607:    rw [tendsto_nhdsWithin_iff]
Poincare/Global/HeatKernelIntegral.lean:147:    exact tendsto_nhdsWithin_iff.mpr ⟨hmul_nhds, hmul_pos⟩
Poincare/Global/HamiltonReactionCoreReduction.lean:77:    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
.lake/packages/mathlib/Mathlib/Probability/Process/Stopping.lean:297:    simp_rw [tendsto_nhdsWithin_iff] at this
exit=0; first four matches shown

$ rg -n -F FiniteExtendedChartFrameDensityDominationAt Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:146:      FiniteExtendedChartFrameDensityDominationAt
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:169:    FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:347:structure FiniteExtendedChartFrameDensityDominationAt
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:372:def FiniteExtendedChartFrameDensityDominationAt.toDominatedDifferentiation
exit=0; first four matches shown

$ rg -n -F GlobalFiniteExtendedChartFrameDensityData Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:137:def GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:148:    GlobalFiniteExtendedChartFrameDensityData C gt where
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:206:  (GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:391:structure GlobalFiniteExtendedChartFrameDensityData
exit=0; first four matches shown

$ rg -n -F compactFiniteExtendedChartCover Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:85:noncomputable def compactFiniteExtendedChartCover :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:425:    (compactFiniteExtendedChartCover (n := n) (M := M)) gt
Poincare/Global/HamiltonReactionCoreReduction.lean:96:    (hBound : let C := compactFiniteExtendedChartCover (n := n) (M := M)
Poincare/Global/HamiltonReactionCoreReduction.lean:104:  let C := compactFiniteExtendedChartCover (n := n) (M := M)
exit=0; first four matches shown

$ rg -n -F parameterContinuous Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein.lean:50:  parameterContinuous :
Poincare/Global/NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein.lean:147:        data.gt data.metric data.parameter data.parameterContinuous
Poincare/Global/NormalizedFlowCompactFixedTargetCoerciveGapPositiveEinstein.lean:50:  parameterContinuous :
Poincare/Global/NormalizedFlowCompactFixedTargetCoerciveGapPositiveEinstein.lean:133:      data.gt data.metric data.parameter data.parameterContinuous
exit=0; first four matches shown

$ rg -n -F continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:206:theorem continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:461:    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
Poincare/Global/NormalizedFlowCompactFiniteDissipationBoundedVariation.lean:304:    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare.lean:124:    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
exit=0; first four matches shown

$ rg -n -F totalVolumeFirstVariation Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:132:        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:243:        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyMaximumDifferentialDecay.lean:79:        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:385:        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
exit=0; first four matches shown

$ rg -n -F hasDerivAt_totalVolume_of_normalizedFlowAt Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:121:theorem GlobalFiniteHausdorffChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:329:    exact hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:369:    exact hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:568:        (hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
exit=0; first four matches shown
```

Negative domain search:

```sh
rg -n 'RicciFlow|ricciFlow|meanScalar|MetricEntriesJointContDiffAt|inverseChartDensity' .lake/packages/mathlib/Mathlib
```

Exit 1; no output. This is a name-level negative result on the pinned tree, not a proof that no differently formulated mathematical theorem could help.

The mean/monotonicity search was:

```sh
rg -n -i 'meanScalar.*monoton|monoton.*meanScalar|meanScalar.*[[:space:]]0[[:space:]]*[<≤]|meanScalar.*deriv_nonneg|meanScalar.*initial' Poincare/Global .lake/packages/mathlib/Mathlib
```

Exit 0. It returned 38 lines of consumers, assumed floors/monotonicity, and S9, preserved in `mean-search.log`. The wider scalar-bound search found S10 and was followed by the exact extra-support probe. In particular, the negative finding is **not** that all scalar maximum principles are absent. It is that no producer from positive initial mean alone was found.

```sh
rg -n '(theorem|def).*(scalar|Scalar).*(lower|Lower|pos|Pos|monoton|Monoton)|(theorem|def).*(lower|Lower|pos|Pos|monoton|Monoton).*(scalar|Scalar)' Poincare/Global/NormalizedFlow*.lean Poincare/Global/*Maximum*.lean
```

Exit 0; actual full output retained in `scalar-bound-search.log`. S9 and S10's actual dependent signatures appear in Appendix A. The proposed all-joint-entries-to-local-envelope theorem and the arbitrary-compact-family continuity producer remain unresolved in this attempt; no declaration is invented for either as a proved result.
