# Hamilton front decomposition survey


> Orchestrator note (2026-09-08): this landed copy keeps sections 1-4 and appendices A-B (lines 1-1519 of the worker report). Appendix C (the 155-producer inventory with four equivalences) and appendix D (search method and negative findings) are retained unmerged on branch `worker/hamilton-front-decomposition` at its head commit because of their size. Tasks 1-3 of section 4 were implemented by the orchestrator as `Poincare/Global/HamiltonReactionEndpoint.lean`, `HamiltonEndpointEquivalences.lean`, and `HamiltonFiniteEnergyFlowInterface.lean`.

Date: 2026-09-08. Base: `468b5a67fca45c9b019665ad6c368c28ff6d7afa`.
Branch: `worker/hamilton-front-decomposition`.
Deliverable: this report only. Survey complete; no analytic existence theorem is claimed.

The main finding is a smaller checked dependency boundary: **the `reaction` field alone implies `HamiltonConvergencePinchedLimit3 M`**. The scratch proof in section 4 compiles against this base. It uses finite forward traceless energy and compact realization of the mean-energy pair. It does not use `compactTensorReferenceControl`, `hequicontinuous`, `hpointwiseCompact`, or `scalarSubordinateGeometry`. The five-field constructor is one sufficient producer, not the smallest available route to the current endpoint.

This removes four inputs from a possible replacement obligation. It does not construct `reaction`, a suitable flow, or an Einstein metric on an arbitrary manifold. The exact reserved Hamilton declaration remains absent, as the negative Lean probe records below.

I read the top of `HANDOFF.md` first, then `README.md`, `docs/PROJECT_MAP.md`, the supplied task, all seven named task context files, the plan-3 style reference, the nearest definitions and imports, and the relevant v2 mission/specification files. The worktree was clean at the base above. The report-only worker contract overrides the general instruction to edit `HANDOFF.md` and use a different branch prefix. No Lean source, root import, audit, mission, ledger, or handoff is changed. This worker does not mark a task accepted or merge it.

Evidence conventions:

- **Repo** means a source declaration found with `rg` and checked with Lean in this checkout. “Unconditional producer” means no unproduced analytic certificate, beyond the metric/manifold explicitly supplied to that lemma. A theorem taking an entire input record is conditional even when its proof is complete.
- **Mathlib** means the pinned tree at `7175569c842f9164564bd76ff8b207e7b4705522`, verified by `git -C .lake/packages/mathlib rev-parse HEAD`. Toolchain: `leanprover/lean4:v4.30.0-rc2`.
- **Absent** means no implementation/producer found in the searched sources, not a theorem of logical nonexistence. The exact missing Hamilton name additionally fails `#check`.
- Proposed names ending in `Survey` or `_survey` occur only in the displayed scratch program, not in the repository. New module paths in section 4 are proposals.
- Appendix A reproduces domain-specific record fields from source, including the embedded flow predicate, metric and partition structures. Recursion stops at standard foundational types such as topology, measures, sets, continuous linear maps and smooth maps; it does not expand the entire Mathlib typeclass graph. Appendix B prints constructors, so dependent field signatures were checked rather than guessed.

## 1. The five fields and their actual remaining content

All five fields belong to `Poincare.HamiltonFrontInputs.{u,v} M` in `Poincare/Global/HamiltonFrontStatements.lean:34`. Its manifold context is a Hausdorff, second countable, compact, connected, simply connected smooth three-manifold with a compatible Borel measurable structure. `v` is independent of `u`. Appendix A gives the literal source fields; Appendix B gives their elaborated dependent signatures.

### 1.1 `reaction`

Exact type: `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u,v} M`, defined at `Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare.lean:56`.

Its complete immediate field list is:

- `K`, `topologicalSpaceK`, `compactSpaceK`;
- `gt`, `metric`, `parameter`, `parameterContinuous`, `realizesFlow`;
- `meanScalarFloor`, `meanScalarFloor_pos`, `meanScalarLower`;
- `normalizedFlow`, `compactFiniteAtlasChartFrameDensityData`, `jointMetricEntries`;
- `reactionDecayRate`, `reactionDecayRate_pos`, `actualReactionDomination`;
- `finiteVolumeMeasureContinuous`, `scalarJointContinuous`, `tracelessRicciNormSqJointContinuous`.

The time family is defined on all real times. The PDE and reaction inequality are required on `Ici 0`; joint `C³` metric entries and the chart-frame density record are required at **every real time**. The compact parameterization covers forward times. Neither `K` being compact nor continuity of its scalar invariants says that the metric-valued map is continuous in a metric/jet topology.

The transitive project records are as follows.

1. `IsClosedNormalizedRicciFlowSolutionAt` in `Poincare/Global/NormalizedFlow.lean:91` has fields `leviCivita` and `flow`. The latter is the section-tested equation
   `deriv g(t)(Z,w) = -2 Ric(Z,w) + (2/3) meanScalar(g(t)) g(t)(Z,w)`.
   Its Levi-Civita predicate is the conjunction of metric compatibility and torsion freedom in `Poincare/RicciFlowEquation.lean:39`. Its test-field regularity is the explicit differentiability predicate in `Poincare/RiemannCurvatureOperator.lean:108`; the `C²` field abbreviation is in `Poincare/Global/RicciFlow.lean:31`.
2. `CompactFiniteAtlasChartFrameDensityData` is an abbreviation, not an additional structure. In `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:422` it is `GlobalFiniteExtendedChartFrameDensityData` on `compactFiniteExtendedChartCover`.
3. The latter global record has `timeSet`, `measureData`, `domination`. Its cover has `chartCount`, `anchor`, `sources_cover`.
4. Each `FiniteExtendedChartFrameMeasureData` has `density_integrable` and `areaFormula`.
5. Each `FiniteExtendedChartFrameDensityDominationAt` has `timeSet_mem`, `densityDerivative_aestronglyMeasurable_at`, `dominatingFunction`, `dominatingFunction_integrable`, `densityDerivative_bound`, `timeDifferentiable`.
6. `MetricEntriesJointContDiffAt` is a predicate: each anchored scalar metric entry is jointly `ContDiffAt` to the specified order, in `Poincare/Global/MetricFlowJointRegularity.lean:198`.
7. Each metric is `ClosedSmoothRiemannianMetric`, an abbreviation in `Poincare/Global/RiemannianContext.lean:44` for Mathlib's `Bundle.ContMDiffRiemannianMetric`. The underlying fields are `inner`, `symm`, `pos`, `isVonNBounded`, `contMDiff`, in `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:244`.

Deepest useful unconditional producers found:

- `exists_finiteExtendedChartCover` and `compactFiniteExtendedChartCover` in `HausdorffFiniteAtlasChartFrameReduction.lean` produce the finite genuine chart cover from the ambient compact manifold.
- `FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula` and `FiniteExtendedChartCover.hausdorffChartDensityEquality` in `Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean` prove the area/density equalities for a supplied metric and selected chart. The older report's claim that these area formulas remain open is stale for the repo.
- `FiniteExtendedChartFrameMeasureData.ofDensityIntegrable` removes its `areaFormula` premise, but **still assumes density integrability**. `GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable` still assumes this and local domination. These are conditional producers, not complete unconditional chart-frame records.
- `metricEntriesJointContDiffAt_const` handles a supplied constant metric family. `isClosedNormalizedRicciFlowSolutionAt_const_of_forall_isEinsteinAt` handles a supplied Einstein metric and nonzero volume. The latter volume condition is supplied by `GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib`. These do not construct an Einstein metric on arbitrary `M`.

The source producer
`NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3`
in `Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay.lean:280` is conditional. Its record has `pinching` and `pinchingCoefficientGap_pos`. The nested `NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3` contains the same compact family, mean floor, flow, chart-frame data, joint entries and three continuity fields listed above; it replaces reaction-rate data by `pinchingEpsilon`, `pinchingEpsilon_pos`, `pinchingEpsilon_le_one_third`, `pinchingDelta`, `pinchingDelta_nonneg`, `pinchingDelta_le_two`, `pinchingDelta_admissible`, `scalarPositive`, `ricciEigenvalueFloor`. All fields appear verbatim in Appendix A. No unconditional producer of that core was found. A positive coefficient gap is an extra quantitative premise, not a consequence of the name “Hamilton pinching”.

Open analytic statements: existence of the actual all-forward-time solution; the required joint regularity and local moving-density domination; a strictly positive mean floor for all forward times; uniform negative domination of the actual traceless-Ricci reaction with one positive rate; and compact realization by smooth metrics with the stated weak measure and joint curvature continuity. The area-formula field itself is already proved for the canonical finite inverse atlas.

**Can `reaction` be constructed without Ricci-flow short-time existence?** No construction on every manifold in the current context is available from landed material. The proposed nonstationary Ricci-flow route must supply local parabolic existence, continuation, estimates and a suitable initial geometry; merely supplying short-time existence would still be insufficient. This is a statement about the available proof route, not a logical necessity theorem: if a positive Einstein metric were supplied independently, its constant normalized family would solve the PDE without invoking a general short-time theorem. Completing all the other static reaction fields from that metric was not proved here. In particular, a constant arbitrary metric is not automatically a solution.

Hamilton's positive-Ricci convergence problem also presupposes suitable positive-Ricci initial geometry. The universal statement in this task assumes only simple connectivity, not such a metric. No conversion of that topological assumption into the required initial pinching data was found. One must not present the positive-Ricci special case as a solution of this universal obligation. This is part of the Hamilton/Perelman analytic core, including the problem of reaching suitable geometry from general initial data.

### 1.2 `compactTensorReferenceControl`

Exact type, after installing `reaction.topologicalSpaceK`:
`CompactReferenceMetricTensorFamilyData reaction.K reaction.metric`, in `Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean:94`.

All fields: `referenceMetric`, `metricFactor`, `volumeFactor`, `metricFactor_continuous`, `volumeFactor_continuous`, `metricFactor_pos`, `volumeFactor_pos`, `metric_le`, `volume_le`. The last two are quadratic-form domination by the square of the metric factor and a lower comparison of volume on **every measurable set**. Its only further domain record is the supplied reference metric, expanded above.

No unconditional constructor for the whole family record was found. Its `uniformBallVolumeLower` and `exists_uniformMetricLowerComparison` theorems are real consequences of supplied tensor/volume comparison data; they do not produce those data. The former is in the defining module and the latter in `Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean:525`. They were both source-verified and probed.

Open: common reference comparison valid throughout the ambient family, with continuous positive factors and the all-measurable-set volume inequality. Compactness of an arbitrarily topologized `K`, plus only scalar/Ricci invariant continuity, does not directly supply joint tensor control. The relation to intrinsic curvature/injectivity estimates or a suitable fixed-manifold gauge remains to be developed. For the endpoint route found in this survey this field is unnecessary, not proved.

### 1.3 `hequicontinuous`

Exact type:
`∀ slot : MetricEntryThirdJetSlot 3 M, Equicontinuous (fun t : Ici (0 : ℝ) => (metricEntryThirdJetProfile (reaction.gt t.1) slot : ClosedSmoothModel 3 → ℝ))`.

This is a proposition, not a project record. `MetricEntryThirdJetSlot` in `Poincare/Global/ClosedMetricThirdJetTopology.lean:38` has four constructors: `value x i j`, `first x u i j`, `second x u a i j`, `third x u a b i j`. `metricEntryThirdJetProfile` at line 115 gives the scalar cutoff-blended value and first three spatial derivatives as continuous maps. Each slot fixes its own anchor/vectors; the quantifier does not demand a single modulus uniform over all slots.

The repo produces each profile's continuity and proves `metricEntryThirdJetProfile_differentiable` in `Poincare/Global/MetricEntryThirdJetProfileCompactness.lean:40`. Its three `isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise...` theorems give formal-profile compactness from equicontinuity/pointwise compactness, boundedness, or derivative bounds. None establishes a uniform-forward-time derivative bound for this unknown flow. The derivative-bound version of the positive-Einstein constructor retains explicit per-slot derivative bounds and bounded values at zero; it does not discharge them.

Open: a uniform-in-forward-time spatial modulus for every scalar jet profile. Smoothness at each individual time is insufficient. Deriving this from a flow requires uniform derivative estimates in the retained coordinates, with chart/gauge control. Curvature derivative estimates alone must still be related to these particular metric jets. The field is unnecessary for the newly checked endpoint route.

### 1.4 `hpointwiseCompact`

Exact type:
`∀ (slot : MetricEntryThirdJetSlot 3 M) (z : ClosedSmoothModel 3), ∃ Q : Set ℝ, IsCompact Q ∧ ∀ t : Ici (0 : ℝ), metricEntryThirdJetProfile (reaction.gt t.1) slot z ∈ Q`.

There are no new transitive project records. This is boundedness in real numbers for each fixed slot and coordinate point, uniformly over all forward times. The bounded componentwise theorem above already converts bounded ranges to compact closures. That conversion is proved; the bounds for the unknown flow are not. Compactness of `M` is spatial, and does not compactify the forward time interval. Weak continuity of the measures or curvature scalars on `K` does not state continuity of these jet evaluations.

Open: those actual uniform bounds, or a stronger estimate implying them. This field too is unnecessary for the newly checked endpoint route.

### 1.5 `scalarSubordinateGeometry`

Exact type:
`∀ t : Ici (0 : ℝ), FiniteSubordinateHausdorffLaplacianGeometry (reaction.gt t.1) (fun y => (reaction.gt t.1).scalarAt y)`.

The record is in `Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:388`. Its complete fields are:

- `chartCount`, `coordinateDomain`, `coordinateDomain_measurable`, `inverseChart`, `inverseChart_measurable`, `chartRegion`, `chartRegion_isOpen`;
- `density`, `density_nonneg`, `density_integrable`, `chartMeasure`;
- `partition`, `partition_subordinate`, `f_contMDiff_two`;
- `coordinateRepresentative`, `coordinateRepresentative_eq`, `coordinateRepresentative_contDiff_two`, `coordinateRepresentative_hasCompactSupport`, `coordinateRepresentative_tsupport_subset_coordinateDomain`;
- `weight`, `weight_contDiff_one`, `weight_eq_density`;
- `inverseMetric`, `inverseMetric_contDiff_one`, `christoffel`, `contractedChristoffel`, `contractedChristoffel_eq`;
- `density_inverseMetric_compatibility`, `intrinsicCoordinateLaplacian_eq`, `localizedLaplacian_aestronglyMeasurable`.

The embedded `SmoothPartitionOfUnity` is Mathlib's record in `Geometry/Manifold/PartitionOfUnity.lean:122`, with `toFun`, `locallyFinite'`, `nonneg'`, `sum_eq_one'`, `sum_le_one'`; its values are smooth functions. `HausdorffChartDensityEquality` in `Poincare/Global/HausdorffCoordinateDensityVariation.lean:82` is a measure equality, not a further record. Appendix A displays it.

Deepest unconditional ingredients: the finite genuine chart cover; Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` for an open cover; and the inverse-chart area theorem for a supplied metric. The scalar `f_contMDiff_two` clause is already derivable from a supplied `reaction`; section 4 contains a passing proof using `scalarAt_contMDiffAt_two_of_normalizedRicciFlow` and the joint-metric-entry regularity bridge. This is stronger than merely citing `scalarAt_mdifferentiableAt`, which alone gives only first differentiability.

The full geometry record has no unconditional producer found. `FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes` proves Stokes **from** that record and thus cannot construct it. The missing assembly includes globally extended `C²` localized representatives with the exact support containment, `C¹` weights/inverse coefficients, density compatibility, and the intrinsic coordinate formula for those choices. The finite disjoint atlas used by the reaction-density record has measurable pieces; the scalar partition record requires open `chartRegion`s. Do not identify these records by changing a field name or assume disjoint pieces form the requested open cover. The appropriate open inverse-chart restrictions and partition must be constructed compatibly.

This field is a local geometry/integration assembly question, not itself all of Ricci-flow existence. Its exact full producer is class C below. It is also unnecessary for the newly checked endpoint route.

## 2. Alternative producers and comparison of assumptions

Appendix C is an exhaustive source inventory of **155 explicitly typed direct producer theorems and four endpoint equivalences** found under `Poincare/` whose final result is one of the requested endpoint propositions, including the two universal propositions. Each entry gives its path, source location, fully qualified name, and the actual `#check` output containing all hypotheses. This includes specialized record consumers, finite-time/forward-time variants, energy and compactness variants, and the round-sphere special case. It excludes theorems merely accepting an endpoint as a hypothesis and ending in a sphere/Poincare conclusion. The four equivalences are identifiable by `↔` in their printed results; three are also repeated among the supporting checks in Appendix B. Source searches against pinned Mathlib found none of these project endpoint names there.

The inventory parser was corrected to respect bracket nesting before locating `:=`; otherwise occurrences such as `(M := M)` incorrectly truncated some signatures. The final inventory has 159 passing checks, not the initial incomplete count of 133. Names were also verified by `rg` against their source files. The parser, checks and actual output are included below so the enumeration can be rerun. The verification script uses “producer” as a label for all 159 entries; four of these are equivalences, not direct implication results.

The useful ordering is by sufficient *mathematical content*, not the number of packaged arguments:

| Rank / route | Smallest visible sufficient premises | What is already proved / what remains |
| --- | --- | --- |
| 1. Direct endpoint | One positive Einstein metric; equivalently one smooth metric with identically zero traceless Ricci and positive scalar somewhere. | Both directions between the core and positive Einstein are proved in `PinchedLimitPositiveEinstein.lean`; scalar regularity bridges the original endpoint in `PinchedLimitInterface.lean`. Existence of such a metric on arbitrary `M` remains the whole endpoint. |
| 1. Stationary form | A smooth metric with zero normalized RHS and positive mean scalar. | `positiveEinsteinMetric3_of_normalizedRicciStationary` and `exists_normalizedRicciStationary_iff_positiveEinsteinMetric3` identify this with rank 1. It is an equivalent formulation, not analytic progress. |
| 2. Zero-energy metric | A supplied metric with zero total squared traceless-Ricci energy and positive mean scalar. | `hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto` in `VolumeMeasureOpenPositivity.lean` removes extra positivity-of-open-measure/pointwise regularity premises. Producing that metric remains open. |
| 3. Finite-energy compact realization | A smooth metric family, integrable forward total traceless energy, a compact parameter family realizing it, continuous mean-energy pair, and one positive mean floor. | `hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower` proves the endpoint without a PDE or Stokes input. These existence, decay and realization hypotheses remain substantial. |
| 3b. Closed attained range | Finite forward traceless energy, closed **actual** forward mean-energy range, positive lower and finite upper mean bounds. | `hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds` bypasses the compact parameter space. Closedness of the attained range is strong: the limiting zero-energy pair must be attained by an original finite-time metric. No derivation from ordinary asymptotic convergence was found. Treat this hypothesis as C, not an easier compactness theorem. |
| 3c. Sampled pinching / convergence | A family with sampled decay plus compact realized invariant range and positive scalar control; or a limit metric with the required component/time-derivative convergence. | The `NormalizedFlowPinchingLimit`, `NormalizedFlowPointwiseConvergence` and `NormalizedFlowConvergenceEndpoint` entries in Appendix C retain those estimates/realization premises. They are incomparable presentations until such premises are produced. |
| 4. Reaction only | The single `reaction` record of section 1.1. | It produces the finite-energy moving-measure record, which produces continuous invariant pairs, which feeds rank 3. The scratch proof establishes this implication. The four other front fields are unused. |
| 5. Five-field / enhanced finite-time packages | Reaction plus tensor comparison, third-jet controls, scalar partition geometry; or finite dissipation, Hamilton improvement/evolution, gradient/curvature derivative bounds and related compactness packages. | These are all proved conditional consumers, individually listed in Appendix C. They can be useful if one studies stronger flow conclusions, but do not lower the current endpoint's premise count. |
| Special case | The standard round sphere itself. | `positiveEinsteinMetric3_roundSphere` in `ConstantCurvatureEinstein.lean` is unconditional at that particular manifold. No arbitrary-manifold transfer follows merely from having a homeomorphism statement. |

Energy-critical-slice routes in `NormalizedFlowEnergyCriticality.lean` ask for a mean-energy derivative identity, a critical mean value, vanishing scalar variance and positive mean. These feed the stationary/zero-energy group. Dissipation routes ask for finite absolute dissipation or an exponential/differential decay law, along with the required moving-volume and total-scalar identities and limit/compactness controls. Forward-rescaling routes additionally assume their original flow and rescaling/time-change data. The detailed hypotheses are printed in Appendix C; no whole record is counted as a proved input merely because its consumer takes one argument.

Positive Einstein existence is **no stronger than** the five-input existence statement: the repository explicitly proves the implication from five inputs to positive Einstein existence, and the scratch universal equivalence identifies the latter with universal Hamilton convergence. I did not find or prove the reverse implication from positive Einstein existence to all five inputs. In particular, constructing a stationary family does not, without further work, populate its chart-density and subordinate-geometry records. Therefore strict weakness versus equivalence is **unclear**, not established. Calling positive Einstein existence “stronger” because it sounds like a classification theorem would contradict the checked forward implication; calling it strictly weaker would also exceed the evidence.

Only `universalHamiltonConvergence_of_universalHamiltonFrontInputs` is currently registered as the producer in `hamilton-front.json`. The newly checked reaction-only and universal positive-Einstein adapters exist in this report's scratch program, not as landed or registered declarations. There is no unconditional universal endpoint in this checkout.

## 3. Classification of the open premises

A = follows from landed material with a concrete checked assembly or specified local construction. B = requires substantial missing analytic theory for arbitrary manifolds; the pinned Mathlib does not contain the stated general theorem, although this repo may contain conditional pieces. C = exact producer or implication not established in this survey. Ambient manifold/typeclass hypotheses are the given problem context, not new analytic obligations.

| Premise or field group | Class | Evidence and precise remaining work |
| --- | --- | --- |
| Reaction-only endpoint assembly; universalization with the canonical Borel structure | A | Full scratch proofs in section 4. No new estimate. |
| Universal Hamilton / universal positive-Einstein equivalence | A | Compose the two landed per-manifold equivalences; full scratch proof below. |
| Finite chart cover and its measurable inverse-chart bookkeeping; restricted area equality | A, already landed | The exact producers in section 1.1 have no analytic input beyond a metric where required. Do not reopen the old area-formula gap. |
| Scalar `f_contMDiff_two` for a supplied reaction | A | Forward-time slice proof below; no extension of the flow equation to negative times is used. |
| Bounded range → compact real range closure; equicontinuity + compact pointwise range → formal profile compactness | A, already landed | The three checked componentwise profile compactness theorems. They do not supply the actual bounds. |
| `gt` together with the genuine normalized PDE on all forward times | B | Closed-manifold parabolic local existence, compatibility/gluing of local constructions, normalization and long-time continuation. Existing DeTurck/BUC coordinate germs and conditional pullback adapters are not a universal global solution. |
| Suitable positive-Ricci/pinched initial geometry under only the universal topological assumptions | B | Hamilton positive-Ricci convergence alone does not produce this input. A general-manifold route must address singularities/topology or independently construct suitable geometry. |
| `jointMetricEntries` uniformly available at all required times | B for the unknown global solution | Parabolic regularity along the actual solution and compatible fixed-chart control; constant-family regularity is only a special case. |
| `meanScalarFloor`, positivity and `meanScalarLower`; scalar floors in alternative routes | B | A global positive normalization/curvature control theorem for the produced solution. Once a suitable flow and initial sign are supplied, some maximum-principle algebra is already in the repo. That does not furnish universal initial data or a global solution. |
| Positive reaction rate and `actualReactionDomination`; the Hamilton core's eigenvalue floor and positive coefficient gap | B | Uniform pinching/reaction estimates for the actual long-time flow. The pointwise algebra and conditional parabolic comparison/energy decay are landed; producing the sign/gap on the required orbit is not. |
| Compact `K`, `metric`, `parameter`, `realizesFlow`; all three measure/curvature continuities on it | B as a combined existence assertion | Smooth realized compactness with nondegeneration, derivative bounds, and chart/diffeomorphism control. A Cheeger-Gromov/injectivity-radius compactness argument is one possible program absent from pinned Mathlib, not a proved requirement of this abstract statement. The invariant-pair endpoint needs less topology, but still needs actual smooth metric realization of its limiting pair. |
| Density integrability in each finite inverse chart | C, likely local work | The exact area theorem and finite metric volume suggest a proof from nonnegative measurable density and finiteness of its weighted measure. No such complete constructor was verified here. This is not a reason to label all manifold integration absent from the repo. |
| `timeSet_mem`, measurable density derivative, integrable dominating function, uniform derivative bound, time differentiability | C for the exact chart-frame record | Joint metric regularity suggests local-in-time control; matching the specific disjoint inverse charts and integrable majorant is unproved here. Constants in coordinates need not be integrable on an unbounded coordinate domain. Do not substitute compactness of `M` for a coordinate domination proof. |
| Tensor-reference metric and continuous factors with `metric_le` / `volume_le` | C from a supplied reaction; B for producing estimates with a new global flow | The current reaction does not expose joint tensor continuity. Derive such control from a stronger proved geometry of the metric family, or retain it as an additional hypothesis. |
| Equicontinuity of every jet profile over forward time | B for the unknown flow | Uniform metric-jet estimates, typically using parabolic derivative estimates such as Shi-type estimates and coordinate/gauge comparison. Individual profile differentiability is already landed. |
| Actual pointwise-in-space uniform bounds over forward time | B for the unknown flow | Same uniform estimates/nondegeneration issue; compactness of space alone is insufficient. |
| Scalar partition geometry's cover/partition existence in isolation | A for an open cover | Mathlib supplies a subordinate smooth partition for an open cover. This does not identify the density, zero extensions and coefficients simultaneously. |
| All remaining scalar partition fields after cover existence and scalar `C²` regularity | C | Exact compatible coordinate choice, smooth extensions/support, integrable density, determinant/connection compatibility, intrinsic Laplacian identification, and localized measurability still need a proof in the stated record. The conditional Stokes theorem is already landed. |
| Finite energy / finite absolute dissipation / exponential decay in alternative routes | B when asserted for an unknown global flow; A conditional on a supplied reaction | The reaction-to-finite-energy map is proved. No unconditional decay theorem supplying its own arbitrary-manifold flow is found. |
| Mean/volume differentiation, scalar variance/energy identities in alternative routes | A after their listed variation/regularity/Stokes hypotheses; C for assembling those hypotheses from a bare flow | Inspect each printed signature; differentiating a moving integral is not automatic from the word “flow”. |
| Compact actual invariant range, closed attained range, or lower-semicontinuous metric realization in alternative routes | C for implication from an existing weaker assumption; B as the geometric compactness work of a new analytic program | An abstract topological compactness theorem is not the missing realization theorem. Closed attained range can even demand a finite-time Einstein slice. |
| Zero energy / stationary positive slice / positive-Einstein metric supplied outright | B as universal existence; A for the equivalences and consumers | These are endpoint formulations. No classification or Ricci-flow construction disappears by renaming one. |
| Reverse construction of all five inputs from a positive Einstein metric | C | The stationary PDE is available, but the exact remaining record construction was not checked. No strictness claim follows. |

This table applies to every analytic hypothesis in the producer inventory by mathematical content: an extra supplied flow, regularity package, estimate, moving-integral identity, or compactness/limit witness belongs to the corresponding row. Record-valued arguments retain the classification of their fields; they do not acquire class A because a constructor bundles them. Trivial arithmetic bounds and parameter/typeclass bookkeeping are class A once the underlying witnesses are supplied.

Pinned Mathlib search results are recorded in Appendix D. It has smooth Riemannian metric and partition structures, ODE and Euclidean analytic infrastructure. The search for Ricci flow, DeTurck, Shi estimates, Cheeger-Gromov, Hamilton compactness, parabolic existence/Schauder and injectivity radius produced only two irrelevant matrix “parabolic” hits. The closed-manifold parabolic existence/convergence library is absent from that tree. This does **not** mean the repo has no integration, no maximum principle, no DeTurck work, or no geometric recognition: those blanket claims in old survey prose are too broad at the current base.

`ricciFlowShortTimeExistence3_of_deTurck_of_pullback` still assumes both the DeTurck short-time interface and the pullback interface. The more recent `exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries` assumes a supplied global metric family, chart identifications and remainder data; it produces point-indexed coordinate flow germs. Its actual long signature is checked in Appendix B. It does not close universal global flow existence.

## 4. Numbered task plan and checked target program

Shared contract: start from the exact base above. Each proposed implementation task owns only its named new module and a task report; existing Lean files, the six frozen contract files, root import, audit scripts, missions, and ledgers are forbidden to the proof worker. The orchestrator can later authorize minimal import/mission integration after independent review. Freeze a new exact base before dispatch if prerequisites have been integrated. These are proposed tasks, not accepted work. In this survey every definition/proof below exists only under `/tmp`.

### Task 1. `Poincare/Global/HamiltonReactionEndpoint.lean`

Namespace: `Poincare`. Imports: `Poincare.Global.HamiltonFrontStatements`, `Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint`.

Objective: expose the reaction-only Hamilton producer and its universal adapter. The displayed `hamilton_of_reaction_survey` and `UniversalHamiltonReactionExistenceSurvey` are checked scratch spellings for the proposed declarations. Their complete signatures and proofs are in the program below. The finite-energy map supplies the entire compact mean-energy payload; install its own compact-space instances and apply the existing finite-energy endpoint. Universalization chooses `borel N` exactly as the landed front adapter does. This task removes four independent analytic assumptions from the producer route; it is not an alias-only task.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionEndpoint.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HamiltonReactionEndpoint.lean
git diff --check
```

Exact stop: both local and universal producers elaborate with no tensor-reference, jet, subordinate-geometry or recognition hypothesis. Do not construct or declare the reserved unconditional Hamilton theorem. The orchestrator may replace the front-input obligation by the universal reaction statement only after verifying the literal implication and freezing the new statement separately.

### Task 2. `Poincare/Global/HamiltonEndpointEquivalences.lean`

Namespace: `Poincare`. Imports: `Poincare.Global.HamiltonFrontStatements`, `Poincare.Global.PinchedLimitPositiveEinstein`.

Objective: record the exact universal equivalence displayed below if the mission reviewer needs an explicit alternative producer from universal positive Einstein existence. The proof is the pointwise composition of the existing equivalences. Do not dispatch this as an independent “analytic progress” milestone; fold it into the review/integration of task 1 unless a separately pinned alternative route is required.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEndpointEquivalences.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HamiltonEndpointEquivalences.lean
git diff --check
```

Exact stop: the literal universal equivalence elaborates in universe `u`, with the same manifold binders and no extra measurable, flow or recognition assumptions. A one-way stronger theorem is not the displayed objective. No existence node is discharged by proving an equivalence.

### Task 3. `Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean`

Namespace: `Poincare`. Imports: `Poincare.Global.HamiltonFrontStatements`, `Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint`.

Objective: if a new analytic obligation is wanted rather than retaining the existing reaction record, state the smaller sufficient **global finite-energy normalized-flow existence** proposition displayed below, its universal version, and the checked reductions `reaction → new statement → Hamilton endpoint`. This task defines an interface and proves its consumers; it does not prove existence. It contains an actual all-forward-time normalized PDE, finite energy, positive mean floor and smooth compact realization, with no input metric imposed. The task is to construct a suitable family on each manifold, not to evolve an arbitrary initial metric.

This is the smallest sufficient flow-existence boundary identified here that removes the reaction/density/jet machinery while reusing a landed analytic endpoint directly. No absolute minimality among equivalent propositions is claimed. The flow equation is deliberately retained because this is a Ricci-flow existence obligation; the current endpoint consumer uses only finite energy and compact invariant realization and does not need that clause. Dropping it gives an even weaker analytic family-existence statement, not a Ricci-flow existence statement. The compact parameter universe remains `v`; no implicit equality with `u` is imposed.

The literal existing bare short-time interface `RicciFlowShortTimeExistence3` is also checked below. It asks for every initial metric, `T > 0`, a family with the correct initial value, and the unnormalized equation on **`Ico 0 T`**. The source docstring's `(0,T)` wording is not the actual interval. This interface is already defined; do not add a duplicate. It cannot replace the Hamilton obligation by itself: positive suitable initial geometry, long-time continuation, decay, positive mean floor and realized compactness would all remain unproved. Nor does it provide the full regularity packages merely by stating the PDE.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HamiltonFiniteEnergyFlowInterface.lean
git diff --check
```

Exact stop: the local/universal propositions and both conditional implication directions shown below compile. The existence proposition stays open. A statement mentioning only short-time existence, or an unrelated limit metric without realization by the supplied family, fails this target. Mission mutation belongs to a separate orchestrator review; the existing endpoint type and frozen definitions remain unchanged.

### Task 4. `Poincare/Global/HamiltonReactionScalarRegularity.lean`, optional local geometry work

Namespace: `Poincare`. Imports: `Poincare.Global.HamiltonFrontStatements`.

Objective: if another consumer still needs the scalar partition record, discharge its scalar `C²` subfield directly from the supplied reaction, with the exact forward-time statement below. The slice equation and joint entry regularity feed the two checked local regularity lemmas. The proof already compiles in scratch. There is no reason to dispatch this task for the Hamilton endpoint alone after task 1; fold this small lemma into a genuine future scalar-geometry constructor task.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonReactionScalarRegularity.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HamiltonReactionScalarRegularity.lean
git diff --check
```

Exact stop: scalar `ContMDiff ... 2` holds for every `t : Ici 0` with only the reaction record. A first-differentiability result or an extra all-real-time flow assumption is insufficient. Do not claim the rest of the subordinate geometry record is constructed. Its class-C production question should be resolved before freezing a larger task; this survey does not invent a proof plan for its resisting compatibility/support fields.

### Complete scratch target program

The following is the exact final source of `/tmp/hamilton-front-decomposition-evidence/plan.lean`. It contains actual proofs for the class-A reductions and statement definitions for the proposed interface. No placeholder body is used. Its import envelope contains the union of the proposed task imports, plus the stationary and short-time modules used for checks.

<!-- plan-source-start -->
```lean
import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowStationaryLimit
import Poincare.Global.ShortTimeInterface
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
-- Task 1, proof in scratch only.
theorem hamilton_of_reaction_survey (reaction : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u,v} M) :
    HamiltonConvergencePinchedLimit3 M := by
  let data := reaction.toMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  apply (hamiltonConvergencePinchedLimit3_iff_core (M := M)).mpr
  exact hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    data.gt data.finiteTracelessRicciEnergy data.metric data.parameter data.realizesFlow
    data.invariantPairContinuous data.meanScalarFloor_pos data.meanScalarLower
-- Universal reaction-only obligation, proposed scratch spelling.
def UniversalHamiltonReactionExistenceSurvey : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      Nonempty (NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u,v} N)
example (h : UniversalHamiltonReactionExistenceSurvey.{u,v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamilton_of_reaction_survey (Classical.choice (h N))
-- Automatic scalar-regularity subfield for a supplied reaction record.
example (r : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u,v} M)
    (t : Ici (0 : ℝ)) :
    ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun x : M ↦ (r.gt t.1).scalarAt x) := by
  intro x
  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
    (r.normalizedFlow t.1 t.2)
    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (r.jointMetricEntries t.1 y)) x
-- Task 2, universal equivalence, proof in scratch only.
example : UniversalHamiltonConvergenceStatement.{u} ↔ UniversalPositiveEinsteinStatement.{u} := by
  constructor
  · intro h N _ _ _ _ _ _ _ _
    exact positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core
      ((hamiltonConvergencePinchedLimit3_iff_core (M := N)).mp (h N))
  · intro h N _ _ _ _ _ _ _ _
    exact hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3 (h N)
-- Task 3, minimal sufficient finite-energy flow interface. Proposed name, not in repo.
def HamiltonFiniteEnergyFlowExistence3Survey : Prop :=
  ∃ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (c : ℝ),
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) ∧
      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
theorem hamilton_of_finiteEnergy_survey (h : HamiltonFiniteEnergyFlowExistence3Survey.{u,v} (M := M)) :
    HamiltonConvergencePinchedLimit3 M := by
  rcases h with ⟨gt, K, topK, compactK, metric, parameter, c, _flow, hE, hreal, hcont, hc, hlower⟩
  letI : TopologicalSpace K := topK
  letI : CompactSpace K := compactK
  exact (hamiltonConvergencePinchedLimit3_iff_core (M := M)).mpr
    (hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt hE metric parameter hreal hcont hc hlower)
example (r : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u,v} M) :
    HamiltonFiniteEnergyFlowExistence3Survey.{u,v} (M := M) := by
  let d := r.toMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
  exact ⟨d.gt, d.K, d.topologicalSpaceK, d.compactSpaceK, d.metric, d.parameter,
    d.meanScalarFloor, r.normalizedFlow, d.finiteTracelessRicciEnergy,
    d.realizesFlow, d.invariantPairContinuous, d.meanScalarFloor_pos, d.meanScalarLower⟩
def UniversalHamiltonFiniteEnergyFlowExistenceSurvey : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonFiniteEnergyFlowExistence3Survey.{u,v} (M := N)
example (h : UniversalHamiltonFiniteEnergyFlowExistenceSurvey.{u,v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamilton_of_finiteEnergy_survey (h N)
-- Bare short-time existence is stated separately and is not sufficient for convergence.
#check RicciFlowShortTimeExistence3
#check ricciFlowShortTimeExistence3_eq
end Poincare

#print axioms Poincare.hamilton_of_reaction_survey
#print axioms Poincare.hamilton_of_finiteEnergy_survey
```
<!-- plan-source-end -->

### Actual plan probe result

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-front-decomposition-evidence/plan.lean > /tmp/hamilton-front-decomposition-evidence/plan-03.log 2>&1
exit_code=0
```

Actual complete output:

```text
Poincare.RicciFlowShortTimeExistence3.{u} (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
Poincare.ricciFlowShortTimeExistence3_eq.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M] :
  RicciFlowShortTimeExistence3 M =
    ∀ (g₀ : ClosedSmoothRiemannianMetric 3 M),
      ∃ T, 0 < T ∧ ∃ gt, gt 0 = g₀ ∧ ∀ t ∈ Ico 0 T, ∀ (x : M), IsClosedRicciFlowSolutionAt gt t x
'Poincare.hamilton_of_reaction_survey' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.hamilton_of_finiteEnergy_survey' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first and second plan attempts also passed. Attempt 2 added the universal reaction and scalar regularity proofs; attempt 3 added the finite-energy universal statement, reaction-to-interface proof, disabled auto-implicit variables and printed the two named proof closures. These are scratch proofs, not landed declarations.

## Appendix A. Exact source field expansion

The following snippets were read from the base source. Names are source-verified by the `rg` log in Appendix D. They are reference excerpts, not standalone modules to compile. The constructor checks in Appendix B verify all dependent field types together.

### `Poincare/Global/HamiltonFrontStatements.lean:34`

```lean
structure HamiltonFrontInputs (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  reaction :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
        M
  compactTensorReferenceControl :
      letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
      CompactReferenceMetricTensorFamilyData reaction.K reaction.metric
  hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : Ici (0 : ℝ) =>
        (metricEntryThirdJetProfile (reaction.gt t.1) slot :
          ClosedSmoothModel 3 → ℝ))
  hpointwiseCompact :
      ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : ClosedSmoothModel 3),
        ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ t : Ici (0 : ℝ),
            metricEntryThirdJetProfile (reaction.gt t.1) slot z ∈ Q
  scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
      FiniteSubordinateHausdorffLaplacianGeometry
        (reaction.gt t.1) (fun y => (reaction.gt t.1).scalarAt y)
```

### `Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare.lean:56`

```lean
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  compactFiniteAtlasChartFrameDensityData :
    CompactFiniteAtlasChartFrameDensityData gt
  jointMetricEntries : ∀ t : ℝ, ∀ x : M,
    MetricEntriesJointContDiffAt gt t x 3
  reactionDecayRate : ℝ
  reactionDecayRate_pos : 0 < reactionDecayRate
  actualReactionDomination : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
      -reactionDecayRate * (gt t).tracelessRicciNormSqAt x
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
```

### `Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay.lean:37`

```lean
structure NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  compactFiniteAtlasChartFrameDensityData :
    CompactFiniteAtlasChartFrameDensityData gt
  jointMetricEntries : ∀ t : ℝ, ∀ x : M,
    MetricEntriesJointContDiffAt gt t x 3
  pinchingEpsilon : ℝ
  pinchingEpsilon_pos : 0 < pinchingEpsilon
  pinchingEpsilon_le_one_third : pinchingEpsilon ≤ 1 / 3
  pinchingDelta : ℝ
  pinchingDelta_nonneg : 0 ≤ pinchingDelta
  pinchingDelta_le_two : pinchingDelta ≤ 2
  pinchingDelta_admissible :
    pinchingDelta ≤
      PinchingAlgebra.pinchedTracelessAdmissibleDelta3 pinchingEpsilon
  scalarPositive : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    0 < (gt t).scalarAt x
  ricciEigenvalueFloor : ∀ t ∈ Ici (0 : ℝ),
    GlobalRicciEigenvalueFloor3 (gt t) pinchingEpsilon
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
```

### `Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay.lean:235`

```lean
structure NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  pinching :
    NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v}
      M
  pinchingCoefficientGap_pos : 0 < pinching.pinchingCoefficientGap
```

### `Poincare/Global/NormalizedFlowFiniteTimeCurvatureCompactness.lean:94`

```lean
structure CompactReferenceMetricTensorFamilyData
    (K : Type v) [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M) where
  referenceMetric : ClosedSmoothRiemannianMetric 3 M
  metricFactor : K → ℝ
  volumeFactor : K → ℝ
  metricFactor_continuous : Continuous metricFactor
  volumeFactor_continuous : Continuous volumeFactor
  metricFactor_pos : ∀ k, 0 < metricFactor k
  volumeFactor_pos : ∀ k, 0 < volumeFactor k
  metric_le : ∀ k x
      (w : TangentSpace (closedSmoothModelWithCorners 3) x),
    (metric k).inner x w w ≤
      (metricFactor k) ^ 2 * referenceMetric.inner x w w
  volume_le : ∀ k (A : Set M), MeasurableSet A →
    volumeFactor k * (volumeMeasure referenceMetric).real A ≤
      (volumeMeasure (metric k)).real A
```

### `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:85`

```lean
noncomputable def compactFiniteExtendedChartCover :
    FiniteExtendedChartCover (n := n) (M := M) :=
  Classical.choice exists_finiteExtendedChartCover
```

### `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:301`

```lean
structure FiniteExtendedChartFrameMeasureData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (s : Set ℝ) where
  density_integrable : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    Integrable (C.inverseChartDensity (gt t) i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  areaFormula : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    C.RestrictedInverseChartPullbackHausdorffAreaFormula (gt t) i
```

### `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:347`

```lean
structure FiniteExtendedChartFrameDensityDominationAt
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (s : Set ℝ) (t₀ : ℝ) where
  timeSet_mem : s ∈ 𝓝 t₀
  densityDerivative_aestronglyMeasurable_at : ∀ i,
    AEStronglyMeasurable
      (finiteExtendedChartFrameDensityDerivative C gt t₀ i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  dominatingFunction :
    (i : Fin C.chartCount) → C.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  densityDerivative_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
      ∀ t ∈ s,
        ‖finiteExtendedChartFrameDensityDerivative C gt t i z‖ ≤
          dominatingFunction i z
  timeDifferentiable : ∀ i (z : C.coordinateDomain i) t,
    t ∈ s → TimeDifferentiableAt gt t (C.inverseChart i z)
```

### `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:391`

```lean
structure GlobalFiniteExtendedChartFrameDensityData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  timeSet : ℝ → Set ℝ
  measureData : ∀ t : ℝ,
    FiniteExtendedChartFrameMeasureData C gt (timeSet t)
  domination : ∀ t : ℝ,
    FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t
```

### `Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:422`

```lean
abbrev CompactFiniteAtlasChartFrameDensityData
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) :=
  GlobalFiniteExtendedChartFrameDensityData
    (compactFiniteExtendedChartCover (n := n) (M := M)) gt
```

### `Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:388`

```lean
structure FiniteSubordinateHausdorffLaplacianGeometry
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) where
  chartCount : ℕ
  coordinateDomain : Fin chartCount → Set E
  coordinateDomain_measurable : ∀ i, MeasurableSet (coordinateDomain i)
  inverseChart : (i : Fin chartCount) → coordinateDomain i → M
  inverseChart_measurable : ∀ i, Measurable (inverseChart i)
  chartRegion : Fin chartCount → Set M
  chartRegion_isOpen : ∀ i, IsOpen (chartRegion i)
  density : (i : Fin chartCount) → coordinateDomain i → ℝ
  density_nonneg : ∀ i,
    0 ≤ᵐ[coordinateLebesgueMeasure (coordinateDomain i)] density i
  density_integrable : ∀ i,
    Integrable (density i) (coordinateLebesgueMeasure (coordinateDomain i))
  chartMeasure : ∀ i,
    HausdorffChartDensityEquality g
      (coordinateDomain i) (inverseChart i) (chartRegion i) (density i)
  partition : SmoothPartitionOfUnity (Fin chartCount) I M Set.univ
  partition_subordinate : partition.IsSubordinate chartRegion
  f_contMDiff_two : ContMDiff I 𝓘(ℝ) 2 f
  coordinateRepresentative : Fin chartCount → E → ℝ
  coordinateRepresentative_eq : ∀ i (z : coordinateDomain i),
    coordinateRepresentative i z =
      partition i (inverseChart i z) * f (inverseChart i z)
  coordinateRepresentative_contDiff_two : ∀ i,
    ContDiff ℝ 2 (coordinateRepresentative i)
  coordinateRepresentative_hasCompactSupport : ∀ i,
    HasCompactSupport (coordinateRepresentative i)
  coordinateRepresentative_tsupport_subset_coordinateDomain : ∀ i,
    tsupport (coordinateRepresentative i) ⊆ coordinateDomain i
  weight : Fin chartCount → E → ℝ
  weight_contDiff_one : ∀ i, ContDiff ℝ 1 (weight i)
  weight_eq_density : ∀ i (z : coordinateDomain i),
    weight i z = (rawHausdorffLebesgueScale n : ℝ) * density i z
  inverseMetric : Fin chartCount → E → Fin n → Fin n → ℝ
  inverseMetric_contDiff_one : ∀ i a b,
    ContDiff ℝ 1 (fun z ↦ inverseMetric i z a b)
  christoffel : Fin chartCount → E → Fin n → Fin n → Fin n → ℝ
  contractedChristoffel : Fin chartCount → E → Fin n → ℝ
  contractedChristoffel_eq : ∀ i (z : coordinateDomain i) k,
    contractedChristoffel i z k =
      -(∑ a : Fin n, ∑ b : Fin n,
        inverseMetric i z a b * christoffel i z k a b)
  density_inverseMetric_compatibility : ∀ i
      (z : coordinateDomain i) (j : Fin n),
    (∑ a : Fin n,
      fderiv ℝ (fun y ↦ weight i y * inverseMetric i y a j) z
        (EuclideanSpace.single a (1 : ℝ))) =
      weight i z * contractedChristoffel i z j
  intrinsicCoordinateLaplacian_eq : ∀ i
      (z : coordinateDomain i),
    g.laplacianAt
        (fun x : M ↦ partition i x * f x) (inverseChart i z) =
      christoffelCoordinateLaplacian
        (inverseMetric i) (christoffel i)
          (coordinateRepresentative i) z
  localizedLaplacian_aestronglyMeasurable : ∀ i,
    AEStronglyMeasurable
      (fun x : M ↦
        g.laplacianAt (fun y : M ↦ partition i y * f y) x)
      (volumeMeasure g)
```

### `Poincare/Global/HausdorffCoordinateDensityVariation.lean:82`

```lean
def HausdorffChartDensityEquality
    (g : ClosedSmoothRiemannianMetric n M)
    (U : Set (ClosedSmoothModel n)) (ψ : U → M) (V : Set M)
    (δ : U → ℝ) : Prop :=
  Measure.map ψ (rawHausdorffCoordinateDensityMeasure U δ) =
    (volumeMeasure g).restrict V
```

### `Poincare/Global/NormalizedFlow.lean:91`

```lean
structure IsClosedNormalizedRicciFlowSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop where
  leviCivita : ∀ t : ℝ,
    CovariantDerivative.IsLeviCivitaAt
      (fun y ↦ (gt t).inner y) (gt t).leviCivita x
  flow : ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField (n := n) (M := M) Z →
    ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
      (w : TM x),
      deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
        -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
          (2 / (n : ℝ)) * meanScalar (gt t₀) *
            (gt t₀).inner x (Z x) w
```

### `Poincare/RicciFlowEquation.lean:39`

```lean
def IsLeviCivitaAt (x : M) : Prop :=
  MetricCompatibleAt g cov x ∧ TorsionFreeAt cov x
```

### `Poincare/RiemannCurvatureOperator.lean:108`

```lean
def DerivRegularAt (Z : Π x : M, TangentSpace I x) (x : M) : Prop :=
  ∀ ⦃W : Π x : M, TangentSpace I x⦄, MDiffAt (T% W) x →
    MDiffAt (T% (fun y ↦ cov Z y (W y))) x
```

### `Poincare/Global/RicciFlow.lean:31`

```lean
abbrev ClosedC2TangentField
    (Z : ∀ y : M, TM y) : Prop :=
  ContMDiff I ((I).prod 𝓘(ℝ, E)) 2
    (fun y : M => (Z y : TotalSpace E TM))
```

### `Poincare/Global/MetricFlowJointRegularity.lean:198`

```lean
def MetricEntriesJointContDiffAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (k : ℕ∞ω) : Prop :=
  ∀ b c : TM x, ContDiffAt ℝ k (metricEntryJointChart gt x b c)
    (t₀, extChartAt Iₘ x x)
```

### `Poincare/Global/ClosedMetricThirdJetTopology.lean:38`

```lean
inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
  | value (x : M) (i j : ClosedSmoothModel n)
  | first (x : M) (u i j : ClosedSmoothModel n)
  | second (x : M) (u a i j : ClosedSmoothModel n)
  | third (x : M) (u a b i j : ClosedSmoothModel n)
```

### `Poincare/Global/ClosedMetricThirdJetTopology.lean:115`

```lean
noncomputable def metricEntryThirdJetProfile (g : G) :
    MetricEntryThirdJetProfileTarget n M
  | .value x i j => metricEntryThirdJetValueMap g x i j
  | .first x u i j => metricEntryThirdJetFirstMap g x u i j
  | .second x u a i j => metricEntryThirdJetSecondMap g x u a i j
  | .third x u a b i j => metricEntryThirdJetThirdMap g x u a b i j
```

### `Poincare/Global/RiemannianContext.lean:44`

```lean
abbrev ClosedSmoothRiemannianMetric (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M] :=
  ContMDiffRiemannianMetric (closedSmoothModelWithCorners n) ∞ (ClosedSmoothModel n)
    (fun x : M => TangentSpace (closedSmoothModelWithCorners n) x)
```

### `.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:244`

```lean
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))
```

### `.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:122`

```lean
structure SmoothPartitionOfUnity (s : Set M := univ) where
  /-- The family of functions forming the partition of unity. -/
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  /-- Around each point, there are only finitely many nonzero functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- All the functions in the partition of unity are nonnegative. -/
  nonneg' : ∀ i x, 0 ≤ toFun i x
  /-- The functions in the partition of unity add up to `1` at any point of `s`. -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- The functions in the partition of unity add up to at most `1` everywhere. -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1
```

## Appendix B. Supporting declaration and record probes

Source-verified supporting names and the exact constructor signatures were checked using the two programs below. Constructors are Lean-generated declarations of the source-verified structures, not additional manually written producers. A constructor accepting every field is not an unconditional existence theorem.

<!-- pieces-source-start -->
```lean
import Poincare
#check Poincare.HamiltonFrontInputs
#check Poincare.UniversalHamiltonFrontInputsStatement
#check Poincare.UniversalPositiveEinsteinStatement
#check Poincare.UniversalHamiltonConvergenceStatement
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.toMeasureAnalyticData3
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3
#check Poincare.CompactReferenceMetricTensorFamilyData
#check Poincare.CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison
#check Poincare.CompactReferenceMetricTensorFamilyData.uniformBallVolumeLower
#check Poincare.CompactFiniteAtlasChartFrameDensityData
#check Poincare.GlobalFiniteExtendedChartFrameDensityData
#check Poincare.FiniteExtendedChartFrameMeasureData
#check Poincare.FiniteExtendedChartFrameDensityDominationAt
#check Poincare.FiniteExtendedChartCover
#check Poincare.exists_finiteExtendedChartCover
#check Poincare.compactFiniteExtendedChartCover
#check Poincare.FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula
#check Poincare.FiniteExtendedChartCover.hausdorffChartDensityEquality
#check Poincare.FiniteExtendedChartCover.hasDerivAt_inverseChartDensity
#check Poincare.FiniteExtendedChartFrameMeasureData.ofDensityIntegrable
#check Poincare.GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
#check Poincare.FiniteSubordinateHausdorffLaplacianGeometry
#check Poincare.FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
#check Poincare.HausdorffChartDensityEquality
#check Poincare.IsClosedNormalizedRicciFlowSolutionAt
#check Poincare.MetricEntriesJointContDiffAt
#check Poincare.metricEntriesJointContDiffAt_const
#check Poincare.isClosedNormalizedRicciFlowSolutionAt_const_of_forall_isEinsteinAt
#check Poincare.MetricEntryThirdJetSlot
#check Poincare.metricEntryThirdJetProfile
#check Poincare.metricEntryThirdJetProfile_differentiable
#check Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise
#check Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded
#check Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_fderiv_bounded
#check Poincare.continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
#check Poincare.scalarAt_mdifferentiableAt
#check Poincare.hamiltonConvergencePinchedLimit3_iff_core
#check Poincare.hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3
#check Poincare.exists_normalizedRicciStationary_iff_positiveEinsteinMetric3
#check Poincare.RicciFlowShortTimeExistence3
#check Poincare.ricciFlowShortTimeExistence3_of_deTurck_of_pullback
#check Poincare.exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries
#check Bundle.ContMDiffRiemannianMetric
#check SmoothPartitionOfUnity
#check SmoothPartitionOfUnity.exists_isSubordinate
#check Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow
#check Poincare.timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
#check Poincare.ClosedC2TangentField
#check CovariantDerivative.IsLeviCivitaAt
#check CovariantDerivative.DerivRegularAt
#check Poincare.GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib
#check Poincare.normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseFDerivBoundedFormalMetricThirdJetProfilesOfCompactTensorControl
```
<!-- pieces-source-end -->

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-front-decomposition-evidence/pieces.lean > /tmp/hamilton-front-decomposition-evidence/pieces-03.log 2>&1
exit_code=0
```

Complete actual output:

```text
Poincare.HamiltonFrontInputs.{u, v} (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] : Type (max u (v + 1))
Poincare.UniversalHamiltonFrontInputsStatement.{u, v} : Prop
Poincare.UniversalPositiveEinsteinStatement.{u} : Prop
Poincare.UniversalHamiltonConvergenceStatement.{u} : Prop
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} (M : Type u) [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1))
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.toMeasureAnalyticData3.{u, v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3 M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3.{u, v} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3 M) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyAnalyticData3 M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.{u, v} (M : Type u) [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1))
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.toReactionDecayAnalyticData3.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (data : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3 M) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M
Poincare.CompactReferenceMetricTensorFamilyData.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] (K : Type v) [TopologicalSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) : Type (max u v)
Poincare.CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison.{u, v} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] {K : Type v} [TopologicalSpace K] [CompactSpace K]
  [Nonempty K] {metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M}
  (data : Poincare.CompactReferenceMetricTensorFamilyData K metric) :
  ∃ c, Poincare.UniformClosedRiemannianMetricLowerComparison data.referenceMetric metric c
Poincare.CompactReferenceMetricTensorFamilyData.uniformBallVolumeLower.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [Nonempty M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] {K : Type v} [TopologicalSpace K] [CompactSpace K]
  [Nonempty K] {metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M}
  (data : Poincare.CompactReferenceMetricTensorFamilyData K metric) :
  Poincare.UniformClosedRiemannianBallVolumeLower metric
Poincare.CompactFiniteAtlasChartFrameDensityData.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) : Type
Poincare.GlobalFiniteExtendedChartFrameDensityData.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) : Type
Poincare.FiniteExtendedChartFrameMeasureData.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (s : Set ℝ) : Prop
Poincare.FiniteExtendedChartFrameDensityDominationAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (s : Set ℝ) (t₀ : ℝ) :
  Type
Poincare.FiniteExtendedChartCover.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] : Type u
Poincare.exists_finiteExtendedChartCover.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] :
  Nonempty Poincare.FiniteExtendedChartCover
Poincare.compactFiniteExtendedChartCover.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] :
  Poincare.FiniteExtendedChartCover
Poincare.FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (C : Poincare.FiniteExtendedChartCover)
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  C.RestrictedInverseChartPullbackHausdorffAreaFormula g i
Poincare.FiniteExtendedChartCover.hausdorffChartDensityEquality.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (g : Poincare.ClosedSmoothRiemannianMetric n M) (i : Fin C.chartCount) :
  Poincare.HausdorffChartDensityEquality g (C.coordinateDomain i) (C.inverseChart i) (C.manifoldPiece i)
    (C.inverseChartDensity g i)
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
Poincare.GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (C : Poincare.FiniteExtendedChartCover) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (timeSet : ℝ → Set ℝ)
  (hDensity :
    ∀ (t τ : ℝ),
      τ ∈ timeSet t →
        ∀ (i : Fin C.chartCount),
          MeasureTheory.Integrable (C.inverseChartDensity (gt τ) i)
            (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i)))
  (hDomination : (t : ℝ) → Poincare.FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t) :
  Poincare.GlobalFiniteExtendedChartFrameDensityData C gt
Poincare.FiniteSubordinateHausdorffLaplacianGeometry.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (f : M → ℝ) : Type u
Poincare.FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {g : Poincare.ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
  (A : Poincare.FiniteSubordinateHausdorffLaplacianGeometry g f) : Poincare.ClosedLaplacianStokes g f
Poincare.HausdorffChartDensityEquality.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (U : Set (Poincare.ClosedSmoothModel n)) (ψ : ↑U → M) (V : Set M) (δ : ↑U → ℝ) : Prop
Poincare.IsClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (t₀ : ℝ) (x : M) : Prop
Poincare.MetricEntriesJointContDiffAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) (k : WithTop ℕ∞) : Prop
Poincare.metricEntriesJointContDiffAt_const.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (bg : Poincare.ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
  Poincare.MetricEntriesJointContDiffAt (fun x => bg) t₀ x 3
Poincare.isClosedNormalizedRicciFlowSolutionAt_const_of_forall_isEinsteinAt.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) {lam : ℝ} (hn : ↑n ≠ 0) (hEin : ∀ (y : M), g.IsEinsteinAt lam y)
  (hvol : (Poincare.volumeMeasure g) Set.univ ≠ 0) (t₀ : ℝ) (x : M) :
  Poincare.IsClosedNormalizedRicciFlowSolutionAt (fun x => g) t₀ x
Poincare.MetricEntryThirdJetSlot.{u} (n : ℕ) (M : Type u) : Type u
Poincare.metricEntryThirdJetProfile.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) : Poincare.MetricEntryThirdJetProfileTarget n M
Poincare.metricEntryThirdJetProfile_differentiable.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (slot : Poincare.MetricEntryThirdJetSlot n M) :
  Differentiable ℝ fun z => (Poincare.metricEntryThirdJetProfile g slot) z
Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise.{u, v} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {I : Type v}
  (gt : I → Poincare.ClosedSmoothRiemannianMetric n M)
  (hequicontinuous :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M),
      Equicontinuous fun t => ⇑(Poincare.metricEntryThirdJetProfile (gt t) slot))
  (hpointwiseCompact :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M) (z : Poincare.ClosedSmoothModel n),
      ∃ Q, IsCompact Q ∧ ∀ (t : I), (Poincare.metricEntryThirdJetProfile (gt t) slot) z ∈ Q) :
  IsCompact (closure (Set.range (Poincare.metricEntryThirdJetProfile ∘ gt)))
Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded.{u, v} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {I : Type v}
  (gt : I → Poincare.ClosedSmoothRiemannianMetric n M)
  (hequicontinuous :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M),
      Equicontinuous fun t => ⇑(Poincare.metricEntryThirdJetProfile (gt t) slot))
  (hpointwiseBounded :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M) (z : Poincare.ClosedSmoothModel n),
      Bornology.IsBounded (Set.range fun t => (Poincare.metricEntryThirdJetProfile (gt t) slot) z)) :
  IsCompact (closure (Set.range (Poincare.metricEntryThirdJetProfile ∘ gt)))
Poincare.isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_fderiv_bounded.{u, v} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {I : Type v}
  (gt : I → Poincare.ClosedSmoothRiemannianMetric n M)
  (hfderivBounded :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M),
      ∃ C,
        ∀ (t : I) (z : Poincare.ClosedSmoothModel n),
          ‖fderiv ℝ (fun w => (Poincare.metricEntryThirdJetProfile (gt t) slot) w) z‖₊ ≤ C)
  (hzeroBounded :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M),
      Bornology.IsBounded (Set.range fun t => (Poincare.metricEntryThirdJetProfile (gt t) slot) 0)) :
  IsCompact (closure (Set.range (Poincare.metricEntryThirdJetProfile ∘ gt)))
Poincare.continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  {K : Type v} [TopologicalSpace K] [Nonempty M] (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hMeasure : Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k))
  (hScalar : Continuous fun p => (metric p.1).scalarAt p.2)
  (hTracelessRicci : Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2) :
  Continuous fun k => Poincare.closedMetricMeanTracelessEnergyPair (metric k)
Poincare.scalarAt_mdifferentiableAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) (x : M) : (MDiffAt fun y => g.scalarAt y) x
Poincare.hamiltonConvergencePinchedLimit3_iff_core.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] :
  Poincare.HamiltonConvergencePinchedLimit3 M ↔ Poincare.HamiltonConvergencePinchedLimit3Core M
Poincare.hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3.{u} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] : Poincare.HamiltonConvergencePinchedLimit3Core M ↔ Poincare.PositiveEinsteinMetric3 M
Poincare.exists_normalizedRicciStationary_iff_positiveEinsteinMetric3.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [SimplyConnectedSpace M] :
  (∃ g, Poincare.IsClosedNormalizedRicciStationary g ∧ 0 < Poincare.meanScalar g) ↔ Poincare.PositiveEinsteinMetric3 M
Poincare.RicciFlowShortTimeExistence3.{u} (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
Poincare.ricciFlowShortTimeExistence3_of_deTurck_of_pullback.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (hDeTurck : Poincare.RicciDeTurckShortTimeExistence3 M)
  (hPullback : Poincare.DeTurckPullbackToRicciFlow3 M) : Poincare.RicciFlowShortTimeExistence3 M
Poincare.exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries.{u, u_1, u_2} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {ι : Type u_1} {κ : Type u_2}
  (D : M → Poincare.RecenteredDeTurckShapedBUCRemainderData ι κ) (K : M → NNReal)
  (u₀ : (y : M) → Poincare.SemilinearBUCBoundedData (K y)) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M)
  (bg : Poincare.ClosedSmoothRiemannianMetric n M) (t : ℝ) (ht₀ : 0 < t)
  (htT :
    ∀ (y : M),
      t < ↑((Poincare.AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground (D y)).uniformLifespan (K y)))
  (hfullGerm :
    ∀ (y : M),
      (fun z' =>
          Poincare.coordinateBilinearFormAt
            ((Poincare.AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground (D y)).uniformInteriorState
                (K y) (u₀ y) t +
              (D y).background)
            z') =ᶠ[nhds (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y)]
        CovariantDerivative.chartMetric (gt t).inner y)
  (hbackgroundGerm :
    ∀ (y : M),
      (fun z' =>
          Poincare.coordinateBilinearFormAt (D y).background
            z') =ᶠ[nhds (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y)]
        CovariantDerivative.chartMetric bg.inner y)
  (hremainder :
    ∀ (y : M) (v w : Poincare.ClosedSmoothModel n),
      Poincare.coordinateMetricValue
          ((D y).base.nonlinearity
            ((Poincare.AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground (D y)).uniformInteriorState
                (K y) (u₀ y) t +
              (D y).background))
          (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y) v w =
        ((Poincare.deTurckChartMetricEvolutionBilin gt bg y t
                  (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y))
                v)
              w -
            Poincare.coordinateMetricLaplacianValue
              ((Poincare.AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground (D y)).uniformInteriorState
                  (K y) (u₀ y) t +
                (D y).background)
              (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y) v w +
          Poincare.coordinateMetricLaplacianValue (D y).background
            (↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y) v w)
  (hJoint : ∀ (y : M), Poincare.MetricEntriesJointContDiffAt gt t y 3) :
  ∃ phi J curv,
    (∀ (y : M), phi y t = ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) y) y) ∧
      (∀ (y : M), J y t = ContinuousLinearMap.id ℝ (Poincare.ClosedSmoothModel n)) ∧
        ∀ (y : M),
          Poincare.IsCoordinateRicciFlowAt (Poincare.reconstructedInverseGaugeMetric (D y) (K y) (u₀ y) (phi y) (J y))
            (curv y) t
Bundle.ContMDiffRiemannianMetric.{u_1, u_2, u_3, u_4, u_5} {EB : Type u_1} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type u_2} [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) (n : WithTop ℕ∞) {B : Type u_3}
  [TopologicalSpace B] [ChartedSpace HB B] (F : Type u_4) [NormedAddCommGroup F] [NormedSpace ℝ F] (E : B → Type u_5)
  [TopologicalSpace (Bundle.TotalSpace F E)] [(b : B) → TopologicalSpace (E b)] [(b : B) → AddCommGroup (E b)]
  [(b : B) → Module ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E] : Type (max u_3 u_5)
SmoothPartitionOfUnity.{uι, uE, uH, uM} (ι : Type uι) {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
  (s : Set M := Set.univ) : Type (max uM uι)
SmoothPartitionOfUnity.exists_isSubordinate.{uι, uE, uH, uM} {ι : Type uι} {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I (↑⊤) M] [T2Space M] [SigmaCompactSpace M] {s : Set M}
  (hs : IsClosed s) (U : ι → Set M) (ho : ∀ (i : ι), IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f, f.IsSubordinate U
Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} (hFlow : ∀ (y : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
  (hEntries : ∀ (y : M), Poincare.TimeVariationExtContMDiffAt gt t₀ y 2) (x : M) :
  ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt t₀).scalarAt y) x
Poincare.timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} (hJoint : Poincare.MetricEntriesJointContDiffAt gt t₀ x 3) :
  Poincare.TimeVariationExtContMDiffAt gt t₀ x 2
Poincare.ClosedC2TangentField.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  (Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y) : Prop
CovariantDerivative.IsLeviCivitaAt.{u_1, u_2, u_3} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_2} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [TopologicalSpace M]
  [ChartedSpace H M] (g : (y : M) → TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) [IsManifold I 1 M]
  (cov : CovariantDerivative I E (TangentSpace I)) (x : M) : Prop
CovariantDerivative.DerivRegularAt.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (cov : CovariantDerivative I E (TangentSpace I)) (Z : (x : M) → TangentSpace I x) (x : M) : Prop
Poincare.GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [Nonempty M]
  (g : Poincare.ClosedSmoothRiemannianMetric n M) : (Poincare.volumeMeasure g) Set.univ ≠ 0
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
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (reaction : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M)
  (compactTensorReferenceControl : Poincare.CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
  (hequicontinuous :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Equicontinuous fun t => ⇑(Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot))
  (hpointwiseCompact :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M) (z : Poincare.ClosedSmoothModel 3),
      ∃ Q, IsCompact Q ∧ ∀ (t : ↑(Set.Ici 0)), (Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot) z ∈ Q)
  (scalarSubordinateGeometry :
    (t : ↑(Set.Ici 0)) →
      Poincare.FiniteSubordinateHausdorffLaplacianGeometry (reaction.gt ↑t) fun y => (reaction.gt ↑t).scalarAt y) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3 M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseFDerivBoundedFormalMetricThirdJetProfilesOfCompactTensorControl.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (reaction : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M)
  (compactTensorReferenceControl : Poincare.CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
  (hfderivBounded :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      ∃ C,
        ∀ (t : ↑(Set.Ici 0)) (z : Poincare.ClosedSmoothModel 3),
          ‖fderiv ℝ (fun w => (Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot) w) z‖₊ ≤ C)
  (hzeroBounded :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Bornology.IsBounded (Set.range fun t => (Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot) 0))
  (scalarSubordinateGeometry :
    (t : ↑(Set.Ici 0)) →
      Poincare.FiniteSubordinateHausdorffLaplacianGeometry (reaction.gt ↑t) fun y => (reaction.gt ↑t).scalarAt y) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3 M
```

<!-- records-source-start -->
```lean
import Poincare
#check Poincare.HamiltonFrontInputs.mk
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.mk
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.mk
#check Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.mk
#check Poincare.CompactReferenceMetricTensorFamilyData.mk
#check Poincare.FiniteExtendedChartCover.mk
#check Poincare.GlobalFiniteExtendedChartFrameDensityData.mk
#check Poincare.FiniteExtendedChartFrameMeasureData.mk
#check Poincare.FiniteExtendedChartFrameDensityDominationAt.mk
#check Poincare.FiniteSubordinateHausdorffLaplacianGeometry.mk
#check Poincare.IsClosedNormalizedRicciFlowSolutionAt.mk
#check Bundle.ContMDiffRiemannianMetric.mk
#check SmoothPartitionOfUnity.mk
```
<!-- records-source-end -->

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-front-decomposition-evidence/records.lean > /tmp/hamilton-front-decomposition-evidence/records-01.log 2>&1
exit_code=0
```

Complete actual output:

```text
Poincare.HamiltonFrontInputs.mk.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M]
  (reaction : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M)
  (compactTensorReferenceControl : Poincare.CompactReferenceMetricTensorFamilyData reaction.K reaction.metric)
  (hequicontinuous :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Equicontinuous fun t => ⇑(Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot))
  (hpointwiseCompact :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M) (z : Poincare.ClosedSmoothModel 3),
      ∃ Q, IsCompact Q ∧ ∀ (t : ↑(Set.Ici 0)), (Poincare.metricEntryThirdJetProfile (reaction.gt ↑t) slot) z ∈ Q)
  (scalarSubordinateGeometry :
    (t : ↑(Set.Ici 0)) →
      Poincare.FiniteSubordinateHausdorffLaplacianGeometry (reaction.gt ↑t) fun y => (reaction.gt ↑t).scalarAt y) :
  Poincare.HamiltonFrontInputs M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.mk.{u, v} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (K : Type v) (topologicalSpaceK : TopologicalSpace K)
  (compactSpaceK : CompactSpace K) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Set.Ici 0) → K)
  (parameterContinuous : Continuous parameter) (realizesFlow : ∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t)
  (meanScalarFloor : ℝ) (meanScalarFloor_pos : 0 < meanScalarFloor)
  (meanScalarLower : ∀ (t : ↑(Set.Ici 0)), meanScalarFloor ≤ Poincare.meanScalar (gt ↑t))
  (normalizedFlow : ∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (compactFiniteAtlasChartFrameDensityData : Poincare.CompactFiniteAtlasChartFrameDensityData gt)
  (jointMetricEntries : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) (reactionDecayRate : ℝ)
  (reactionDecayRate_pos : 0 < reactionDecayRate)
  (actualReactionDomination :
    ∀ t ∈ Set.Ici 0,
      ∀ (x : M),
        Poincare.normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
          -reactionDecayRate * (gt t).tracelessRicciNormSqAt x)
  (finiteVolumeMeasureContinuous : Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k))
  (scalarJointContinuous : Continuous fun p => (metric p.1).scalarAt p.2)
  (tracelessRicciNormSqJointContinuous : Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3 M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3.mk.{u, v} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (K : Type v) (topologicalSpaceK : TopologicalSpace K)
  (compactSpaceK : CompactSpace K) (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Set.Ici 0) → K)
  (parameterContinuous : Continuous parameter) (realizesFlow : ∀ (t : ↑(Set.Ici 0)), metric (parameter t) = gt ↑t)
  (meanScalarFloor : ℝ) (meanScalarFloor_pos : 0 < meanScalarFloor)
  (meanScalarLower : ∀ (t : ↑(Set.Ici 0)), meanScalarFloor ≤ Poincare.meanScalar (gt ↑t))
  (normalizedFlow : ∀ t ∈ Set.Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (compactFiniteAtlasChartFrameDensityData : Poincare.CompactFiniteAtlasChartFrameDensityData gt)
  (jointMetricEntries : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) (pinchingEpsilon : ℝ)
  (pinchingEpsilon_pos : 0 < pinchingEpsilon) (pinchingEpsilon_le_one_third : pinchingEpsilon ≤ 1 / 3)
  (pinchingDelta : ℝ) (pinchingDelta_nonneg : 0 ≤ pinchingDelta) (pinchingDelta_le_two : pinchingDelta ≤ 2)
  (pinchingDelta_admissible : pinchingDelta ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 pinchingEpsilon)
  (scalarPositive : ∀ t ∈ Set.Ici 0, ∀ (x : M), 0 < (gt t).scalarAt x)
  (ricciEigenvalueFloor : ∀ t ∈ Set.Ici 0, Poincare.GlobalRicciEigenvalueFloor3 (gt t) pinchingEpsilon)
  (finiteVolumeMeasureContinuous : Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k))
  (scalarJointContinuous : Continuous fun p => (metric p.1).scalarAt p.2)
  (tracelessRicciNormSqJointContinuous : Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3 M
Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3.mk.{u, v} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (pinching : Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingCoreData3 M)
  (pinchingCoefficientGap_pos : 0 < pinching.pinchingCoefficientGap) :
  Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureHamiltonPinchingDecayAnalyticData3 M
Poincare.CompactReferenceMetricTensorFamilyData.mk.{u, v} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] {K : Type v} [TopologicalSpace K]
  {metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M} (referenceMetric : Poincare.ClosedSmoothRiemannianMetric 3 M)
  (metricFactor volumeFactor : K → ℝ) (metricFactor_continuous : Continuous metricFactor)
  (volumeFactor_continuous : Continuous volumeFactor) (metricFactor_pos : ∀ (k : K), 0 < metricFactor k)
  (volumeFactor_pos : ∀ (k : K), 0 < volumeFactor k)
  (metric_le :
    ∀ (k : K) (x : M) (w : TangentSpace (Poincare.closedSmoothModelWithCorners 3) x),
      (((metric k).inner x) w) w ≤ metricFactor k ^ 2 * ((referenceMetric.inner x) w) w)
  (volume_le :
    ∀ (k : K) (A : Set M),
      MeasurableSet A →
        volumeFactor k * (Poincare.volumeMeasure referenceMetric).real A ≤ (Poincare.volumeMeasure (metric k)).real A) :
  Poincare.CompactReferenceMetricTensorFamilyData K metric
Poincare.FiniteExtendedChartCover.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] (chartCount : ℕ) (anchor : Fin chartCount → M)
  (sources_cover : ⋃ i, (extChartAt (Poincare.closedSmoothModelWithCorners n) (anchor i)).source = Set.univ) :
  Poincare.FiniteExtendedChartCover
Poincare.GlobalFiniteExtendedChartFrameDensityData.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {C : Poincare.FiniteExtendedChartCover} {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} (timeSet : ℝ → Set ℝ)
  (measureData : ∀ (t : ℝ), Poincare.FiniteExtendedChartFrameMeasureData C gt (timeSet t))
  (domination : (t : ℝ) → Poincare.FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t) :
  Poincare.GlobalFiniteExtendedChartFrameDensityData C gt
Poincare.FiniteExtendedChartFrameMeasureData.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {C : Poincare.FiniteExtendedChartCover} {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
  (density_integrable :
    ∀ t ∈ s,
      ∀ (i : Fin C.chartCount),
        MeasureTheory.Integrable (C.inverseChartDensity (gt t) i)
          (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i)))
  (areaFormula : ∀ t ∈ s, ∀ (i : Fin C.chartCount), C.RestrictedInverseChartPullbackHausdorffAreaFormula (gt t) i) :
  Poincare.FiniteExtendedChartFrameMeasureData C gt s
Poincare.FiniteExtendedChartFrameDensityDominationAt.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
  {C : Poincare.FiniteExtendedChartCover} {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {s : Set ℝ} {t₀ : ℝ}
  (timeSet_mem : s ∈ nhds t₀)
  (densityDerivative_aestronglyMeasurable_at :
    ∀ (i : Fin C.chartCount),
      MeasureTheory.AEStronglyMeasurable (Poincare.finiteExtendedChartFrameDensityDerivative C gt t₀ i)
        (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i)))
  (dominatingFunction : (i : Fin C.chartCount) → ↑(C.coordinateDomain i) → ℝ)
  (dominatingFunction_integrable :
    ∀ (i : Fin C.chartCount),
      MeasureTheory.Integrable (dominatingFunction i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i)))
  (densityDerivative_bound :
    ∀ (i : Fin C.chartCount),
      ∀ᵐ (z : ↑(C.coordinateDomain i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
        ∀ t ∈ s, ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt t i z‖ ≤ dominatingFunction i z)
  (timeDifferentiable :
    ∀ (i : Fin C.chartCount) (z : ↑(C.coordinateDomain i)),
      ∀ t ∈ s, Poincare.TimeDifferentiableAt gt t (C.inverseChart i z)) :
  Poincare.FiniteExtendedChartFrameDensityDominationAt C gt s t₀
Poincare.FiniteSubordinateHausdorffLaplacianGeometry.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {g : Poincare.ClosedSmoothRiemannianMetric n M}
  {f : M → ℝ} (chartCount : ℕ) (coordinateDomain : Fin chartCount → Set (Poincare.ClosedSmoothModel n))
  (coordinateDomain_measurable : ∀ (i : Fin chartCount), MeasurableSet (coordinateDomain i))
  (inverseChart : (i : Fin chartCount) → ↑(coordinateDomain i) → M)
  (inverseChart_measurable : ∀ (i : Fin chartCount), Measurable (inverseChart i)) (chartRegion : Fin chartCount → Set M)
  (chartRegion_isOpen : ∀ (i : Fin chartCount), IsOpen (chartRegion i))
  (density : (i : Fin chartCount) → ↑(coordinateDomain i) → ℝ)
  (density_nonneg : ∀ (i : Fin chartCount), 0 ≤ᵐ[Poincare.coordinateLebesgueMeasure (coordinateDomain i)] density i)
  (density_integrable :
    ∀ (i : Fin chartCount),
      MeasureTheory.Integrable (density i) (Poincare.coordinateLebesgueMeasure (coordinateDomain i)))
  (chartMeasure :
    ∀ (i : Fin chartCount),
      Poincare.HausdorffChartDensityEquality g (coordinateDomain i) (inverseChart i) (chartRegion i) (density i))
  (partition : SmoothPartitionOfUnity (Fin chartCount) (Poincare.closedSmoothModelWithCorners n) M)
  (partition_subordinate : partition.IsSubordinate chartRegion)
  (f_contMDiff_two : ContMDiff (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 f)
  (coordinateRepresentative : Fin chartCount → Poincare.ClosedSmoothModel n → ℝ)
  (coordinateRepresentative_eq :
    ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
      coordinateRepresentative i ↑z = (partition i) (inverseChart i z) * f (inverseChart i z))
  (coordinateRepresentative_contDiff_two : ∀ (i : Fin chartCount), ContDiff ℝ 2 (coordinateRepresentative i))
  (coordinateRepresentative_hasCompactSupport : ∀ (i : Fin chartCount), HasCompactSupport (coordinateRepresentative i))
  (coordinateRepresentative_tsupport_subset_coordinateDomain :
    ∀ (i : Fin chartCount), tsupport (coordinateRepresentative i) ⊆ coordinateDomain i)
  (weight : Fin chartCount → Poincare.ClosedSmoothModel n → ℝ)
  (weight_contDiff_one : ∀ (i : Fin chartCount), ContDiff ℝ 1 (weight i))
  (weight_eq_density :
    ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
      weight i ↑z = ↑(Poincare.rawHausdorffLebesgueScale n) * density i z)
  (inverseMetric : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → Fin n → ℝ)
  (inverseMetric_contDiff_one : ∀ (i : Fin chartCount) (a b : Fin n), ContDiff ℝ 1 fun z => inverseMetric i z a b)
  (christoffel : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → Fin n → Fin n → ℝ)
  (contractedChristoffel : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → ℝ)
  (contractedChristoffel_eq :
    ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)) (k : Fin n),
      contractedChristoffel i (↑z) k = -∑ a, ∑ b, inverseMetric i (↑z) a b * christoffel i (↑z) k a b)
  (density_inverseMetric_compatibility :
    ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)) (j : Fin n),
      ∑ a, (fderiv ℝ (fun y => weight i y * inverseMetric i y a j) ↑z) (EuclideanSpace.single a 1) =
        weight i ↑z * contractedChristoffel i (↑z) j)
  (intrinsicCoordinateLaplacian_eq :
    ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
      g.laplacianAt (fun x => (partition i) x * f x) (inverseChart i z) =
        Poincare.christoffelCoordinateLaplacian (inverseMetric i) (christoffel i) (coordinateRepresentative i) ↑z)
  (localizedLaplacian_aestronglyMeasurable :
    ∀ (i : Fin chartCount),
      MeasureTheory.AEStronglyMeasurable (fun x => g.laplacianAt (fun y => (partition i) y * f y) x)
        (Poincare.volumeMeasure g)) :
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry g f
Poincare.IsClosedNormalizedRicciFlowSolutionAt.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M}
  (leviCivita : ∀ (t : ℝ), CovariantDerivative.IsLeviCivitaAt (fun y => (gt t).inner y) (gt t).leviCivita x)
  (flow :
    ∀ {Z : (y : M) → TangentSpace (Poincare.closedSmoothModelWithCorners n) y},
      Poincare.ClosedC2TangentField Z →
        ∀ (hreg : (gt t₀).leviCivita.DerivRegularAt Z x) (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
          deriv (fun t => (((gt t).inner x) (Z x)) w) t₀ =
            -2 * (gt t₀).leviCivita.ricciTraceAt hreg w +
              2 / ↑n * Poincare.meanScalar (gt t₀) * (((gt t₀).inner x) (Z x)) w) :
  Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x
Bundle.ContMDiffRiemannianMetric.mk.{u_1, u_2, u_3, u_4, u_5} {EB : Type u_1} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type u_2} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞} {B : Type u_3}
  [TopologicalSpace B] [ChartedSpace HB B] {F : Type u_4} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type u_5}
  [TopologicalSpace (Bundle.TotalSpace F E)] [(b : B) → TopologicalSpace (E b)] [(b : B) → AddCommGroup (E b)]
  [(b : B) → Module ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E] (inner : (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ)
  (symm : ∀ (b : B) (v w : E b), ((inner b) v) w = ((inner b) w) v)
  (pos : ∀ (b : B) (v : E b), v ≠ 0 → 0 < ((inner b) v) v)
  (isVonNBounded : ∀ (b : B), Bornology.IsVonNBounded ℝ {v | ((inner b) v) v < 1})
  (contMDiff : ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (F →L[ℝ] F →L[ℝ] ℝ))) n fun b => ⟨b, inner b⟩) :
  Bundle.ContMDiffRiemannianMetric IB n F E
SmoothPartitionOfUnity.mk.{uι, uE, uH, uM} {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {s : optParam (Set M) Set.univ} (toFun : ι → ContMDiffMap I (modelWithCornersSelf ℝ ℝ) M ℝ ↑⊤)
  (locallyFinite' : LocallyFinite fun i => Function.support ⇑(toFun i)) (nonneg' : ∀ (i : ι) (x : M), 0 ≤ (toFun i) x)
  (sum_eq_one' : ∀ x ∈ s, ∑ᶠ (i : ι), (toFun i) x = 1) (sum_le_one' : ∀ (x : M), ∑ᶠ (i : ι), (toFun i) x ≤ 1) :
  SmoothPartitionOfUnity ι I M s
```

The first two supporting probes failed on the unqualified Mathlib metric name. Its source namespace is `Bundle`; the final spelling above passes. Actual failed diagnostic, before correction:

```text
/tmp/hamilton-front-decomposition-evidence/pieces.lean:47:7: error(lean.unknownIdentifier): Unknown identifier `ContMDiffRiemannianMetric`
```

The failed logs are retained as `pieces-01.log` and `pieces-02.log`; successful declarations around that diagnostic have the same signatures shown above. No repository source was edited to fix the probe.

