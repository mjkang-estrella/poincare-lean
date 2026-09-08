# Ricci-flow existence interface survey

Date: 2026-09-08. Base commit: `5a3dab3991e9e09d01a2f60957aa16b1110f0277`.

> Orchestrator note (2026-09-08): this landed copy keeps sections 1-4, the verification section, and Appendix D (the proposed goal program) from the worker report (lines 1-480 and 3734-4067). Appendices A-C and E-G (source inventories, existential-theorem probe, source searches, Mathlib probe, failed attempts) stay unmerged on branch `worker/ricci-flow-existence-interface-survey` at its head commit because of their size.

Branch: `worker/ricci-flow-existence-interface-survey`.
Result: survey done. No short-time existence theorem is proved by this report.

The missing core is a **variable-coefficient quasilinear parabolic existence and regularity theorem**, with a compatible global construction and control at the initial time. The repository already has genuine Euclidean heat solutions, BUC semilinear fixed points, local inverse-gauge ODEs, curvature pullback identities, and conditional global metric assembly. These are substantial results. They do not instantiate short-time Ricci flow for an arbitrary initial closed metric.

A small next task is available: uniform coercivity of a continuous positive bilinear coefficient on a compact parameter set. Its exact target elaborates in Appendix D. It provides an ellipticity constant; it does not discharge the parabolic existence core. The first missing PDE estimate is the variable-coefficient, zero-initial-data parabolic Schauder solvability estimate specified in task 3.

The worktree was clean at the recorded base. I read the task file, the top of `HANDOFF.md`, `README.md`, `docs/PROJECT_MAP.md`, the requested reports, plan-3, the two Hamilton mission files, and the relevant definitions and imports. The requested module search returned 93 files. Appendix A records that set; their imports, module documentation and declaration surfaces were reviewed, with the relevant definitions and proof routes inspected in detail. Historical comments were checked against later consumers. In particular, the old frontier report predates the current DeTurck and recognition results.

The task-specific report-only contract governs this job. No repository Lean file, frozen contract, root import, audit, mission, ledger, or `HANDOFF.md` was edited. Scratch `.lean` probes live under `/tmp`, as explicitly requested. There is no proof-source deliverable, so no separate lemma commits. This report is not an acceptance or merge decision.

Evidence conventions:

- **Repo, proved** means an existing declaration whose source was found and whose type was checked in the current cache. A proved implication with an analytic hypothesis remains conditional.
- **Repo, interface** means a defined proposition or record, not an inhabitant constructed for every initial metric.
- **Mathlib** means the pinned tree at `7175569c842f9164564bd76ff8b207e7b4705522`, with toolchain `leanprover/lean4:v4.30.0-rc2`.
- **Absent** means no theorem implementing the stated mathematical content was found in the recorded source searches. It is not a proof that no logically equivalent theorem exists under another name. Names of legacy records are not evidence that their corresponding PDE theory exists.
- Names in namespace `RicciExistenceSurvey` and new module paths in the plan are proposals, not landed declarations. Appendix D checks their types, not the truth of the open goals. The two anonymous examples only verify already-landed bookkeeping.
- Appendices B and C contain the complete printed hypotheses of the inventory, including ambient instances, and constructors of the important premise records. Proof terms printed as `⋯` are omitted proof arguments, not omitted hypotheses. Expansion stops at standard foundational types and explicitly named subordinate records.

## 1. Landed existence interfaces and what they actually require

### 1.1 Closed-flow and DeTurck statement interfaces

The shared three-dimensional context is a type `M`, topology, Hausdorff and second-countable instances, charts modeled on `ClosedSmoothModel 3`, a smooth boundaryless manifold instance, compactness, connectedness and simple connectivity. These last topology assumptions are stronger than classical short-time existence needs; they belong to the existing interface and are retained here.

| Declaration and source | Exact content and status |
| --- | --- |
| `RicciFlowShortTimeExistence3`, `Global/ShortTimeInterface.lean:43` | Interface: for every `g₀ : ClosedSmoothRiemannianMetric 3 M`, there are `T > 0` and a total family `gt : ℝ → ClosedSmoothRiemannianMetric 3 M`, with `gt 0 = g₀` and `IsClosedRicciFlowSolutionAt gt t x` for every `t ∈ Ico 0 T` and every `x`. No unconditional producer was found. |
| `IsClosedRicciFlowSolutionAt`, `Global/RicciFlow.lean:39` | Definition reducing to `CovariantDerivative.IsRicciFlowSolutionAt` for the metric's actual canonical connection. The constructor requires Levi-Civita at each real time and the section-tested derivative equation at the active time. `isClosedRicciFlowSolutionAt_of_metric` proves the Levi-Civita part from each smooth metric; its remaining hypothesis is the actual section-tested equation. |
| `RicciDeTurckShortTimeExistence3`, `Global/DeTurck.lean:156` | Same initial metric and interval quantifiers, plus an existential tangent-field family `Wt`. Every active slice satisfies `IsClosedRicciDeTurckSolutionAt gt Wt t x`. That record adds `ClosedC2TangentField (Wt t)` and the Lie derivative to the flow equation. It does **not** identify `Wt` with the canonical DeTurck field of a background. |
| `DeTurckPullbackToRicciFlow3`, `Global/DeTurck.lean:174` | For every `g₀`, every `T`, `gt`, `Wt`, positive `T`, initial equality, and the preceding DeTurck equation on `Ico 0 T`, produce a Ricci-flow family on that **same** interval with that initial metric. It contains no actual diffeomorphism field and no joint regularity hypothesis. No producer of this full proposition was found. |
| `ricciFlowShortTimeExistence3_of_deTurck_of_pullback`, `Global/DeTurck.lean:196` | Repo, proved. Its only additional hypotheses are `RicciDeTurckShortTimeExistence3 M` and `DeTurckPullbackToRicciFlow3 M`. It chooses the first solution, applies the second interface and returns the witnesses. Neither analytic premise is discharged. |
| `IsDeTurckGaugedFlowAt`, `Global/DeTurckField.lean` | The concrete field variant uses `deTurckVectorField gt bg`, with a supplied fixed background metric. `isDeTurckGaugedFlowAt_of_equations` discharges the field's C2 regularity by `deTurckVectorFieldRegularAt_holds`. It still assumes the evolution equation. |
| `IsClosedNormalizedRicciFlowSolutionAt`, `Global/NormalizedFlow.lean:91` | Levi-Civita plus `deriv g = -2 Ric + (2/n) meanScalar(g) g`. It additionally needs compactness, connectedness and a compatible Borel measure structure. There is no general normalized short-time producer found. |

The full quantified expressions are printed in Appendix B, and the smallest per-metric payload is displayed in section 4.

Two source-level qualifications matter:

1. The short-time interface's comment says `(0,T)`, but its actual set is `Ico 0 T`, meaning **[0,T)**. Its time derivative is ordinary `deriv`, including at zero. Positive-interior or right-sided results alone cannot fill it. A constant extension to negative time generally gives the wrong derivative at zero. One needs a compatible extension of the metric family, not a backward Ricci-flow solution. No change to the frozen/existing target is proposed.
2. The predicates equate a total derivative operation to a tensor but do not themselves supply `HasDerivAt` or joint regularity. Even the generic DeTurck interface only demands C2 field regularity separately at active times. A standard smooth gauge-ODE theorem needs more than those hypotheses. Task 8 uses an explicitly stronger concrete-field input and allows shrinking the interval. It does not claim to prove the broader same-interval pullback interface.

`exists_shortTime_ricciFlow_of_interface` is extraction from the supplied interface. `exists_shortTime_flow_half_of_hamiltonScalarEvolution_input` adds the flow-only spatial neighborhood fact, using the equation at every point. Neither produces the independent regularity conditions needed for scalar evolution. `static_ricciFlat_flowClause` requires that the actual Ricci trace vanish for every admissible C2 test field and every regularity witness and tangent slot; it is a special-case solution, not an arbitrary-metric existence proof.

### 1.2 Euclidean BUC existence and reconstruction

Appendix B checks the following substantial proved routes and the full record constructors.

- `AffineRecenteredDeTurckShapedBUCRemainderData.exists_single_time_fixedPoints` gives one positive lifespan for all BUC initial data in a prescribed norm ball. Its data is an assembled bounded linear/quadratic/composition nonlinearity and constant forcing. The norm ball, finite-dimensional target and nonlinearity controls are actual hypotheses.
- `AffineRecenteredDeTurckShapedBUCRemainderData.exists_positive_reconstructedMetricCoefficient_evolution` adds a uniformly positive background, symmetry preservation, a suitable small initial-data bound, and a heat-generator witness for the initial perturbation. It produces a positive coordinate coefficient and its **right-sided** initial evolution. It does not produce a smooth global metric.
- `semilinearHeatBUCUniformLocalSolution_hasDerivAt_interior` supplies an ordinary Banach-valued derivative at strictly positive interior times from the semilinear local-data package. `coordinateMetricValue_generator_eq_laplacian_of_contDiffAt_two` identifies the generator pointwise from a local C2 germ; the older global-classical-core requirement has been reduced by this later theorem.
- `vectorHeatSolution_solves_heatEquation_of_bounded_measurable` is genuine finite-dimensional vector-valued Euclidean heat analysis. Its ambient domain is a finite-dimensional inner-product vector space, not an arbitrary closed manifold.

The critical distinction is the type of `SemilinearHeatBUCLocalData`: continuity of `N : BUC → BUC`, a finite growth bound on every norm ball, and a finite Lipschitz constant on each such ball. The BUC norm controls values, not first or second derivatives.

For the actual Ricci–DeTurck equation the principal term is `g^{ab} ∂a∂b g`. Subtracting a flat Laplacian leaves `(g^{ab} - δ^{ab}) ∂a∂b g` as well as terms in first derivatives. This is a derivative-losing expression in the plain BUC norm. Smooth oscillatory functions can have arbitrarily small value norm with large second derivative. Thus there is no justified route from arbitrary smooth metric coefficients to the currently supplied bounded-ball BUC remainder record merely by expanding the coordinate formula. The checked coefficient identity still leaves that identification as `hremainder`. This is a mathematical type/estimate obstruction, not just a missing constructor name.

### 1.3 Pointwise inverse-gauge existence, with all premises exposed

There is exactly **one** source declaration matching `exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_*` in the requested search, namely
`exists_pointwise_reconstructedInverseGaugeRicciFlowData_of_metricEntries`, in `Global/DeTurckBUCInteriorGlobalRicciData.lean:40`.

Its full source signature and checked type are in Appendices A and B. It works in general dimension `n` with a Hausdorff smooth manifold, without compactness or simple connectivity. The premises are:

1. For **every point** `y`, a recentered BUC remainder datum `D y`, norm bound `K y`, and bounded initial perturbation `u₀ y`.
2. An already supplied global smooth metric family `gt`, a smooth background `bg`, and one time `t > 0` less than **every** selected lifespan.
3. For every `y`, the full reconstructed coefficient agrees as a spatial germ at its self-chart center with the chart metric of `gt t`; the background coefficient agrees there with the chart metric of `bg`.
4. For every `y` and tangent-coordinate slots, the actual BUC nonlinearity equals the actual DeTurck chart rate minus the full coefficient's flat Laplacian plus the background's flat Laplacian.
5. `MetricEntriesJointContDiffAt gt t y 3` for every `y`.

Its conclusion selects point-indexed trajectories `phi`, differentials `J`, and curvature endomorphism rates. At each point the trajectory starts at that self-chart center at time `t`, its differential starts at the identity, and the reconstructed pullback has a genuine two-sided **coordinate** Ricci equation at that restart time. The proof uses the corresponding self-chart interior theorem and dependent choice.

What is proved is local analytic reconstruction and simultaneous choice **from these inputs**. What is not proved is the construction of `D`, its geometric remainder identification, the global `gt` with the required germs/regularity, a positive infimum of all pointwise lifespans, or a single physical gauge starting at the original initial time. Independently restarting at every point and time does not supply that physical gauge.

Appendix C inventories all 52 `exists_*` declarations found in the 91 matched modules other than the two large legacy/model files. This includes the initial one-sided, generator-domain, interior, point-flow variational, symmetric-time, physical-time, local-diffeomorphism, metric-assembly and conditional continuation variants. Every one has a source index and passing `#check @...`; none of these is silently counted as an unconditional closed-flow producer.

### 1.4 Gluing and pullback: proved edges versus unproduced inputs

| Proved edge | Inputs still required |
| --- | --- |
| `exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction` | Point-indexed BUC data with a common bound, supplied endpoint and differential families, symmetry, positivity, bounded unit sublevels, smoothness of the self-chart tensor section at every real time, and the actual chart-transition covariance law. It assembles precisely that metric; it does not produce covariance or smoothness. |
| `exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction_of_flatHSEnergy` | Endpoint derivatives, overlap containment and endpoint-germ compatibility, background transport, smooth positive reconstruction, and the chartwise flat-Hilbert–Schmidt energy record. Its subordinate compact-support/maximum-principle and corrected-lower-linearization records remain substantive premises. |
| `exists_inverseDeTurck_twoRestartPointFlowPackage_of_metricEntries_five` | A supplied metric family, background and anchor, any upper time bound `Tmax > 0`, and joint C5 metric entries at time zero at that anchor. It constructs forward/backward point-flow data at some `t ∈ Ioo 0 Tmax`. This is a local result at a chosen anchor, not yet a common global manifold diffeomorphism for all times. |
| `isClosedRicciFlowSolutionAt_of_spatialVariationalTwoRestartPackage` | The supplied local point-flow package plus its BUC coefficient, realization, geometric and regularity hypotheses. Its complete long signature is printed in Appendix B. It is a conditional genuine Ricci equation at the supplied point/time. |
| `hasDerivAt_pullbackBilinearApply_eq_neg_two_ricci_comp` and `hasDerivAt_pullbackBilinearApply_eq_neg_two_source_ricciTrace` | Actual derivatives of the moving coefficient and gauge differential, the DeTurck rate identity, and in the source-trace version the curvature intertwining data. Calculus and trace cancellation are proved; an arbitrary diffeomorphism flow is not manufactured. |

The flat-semigroup transport route must not be used for arbitrary nonlinear chart transitions. Flat heat propagation does not commute with a general nonlinear coordinate change. The alternative overlap-energy route replaces that requirement by compact support/maximum-principle and lower-order estimates, which must themselves be proved for the actual local construction. A difference of two locally constructed solutions on an overlap need not vanish there just because the initial metrics match: artificial chart boundaries and outside extensions affect parabolic evolution immediately. A finite atlas and a partition of unity by themselves do not solve this.

### 1.5 Normalization adapters already proved

Further source review found the exact rescaling route in `Global/NormalizedFlowRescaling.lean`, `MetricRescale.lean`, `MetricRescaleCurvature.lean`, `MetricRescaleFiniteAtlasIntegrals.lean`, and `MetricRescaleFiniteAtlasForwardFlow.lean`. These are additional context modules beyond the 93-file DeTurck search. Their relevant declarations are source-verified and their full signatures are included in Appendix B's support probe.

`timeReparameterizedConstRescaling` is the actual metric family `c(t) • gt(τ(t))`, with positivity of `c` at every real time. `isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_componentHasDerivAt` proves the normalized PDE from `τ'(t) = c(t)⁻¹`, the actual componentwise Ricci derivative at the reached base time, and `c'(t) = (2/n) meanScalar(c(t) • gt(τ(t))) c(t)`. The `_of_ricciFlow` version instead accepts the genuine Ricci-flow predicate and `TimeDifferentiableAt` at that reached time. These are proved general **conditional normalization identities**, not just mean-zero cases.

`ClosedSmoothRiemannianMetric.constSMul`, `.constSMul_ricciAt`, and `.constSMul_scalarAt` construct positive rescalings and prove their actual curvature scaling. `FiniteAtlasConstSMulAreaData.meanScalar_constSMul` proves mean-scalar scaling by the inverse factor, assuming its area/density record and nonzero base total volume. `FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable` supplies both area formulas from base density integrability; the area formulas themselves must not be reopened as missing inputs.

`isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale` reduces the scale ODE to `c'(t) = (2/n) meanScalar(gt(τ(t)))`, retaining the finite-atlas measure data, volume, source equation and time differentiability. The forward-ray theorem `isClosedNormalizedRicciFlowSolutionAt_forwardTimeReparameterizedConstRescaling_Ici_of_baseForwardFlow_of_baseDensityIntegrable` additionally uses `τ(0)=0`, positivity and both scalar ODEs on the forward ray, base chart-density integrability and nonzero volume at reached times, and a differentiable base Ricci flow on that ray. It proves the normalized equation on the ray. Its positive-scale extension preserves the full time germ at forward times, by `positiveForwardScaleExtension_eventuallyEq_of_mem_Ici`.

Missing for the present short-time producer: construct those scalar functions with `c(0)=1`, keep reached times inside the finite base interval, and derive any required density/volume and time regularity from the actual solution. The pointwise rescaling theorem is suitable for a finite interval; an all-forward-ray wrapper cannot be invoked using only a short-time source. No theorem producing these complete inputs from the bare short-time interface was found. Task 8 is limited to that remaining work.

### 1.6 Legacy interfaces and the Hamilton boundary

`AnalyticFoundation.lean` also defines `DeTurckShortTimeExistenceData`, `HasDeTurckShortTimeExistence`, `ShortTimeRicciFlowSolutionData`, and `HasShortTimeRicciFlowSolution`. Their constructors are probed in Appendix B. They are indexed by an already supplied legacy flow datum and require nested fixed-point, linear-theory, regularity or pullback data. They are not producers of `RicciFlowShortTimeExistence3`.

The same file's `StrictlyParabolicDeTurckSystemData` stores a positive scalar multiple of the identity on tensor fields, with no cotangent frequency argument. Its `ParabolicLinearTheoryData` stores a time-indexed right inverse and a pointwise domination by the forcing's value at the same point. These are not the standard frequency-dependent principal symbol and nonlocal parabolic Schauder solution estimate. They must not be reinterpreted as those theorems. The frozen `RicciFlowInterface.lean` is the surgery/extinction interface; its freely supplied evidence propositions do not establish the genuine local PDE. All were left untouched.

The current Hamilton finite-energy interface asks for a normalized flow on the entire forward ray, finite traceless-Ricci energy, compact realization of the mean-energy pair and a positive mean-scalar floor. Short-time existence alone proves none of the long-time, pinching or compactness conditions. Moreover, the universal manifold hypotheses do not give a positive-Ricci initial metric. Unit recognition being proved does not remove these analytic obligations. These conclusions agree with the current mission files and the checked Hamilton reduction, not with the older M-frontier recommendation.

## 2. Pinned Mathlib inventory

The complete commands and outputs are in Appendix E. Absence searches cover the full tree as well as `Analysis` and `Geometry/Manifold`; unrelated matches are retained so that a nonzero match count is not mistaken for PDE support. Appendix F gives the actual elaborated signatures. A focused build of four previously uncached Mathlib modules succeeded before the final probe.

| Area | Actual available material | What is absent for this proof |
| --- | --- | --- |
| Banach-space ODE | `Analysis/ODE/PicardLindelof.lean`: `ODE.picard` is the integral iteration, not itself an existence theorem. `IsPicardLindelof` requires spatial Lipschitz bounds, time continuity, a vector-field norm bound, and an interval-size inequality. `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` works in a complete normed real vector space and gives a curve on the specified closed interval. The continuous-family variant and `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` are also checked. | No automatic interpretation of an unbounded spatial differential operator as a locally Lipschitz Banach vector field. |
| Banach fixed point | `Topology/MetricSpace/Contracting.lean`: `ContractingWith.exists_fixedPoint` and `exists_fixedPoint'`; completeness, contraction, and in the latter theorem an invariant complete subset are real hypotheses. | No smoothing estimate, invariant PDE ball or compatible atlas solution comes from the fixed-point theorem itself. |
| Evolution semigroups | Full-tree PDE search found no heat-semigroup, Hille–Yosida, analytic-semigroup or maximal-regularity theorem. `Analysis` semigroup hits are algebraic structures. Topological dynamical-flow vocabulary is not an unbounded-generator theory. | Compact-manifold heat generator/domain, strongly continuous analytic heat semigroup and parabolic mapping estimates. These are partly implemented for Euclidean BUC in the **repo**, not Mathlib. |
| Heat/Laplacian on manifolds | No whole-word heat/Laplacian/Laplace–Beltrami hit in `Geometry/Manifold`. `Analysis/InnerProductSpace/Laplacian.lean` provides `InnerProductSpace.instLaplacian` and `bilinearIteratedFDerivTwo` on finite-dimensional real inner-product spaces. | A Riemannian heat kernel and a linear parabolic solution operator on an arbitrary closed manifold. The repo's intrinsic Laplacian is separate and does exist. |
| Sobolev | `Analysis/Distribution/Sobolev.lean`: `TemperedDistribution.MemSobolev`, its Laplacian map from order `s` to `s-2` at exponent 2, and the bounded Fourier-multiplier theorem. `Analysis/FunctionalSpaces/SobolevInequality.lean`: `MeasureTheory.eLpNorm_le_eLpNorm_fderiv` for compactly supported C1 Euclidean functions, with its dimensional/exponent hypotheses. | Bundle-valued Sobolev spaces on finite manifold atlases, norm equivalence and chart transport, parabolic maximal regularity, the required product/inversion estimates and a compactness theorem suited to passing Galerkin nonlinearities to a limit. A distributional membership predicate is not this entire stack. |
| Hölder/Schauder | `Topology/MetricSpace/HolderNorm.lean`: `eHolderNorm` and `MemHolder`. `Analysis/Calculus/ContDiffHolder/Pointwise.lean`: `ContDiffPointwiseHolderAt` and `ContDiffAt.contDiffPointwiseHolderAt`. | Anisotropic parabolic Hölder Banach spaces with time exponent α/2, their trace and extension theory, and linear Schauder existence/estimates. Pointwise Hölder differentiability is not a uniform parabolic estimate. Searches for Schauder estimates found no such Mathlib result; Schauder bases are unrelated. |
| Elliptic regularity | Distributional derivatives and Fourier-multiplier tools are present. | Variable-coefficient elliptic regularity, a compact-manifold Laplacian spectral/resolvent construction with smooth eigenfunctions and the estimates needed for the proposed semigroup route were not found. |
| Atlas/integration | `Geometry/Manifold/PartitionOfUnity.lean`: `SmoothPartitionOfUnity.exists_isSubordinate`, with its finite-dimensional, smooth-manifold and topological hypotheses printed in Appendix F. Euclidean integration and change-of-variables tools exist. | No general manifold parabolic integration-by-parts or energy-existence package in Mathlib. The old integration report must not be read as saying the **repo** lacks its later Hausdorff metric-volume and restricted chart-area results. |

The Banach ODE and fixed-point signatures retain `CompleteSpace`; the ODE theorem is not restricted to finite dimension. Finite-dimensional Galerkin truncations therefore fit its ambient type requirements, once their vector fields are proved locally Lipschitz. This says nothing about estimates uniform in the truncation index.

## 3. Lemma-level decomposition and route comparison

Classification follows the Hamilton survey: A is a local construction from landed material, B needs substantial missing analytic theory, and C is an exact geometric/analytic producer whose proof was not established here. Effort estimates below are planning judgments in expert formalizer time, not measurements or commitments.

Common contract for future tasks: freeze the recorded base plus independently accepted prerequisite commits; own only the new module named below; preserve all existing and frozen files. A future task gate is

```sh
LEAN_NUM_THREADS=1 lake env lean <the module path below>
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <the module path below>
git diff --check
```

Lean and diff must exit 0; the token scan must have no matches. Probe each new theorem's exact type and dependency closure. Future task files need fresh hashes after prerequisites land; this report does not invent them. The displayed `...Goal` definitions are the complete proposed propositions, checked together in Appendix D. Proving one is a separate worker job. In particular, the abstract Banach signatures in tasks 4–5 are obligations for the **specified geometric operators**, not universal existence assertions about an arbitrary continuous linear map.

### Task 1. Compact ellipticity constant, class A

Module: `Poincare/Global/CompactCoefficientEllipticity.lean`.
Namespace: `Poincare.CompactCoefficientEllipticity`.
Imports: `Poincare.Global.RiemannianContext`, `Mathlib.Topology.Order.Compact`, `Mathlib.Analysis.InnerProductSpace.PiL2`.
Objective: from a continuous family of positive bilinear forms on a compact parameter space, produce one positive quadratic lower bound, with the constant before the point and vector quantifiers.

Displayed signature: `compactCoercivityGoal` in Appendix D. The intended theorem takes `A`, `Continuous A` and pointwise positivity and returns the existential bound in that definition. No parabolic hypothesis is needed.

Proof route: minimize `(x,v) ↦ A x v v` on the product with the Euclidean unit sphere; use strict positivity of the minimum, then homogeneity for nonzero vectors and a separate zero-vector case. Empty parameter sets are harmless and must be handled. `IsCompact.exists_isMinOn` is source-verified and probed. Apply this later to the actual inverse principal coefficient on a compact chart buffer, after proving its continuity and positivity.

Checked proposed proposition, in the common context of Appendix D:

```lean
def compactCoercivityGoal {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (A : K → Bilin) : Prop :=
  Continuous A → (∀ x v, v ≠ 0 → 0 < A x v v) →
    ∃ c : ℝ, 0 < c ∧ ∀ x v, c * ‖v‖ ^ 2 ≤ A x v v
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CompactCoefficientEllipticity.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/CompactCoefficientEllipticity.lean
git diff --check
```

The common token and diff gates also apply. Stop exactly if positivity/continuity of the intended coefficient cannot be obtained without assuming the desired uniform bound. Do not replace the conclusion by pointwise constants. Expected effort: 1–3 days. This is the first dispatchable A task, not a claim that it is already proved here.

### Task 2. Actual second-order principal part, class C

Module: `Poincare/Global/DeTurckPrincipalSecondJet.lean`.
Namespace: `Poincare.DeTurckPrincipalSecondJet`.
Imports: `Poincare.Global.DeTurckBUCCoefficientIdentification`, `Poincare.Global.DeTurckGaugedFlowClosure`, `Mathlib.Analysis.InnerProductSpace.PiL2`.
Objective: prove that, at a genuine cutoff-one chart point, the actual DeTurck chart rate is the inverse-metric contraction of the metric's second spatial derivative plus a function of only its value and first spatial derivative. Appendix D defines `inverseEntries`, `spatialPrincipal`, and `principalIdentityGoal` with the actual chart metric and actual DeTurck rate.

The existential lower-order function is quantified **before** the arbitrary input metric. Thus it cannot be chosen separately from each metric's second jet. This is stronger than merely defining the remainder by subtracting a flat Laplacian. Prove the inverse-matrix derivative identity, expand the Christoffel/Ricci and Lie terms, cancel mixed second derivatives, and identify the remaining expression as a first-jet function. Then the principal symbol is multiplication by `g^{ab} ξa ξb`; task 1 supplies uniform ellipticity on compact buffers. The currently checked flat-principal-removed identity still contains curvature and field derivatives and does not establish this result.

Checked proposed proposition, in the common context of Appendix D:

```lean
def principalIdentityGoal (bg : ClosedSmoothRiemannianMetric 3 M)
    (anchor : M) (z : E) : Prop :=
  z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target →
  (∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) →
  ∃ lower : Bilin → Jet1 → Bilin,
    ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
      deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z v w =
        spatialPrincipal (CovariantDerivative.chartMetric g.inner anchor) z v w +
        lower (CovariantDerivative.chartMetric g.inner anchor z)
          (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) v w
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckPrincipalSecondJet.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DeTurckPrincipalSecondJet.lean
git diff --check
```

The common token and diff gates also apply. Stop at the exact uncancelled second-jet expression if it cannot be eliminated; do not assume a bounded BUC map for it. Expected effort: 2–6 weeks; most work is coordinate algebra and matching the canonical curvature definitions, not a new PDE theorem.

### Task 3. Euclidean linear parabolic Schauder solvability, class B

Module: `Poincare/Global/EuclideanParabolicSchauder.lean`.
Namespace: `Poincare.EuclideanParabolicSchauder`.
Imports: the task-1 module, `Poincare.Global.VectorHeatCauchy`, `Poincare.Global.HeatSemigroupBUCPositiveGenerator`, `Mathlib.Topology.MetricSpace.HolderNorm`.
Objective: prove the exact `linearSchauderGoal` in Appendix D. It is a scalar zero-initial-data problem on `[0,T] × ℝ³`, `T ≤ 1`, with bounded parabolically Hölder symmetric uniformly elliptic principal coefficients. It produces actual time and spatial derivatives, the equation and a uniform parabolic bound on the solution, time derivative, gradient and Hessian. Six components give the diagonal principal system; bounded coupled lower-order terms are handled after this estimate.

The raw predicates in the probe spell out the supremum and Hölder bounds. They do not assert that the corresponding Banach spaces already exist. Split implementation into the following real lemmas, keeping this exact final estimate as the gate:

1. Complete the normed spaces defined by those actual function/derivative graphs; prove trace, restriction, cutoff multiplication and norm equivalence.
2. For the constant-coefficient Gaussian problem, prove the Hessian cancellation estimate against Hölder forcing, including integrability of the time singularity. A bound of order `1/(t-s)` alone is not integrable at `s=t` and does not suffice.
3. Freeze the principal coefficient on small parabolic cylinders and bound the coefficient oscillation error in those norms.
4. Construct the variable-coefficient solver by localization and an error correction; retain constants before the forcing quantifier.
5. Prove the initial trace and one-sided initial derivative in the same solution class. Do not upgrade one-sided derivatives by a mere set inclusion.

Checked proposed proposition, in the common context of Appendix D:

```lean
def linearSchauderGoal : Prop :=
  ∀ (α T ell Λ : ℝ), 0 < α → α < 1 → 0 < T → T ≤ 1 → 0 < ell →
  ∀ a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ p ∈ cylinder T, ∀ i j, a p i j = a p j i) →
    (∀ i j, parabolicBound α T Λ (fun p => a p i j)) →
    (∀ p ∈ cylinder T, ∀ ξ : E,
      ell * ‖ξ‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a p i j * ξ i * ξ j) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ × E → ℝ) (Fbound : ℝ),
      0 ≤ Fbound → parabolicBound α T Fbound f →
      ∃ u ut : ℝ × E → ℝ, ∃ Du : ℝ × E → E →L[ℝ] ℝ,
        ∃ DDu : ℝ × E → Bilin,
          (∀ x, u (0, x) = 0) ∧
          (∀ p ∈ cylinder T,
            HasDerivWithinAt (fun s => u (s, p.2)) (ut p) (Icc 0 T) p.1 ∧
            HasFDerivAt (fun x => u (p.1, x)) (Du p) p.2 ∧
            HasFDerivAt (fun x => Du (p.1, x)) (DDu p) p.2 ∧
            ut p = linearRate a DDu p + f p) ∧
          parabolicBound α T (C * Fbound) u ∧
          parabolicBound α T (C * Fbound) ut ∧
          parabolicBound α T (C * Fbound) Du ∧
          parabolicBound α T (C * Fbound) DDu
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/EuclideanParabolicSchauder.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/EuclideanParabolicSchauder.lean
git diff --check
```

The common token and diff gates also apply. Stop if only pointwise heat smoothing or a bounded-generator witness is proved: record that as a partial lemma, not a Schauder theorem. Precise missing Mathlib theory: parabolic Hölder function spaces and linear variable-coefficient Schauder existence/estimates. Expected effort: several months, plausibly 6–18 person-months with substantial uncertainty. This is the first missing PDE library theorem, even though task 1 is locally accessible.

### Task 4. Compatible finite-atlas linear inverse, class B

Module: `Poincare/Global/ClosedTensorParabolicParametrix.lean`.
Namespace: `Poincare.ClosedTensorParabolicParametrix`.
Imports: task 3, `Poincare.Global.HausdorffFiniteAtlasChartFrameReduction`, `Mathlib.Geometry.Manifold.PartitionOfUnity`.
Objective: on a finite buffered atlas, define `X` as compatible symmetric-two-tensor perturbations with zero initial trace and parabolic order `(2+α,1+α/2)`, and `Y` as compatible order `(α,α/2)` forcing. Their norm is the finite maximum of the local derivative/Hölder norms, after the chosen subordinate cutoffs. For the **actual frozen-background tensor linearization** `L : X →L[ℝ] Y`, prove `linearInverseGoal L` from Appendix D.

Required lemmas: compatible chart sections form a closed subspace; the finite norm is complete and independent up to comparison of the chosen buffered trivializations; multiplication by cutoff and changes of trivialization are bounded; the local solution patching gives a parametrix; chart-boundary and cutoff commutators give an error operator small on a shortened time interval; invert that error to obtain a genuine global right inverse. Lower-order coupled terms must be included in this error or solved in a further bounded perturbation step.

The `linearInverseGoal` probe deliberately takes arbitrary abstract Banach spaces only to check the operator type. There is no claim that an arbitrary `L` has such an inverse. A dispatch for this task must first freeze the concrete `X`, `Y`, `L` definitions and their norms from the construction just specified. A generic right-inverse certificate without that implementation is not a completion.

Checked proposed proposition, in the common context of Appendix D:

```lean
def linearInverseGoal (L : X →L[ℝ] Y) : Prop :=
  ∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedTensorParabolicParametrix.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedTensorParabolicParametrix.lean
git diff --check
```

The common token and diff gates also apply. Stop if the local charts produce independent solutions without a proved commutator correction and overlap law. Missing theory: parabolic Banach spaces of bundle sections and finite-atlas parametrix estimates, not finite-cover existence. Expected effort: 2–6 months after task 3.

### Task 5. Nonlinear residual estimate in the parabolic norm, class B

Module: `Poincare/Global/DeTurckParabolicContraction.lean`.
Namespace: `Poincare.DeTurckParabolicContraction`.
Imports: tasks 2–4 and `Mathlib.Topology.MetricSpace.Contracting`.
Objective: for `g = g₀ + h`, subtract the frozen linearization to define the **actual** DeTurck residual `N : X → Y`. Let `S` be task 4's right inverse and `b` its image of the background forcing. Prove `residualEstimateGoal S N b` in Appendix D, after choosing a short time and radius with uniform positivity of `g₀+h`.

Required lemmas: bounded products in the parabolic norm; smooth metric inversion on the uniformly positive ball; local differentiability of the actual nonlinear geometric operator with a quadratic remainder; a small residual-Lipschitz bound after composing with `S`; and the ball-invariance estimate. Both principal-coefficient variation times `D²h` and the first-derivative quadratic terms must be accounted for. The probe's conclusion is a concrete invariant ball and a contraction constant less than one, not a renamed assertion that a solution already exists.

The abstract signature does not dispatch until the geometric `S`, `N`, `b`, and norms are frozen. In particular, using the existing BUC norm instead of the task-4 parabolic norm is not permitted.

Checked proposed proposition, in the common context of Appendix D:

```lean
def residualEstimateGoal (S : Y →L[ℝ] X) (N : X → Y) (b : X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ q : ℝ≥0, (q : ℝ) < 1 ∧
    MapsTo (fun v => b + S (N v)) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
    LipschitzOnWith q (fun v => b + S (N v)) (Metric.closedBall 0 r)
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckParabolicContraction.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DeTurckParabolicContraction.lean
git diff --check
```

The common token and diff gates also apply. Stop if the second-derivative term requires an unproved BUC Lipschitz bound. Missing theory: parabolic product, inversion, interpolation and nonlinear remainder estimates. Expected effort: 1–4 months after tasks 2–4. Banach's fixed-point theorem itself is already available and is not a new missing lemma.

### Task 6. Smooth regularity and the initial extension, class B

Module: `Poincare/Global/ClosedDeTurckRegularShortTime.lean`.
Namespace: `Poincare.ClosedDeTurckRegularShortTime`.
Imports: task 5, `Poincare.Global.DeTurckGaugedFlowClosure`, `Poincare.Global.MetricFlowJointRegularity`.
Objective: for each `g₀`, prove the exact `regularDeTurckGoal g₀` in Appendix D. Construct the fixed point, prove symmetry and positivity, bootstrap spatial regularity to smooth metric slices, and obtain joint smooth metric entries through the initial time in a total family. Retain the canonical field with background `g₀`.

Required lemmas: the fixed point solves the genuine geometric equation; a differentiated linear equation upgrades each spatial derivative; time derivatives follow with the correct two-spatial-derivative budget; smooth initial data yields compatibility of all required initial jets; extend those jets to negative time while preserving positive definiteness near zero. Outside the retained interval the total metric family may be extended without satisfying the PDE. A BUC positive-interior generator derivative is not an all-order spatial bootstrap.

Checked proposed proposition, in the common context of Appendix D:

```lean
def regularDeTurckGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsDeTurckGaugedFlowAt gt g₀ t x) ∧
      ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x ∞
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedDeTurckRegularShortTime.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedDeTurckRegularShortTime.lean
git diff --check
```

The common token and diff gates also apply. Stop if only `t > 0`, only a right derivative, or only finite spatial regularity is established. Report that exact regularity result without claiming the frozen short-time interface. Missing theory: parabolic boundary regularity and smooth extension with prescribed initial jets. Expected effort: 2–6 months after task 5.

### Task 7. Physical inverse gauge on one common interval, class C

Module: `Poincare/Global/ClosedDeTurckGaugeAssembly.lean`.
Namespace: `Poincare.ClosedDeTurckGaugeAssembly`.
Imports: task 6, `Poincare.Global.DeTurckPointFlowMetricTwoRestartPackage`, `Poincare.Global.DeTurckBUCSpatialVariationalTwoRestartPackage`, `Poincare.Global.DeTurckGaugePullbackDerivative`, `Poincare.Global.DeTurckRicciTracePullback`.
Objective: prove `regularPullbackGoal g₀ T gt` from Appendix D. This jointly smooth concrete-field input is the appropriate producer boundary. The landed C5 theorem supplies the finite-order local package, but it alone does not prove smoothness of every pulled-back metric slice; the new producer retains all spatial orders. Its output retains joint C3 entries on the same Ricci-flow family for task 8. It permits `0 < S ≤ T`, avoiding the unsupported demand for the whole originally supplied interval.

Required lemmas: choose a common positive time over a finite cover; construct the forward and backward solutions for the same time-dependent vector field; use ODE uniqueness to identify those choices on overlaps; construct globally inverse maps with the required finite joint regularity starting at the identity; identify their derivative with the variational solution; prove smooth spatial dependence from the jointly smooth canonical field for smooth pulled-back metric slices; and prove initial equality, joint C3 entries, curvature naturality and the equation including zero. The pointwise cancellation and local ODE pieces are proved in the repository. The complete global producer is not established here.

Use the sign already proved in the repository: the inverse gauge solves `dφ/dt = -W(gt,bg) ∘ φ`; its differential solves the corresponding negative variational equation. In the harmonic-map description, the inverse coordinate map is related to a harmonic-map heat equation after transporting the evolving metric. This is not permission to assume an independent harmonic-map heat-flow existence theorem. For existence, solving the canonical DeTurck PDE and then this ODE uses the landed calculus more directly. Global Ricci-flow uniqueness is unnecessary, though local ODE uniqueness is necessary for this assembly.

Checked proposed proposition, in the common context of Appendix D:

```lean
def regularPullbackGoal (g₀ : ClosedSmoothRiemannianMetric 3 M)
    (T : ℝ) (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) : Prop :=
  0 < T → gt 0 = g₀ →
  (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsDeTurckGaugedFlowAt gt g₀ t x) →
  (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x ∞) →
  ∃ S : ℝ, 0 < S ∧ S ≤ T ∧ ∃ ht : ℝ → ClosedSmoothRiemannianMetric 3 M,
    ht 0 = g₀ ∧
      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : M, IsClosedRicciFlowSolutionAt ht t x) ∧
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : M, MetricEntriesJointContDiffAt ht t x 3
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedDeTurckGaugeAssembly.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedDeTurckGaugeAssembly.lean
git diff --check
```

The common token and diff gates also apply. Stop at a point-indexed restarted gauge, missing common time, missing overlap equality, or missing initial derivative. Expected effort: several weeks to a few months after task 6. No new Banach ODE theorem is needed; exact global and initial-time assembly still is.

### Task 8. Normalization, class C

Module: `Poincare/Global/ClosedRicciFlowNormalization.lean`.
Namespace: `Poincare.ClosedRicciFlowNormalization`.
Imports: task 7, `Poincare.Global.NormalizedFlowRescaling`, `Poincare.Global.MetricRescaleFiniteAtlasIntegrals`, `Poincare.Global.MetricRescaleFiniteAtlasForwardFlow`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, `Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv`. Both Mathlib import paths were verified in the pinned tree; the support signature probe uses the already-built root envelope.
Objective: produce the `normalizationGoal` in Appendix D from actual regular Ricci flows. The input `regularRicciFlowGoal` includes the actual PDE and joint C3 metric entries on the **same** family. This is stronger than the bare short-time interface and sufficient to formulate the required moving scalar/volume continuity work. Task 7 must retain that regularity in its output before this task is dispatched.

Required remaining lemmas: assemble positive finite metric volume for nonempty `M` and the chart-density integrability data; prove local-in-time continuity of the mean scalar along the retained family; construct a positive scalar scale factor and a strictly increasing reparameterization whose reached times stay inside the base interval; transfer the initial metric and the ordinary derivative at zero. Reuse the already-proved metric/Ricci/mean-scalar scaling and rescaling chain-rule identities in section 1.5. Handle the empty manifold separately instead of assuming division by a positive volume there. Shrink the time interval as needed.

The actual normalized target uses `IsClosedNormalizedRicciFlowSolutionAt`. Do not set the mean scalar to zero to obtain a conversion: that is a special-case theorem, not the general normalization argument. The metric scaling construction and conditional PDE adapter already exist. What must be frozen is the scalar-function and measure-data producer on a finite interval. One route is to construct the scale in base time as the exponential of an integral of `(2/3) meanScalar`, integrate that positive scale to obtain normalized time, and invert this strictly increasing local time map. This only requires the appropriate continuity/FTC and inverse derivative results, rather than assuming Lipschitz dependence of the mean scalar for a new Picard system. This finite-interval producer was not proved here.

Checked proposed proposition, in the common context of Appendix D:

```lean
def normalizationGoal : Prop :=
  (∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) →
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedRicciFlowNormalization.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedRicciFlowNormalization.lean
git diff --check
```

The common token and diff gates also apply. Stop if mean continuity, the required chart-density integrability, reached-time containment or initial differentiability cannot be proved for the actual retained family. Do not restate the already-proved curvature scaling or rescaling chain rule as a new missing theorem. Missing pieces are the scalar-function and measure-data producer, not a second quasilinear PDE solver. Expected effort: several weeks after a suitably regular task-7 output.

### Task 9. Final short-time interface assembly, class A, already checked as bookkeeping

Module, if a named export is useful: `Poincare/Global/ClosedRicciShortTimeFromPointwise.lean`.
Namespace: `Poincare.ClosedRicciShortTimeFromPointwise`.
Imports: `Poincare.Global.ShortTimeInterface`, `Poincare.Global.DeTurckBUCScalarEvolutionBridge`.
Objective: universalize the per-metric family, or apply the pointwise bilinear derivative bridge. Both complete scratch proofs appear in Appendix D. There is no new analytic content in this task, so do not dispatch it instead of tasks 1–8 merely to create a theorem count.

Checked proposed proposition, in the common context of Appendix D:

```lean
def strongFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace (closedSmoothModelWithCorners 3) x,
        HasDerivAt (fun s => (gt s).inner x v w) (-2 * (gt t).ricciAt x v w) t
```

Exact Lean gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedRicciShortTimeFromPointwise.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedRicciShortTimeFromPointwise.lean
git diff --check
```

The common token and diff gates also apply. Stop if its input is only a positive-interior solution or a right derivative at zero. Expected effort: less than one day once the actual producer exists.

### Route ranking

| Rank | Route | Assessment |
| --- | --- | --- |
| 1 | Finite-atlas parabolic Hölder linearization and contraction | Best fit to the existing geometry and Euclidean Gaussian analysis. The decisive new work is the linear Schauder estimate, compatible parametrix, nonlinear derivative accounting and regularity bootstrap. A Sobolev version is possible, but needs manifold Sobolev product, trace and interpolation machinery not already supplied by the Euclidean distributional membership API. This remains a large multi-month to multi-year library campaign. |
| 2 | Linear heat semigroup on a compact manifold | A good long-term architecture once the compact-manifold elliptic/resolvent theory is built. Requires a self-adjoint or sectorial bundle Laplacian, domain/graph norm control, smoothing and resolvent estimates, an analytic semigroup and maximal regularity. The repo's flat BUC semigroup is useful evidence and a template but not that operator. A semigroup estimate losing two derivatives like `t⁻¹` does not alone close a same-norm contraction. Expected additional foundation cost is larger than route 1. |
| 3 | Finite-dimensional Galerkin approximations in a finite atlas | Each projected finite-dimensional smooth vector field is accessible to the checked Banach ODE theorem. The hard work is uniform lifespan and positivity, derivative/energy bounds independent of projection dimension, a compatible dense tensor approximation, compactness in a topology strong enough for the nonlinear second derivatives, convergence of the initial trace, and smooth regularity of the limit. These are not consequences of the ODE theorem. Poor choice if the aim is to bypass parabolic analysis; likely the largest library burden here. |

This ranking is my assessment of the current formal interfaces. For mathematical orientation, Koch–Lamm's Euclidean Ricci–DeTurck construction uses a fixed point in derivative-sensitive spacetime norms; it does not assert that the genuine remainder is locally Lipschitz on plain BUC. Its small perturbation theorem on Euclidean space is not an arbitrary closed-manifold producer. See [Koch–Lamm, section 4](https://arxiv.org/html/0902.1488v2#S4). The historical compact existence and DeTurck simplification are also described in [Chen–Zhu](https://arxiv.org/abs/math/0505447). These external references guide the proposed proof strategy; all claims about Lean availability come from the pinned local tree.

## 4. Smallest analytic boundary and the first dispatch

For the existing target, the smallest per-initial-metric payload found is literally the following. The full ambient manifold context is retained in Appendix D:

```lean
-- Proposed goal, not a proved existence theorem.
def minimalFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t x
```

Universalizing over `g₀` is definitionally `RicciFlowShortTimeExistence3 M`; the anonymous probe proves this. This is minimal relative to the landed interface, not a claim of logical minimality among all equivalent formulations.

For an analytic solver, the cleaner sufficient boundary is the probe's `strongFlowGoal`, which replaces the solution predicate by an ordinary `HasDerivAt` equation against **all** tangent-vector slots. The existing `isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt` and `.deriv` turn it into the frozen interface. This avoids asking an analytic worker to assemble the section-test/connection bookkeeping while retaining a genuine derivative. It is stronger than the bare target and is proved sufficient, not claimed equivalent.

The normalized analogue is `normalizedFlowGoal` in Appendix D, with the same initial metric and `[0,T)` interval and a compatible Borel structure. No landed theorem was found that turns this bare normalized existence assertion into unnormalized short-time existence, or conversely. The checked general conditional rescaling adapters in section 1.5 need scalar ODE, positivity, reached-time and differentiability data; the mean-zero reduction is only a special case. Producing the general inputs requires the work in task 8. Do not conjoin both PDE predicates for the same unrescaled family and call that normalization.

Can the boundary be split into **one chartwise linear existence assumption plus entirely proved gluing/pullback bookkeeping**? **No.** It can be decomposed into linear existence, nonlinear estimates, compatible global solution construction, initial-time/all-order regularity and gauge assembly, with many proved internal edges. The missing remainder estimate loses derivatives; local parabolic solutions need a coherent global construction; the broad DeTurck interface lacks the time regularity used by the gauge ODE; and the frozen endpoint includes zero. None is eliminated by a finite cover alone. The checked `linearSchauderGoal` is therefore an honest first missing library theorem, not a sufficient replacement premise by itself.

First independent action for the next agent:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/ricci-existence-survey/Targets.lean
```

Recreate the scratch file from Appendix D if it has expired. Then freeze task 1, with only its new module allowed, at the recorded base or an independently checked descendant. Prove its compact uniform lower bound. Do not dispatch a universal closed Ricci-flow theorem as an A-sized task.

## Verification and handoff

Five final scratch probes pass: `Inventory.lean`, `ExtraInventory.lean`, `Support.lean`, `Mathlib.lean`, and `Targets.lean`. The latter contains two anonymous proofs of existing reductions and definitions of proposed goals. No open PDE target was supplied a proof body. Failed probe diagnostics are retained below, including a wrong pretty-printer option, one omitted namespace, a missing cache module, and syntax/namespace corrections in the proposed target program. Final semantic review strengthened the concrete DeTurck input to joint smoothness and retained joint C3 regularity in the gauge output; these signatures also pass. Final commands and actual outputs follow.

Only this report is committed. Root integration builds and mission/audit acceptance remain the orchestrator's responsibility; running the full project audit would not verify a new proof here because no repository Lean source changed.


## Appendix D. Complete proposed goal program and reduction probes

These are definitions of propositions, with two anonymous proof examples for existing bookkeeping. No open goal below is proved merely because its definition elaborates. The common context and auxiliary norm/coordinate definitions make every proposed signature unambiguous.

```lean
import Poincare.Global.DeTurckBUCScalarEvolutionBridge
import Poincare.Global.DeTurckPointFlowMetricTwoRestartPackage
import Poincare.Global.NormalizedFlow
import Poincare.Global.DeTurckGaugedFlowClosure
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option format.width 110
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology BigOperators NNReal
namespace RicciExistenceSurvey
open Poincare
abbrev E := ClosedSmoothModel 3
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
abbrev Jet1 := E →L[ℝ] Bilin

def compactCoercivityGoal {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (A : K → Bilin) : Prop :=
  Continuous A → (∀ x v, v ≠ 0 → 0 < A x v v) →
    ∃ c : ℝ, 0 < c ∧ ∀ x v, c * ‖v‖ ^ 2 ≤ A x v v

abbrev basis3 (i : Fin 3) : E := EuclideanSpace.basisFun (Fin 3) ℝ i

def inverseEntries (G : Bilin) : Matrix (Fin 3) (Fin 3) ℝ :=
  (fun i j => G (basis3 i) (basis3 j))⁻¹

def spatialPrincipal (G : E → Bilin) (z v w : E) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    inverseEntries (G z) i j *
      fderiv ℝ (fderiv ℝ G) z (basis3 i) (basis3 j) v w

section Manifold
universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

def principalIdentityGoal (bg : ClosedSmoothRiemannianMetric 3 M)
    (anchor : M) (z : E) : Prop :=
  z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target →
  (∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) →
  ∃ lower : Bilin → Jet1 → Bilin,
    ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
      deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z v w =
        spatialPrincipal (CovariantDerivative.chartMetric g.inner anchor) z v w +
        lower (CovariantDerivative.chartMetric g.inner anchor z)
          (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) v w

variable [SecondCountableTopology M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]

def minimalFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t x

def strongFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      ∀ v w : TangentSpace (closedSmoothModelWithCorners 3) x,
        HasDerivAt (fun s => (gt s).inner x v w) (-2 * (gt t).ricciAt x v w) t

def regularDeTurckGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsDeTurckGaugedFlowAt gt g₀ t x) ∧
      ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x ∞

def regularPullbackGoal (g₀ : ClosedSmoothRiemannianMetric 3 M)
    (T : ℝ) (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) : Prop :=
  0 < T → gt 0 = g₀ →
  (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsDeTurckGaugedFlowAt gt g₀ t x) →
  (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x ∞) →
  ∃ S : ℝ, 0 < S ∧ S ≤ T ∧ ∃ ht : ℝ → ClosedSmoothRiemannianMetric 3 M,
    ht 0 = g₀ ∧
      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : M, IsClosedRicciFlowSolutionAt ht t x) ∧
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : M, MetricEntriesJointContDiffAt ht t x 3

-- These are scratch proof witnesses for already-landed bookkeeping only.
example (h : ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, minimalFlowGoal g₀) :
    RicciFlowShortTimeExistence3 M := h
example (h : ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, strongFlowGoal g₀) :
    RicciFlowShortTimeExistence3 M := by
  intro g₀
  obtain ⟨T, hT, gt, h0, hder⟩ := h g₀
  refine ⟨T, hT, gt, h0, ?_⟩
  intro t ht x
  apply isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt
  intro v w
  exact (hder t ht x v w).deriv

variable [MeasurableSpace M] [BorelSpace M]
def normalizedFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x

def regularRicciFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x) ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3

def normalizationGoal : Prop :=
  (∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) →
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀
end Manifold

-- Raw function predicates, not claims that a parabolic Banach space is landed.
def cylinder (T : ℝ) : Set (ℝ × E) := Icc 0 T ×ˢ univ

def parabolicBound {F : Type*} [NormedAddCommGroup F]
    (α T C : ℝ) (f : ℝ × E → F) : Prop :=
  (∀ p ∈ cylinder T, ‖f p‖ ≤ C) ∧
  ∀ p ∈ cylinder T, ∀ q ∈ cylinder T,
    ‖f p - f q‖ ≤ C * (‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|) ^ α

def linearRate (a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ)
    (H : ℝ × E → Bilin) (p : ℝ × E) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, a p i j * H p (basis3 i) (basis3 j)

def linearSchauderGoal : Prop :=
  ∀ (α T ell Λ : ℝ), 0 < α → α < 1 → 0 < T → T ≤ 1 → 0 < ell →
  ∀ a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ p ∈ cylinder T, ∀ i j, a p i j = a p j i) →
    (∀ i j, parabolicBound α T Λ (fun p => a p i j)) →
    (∀ p ∈ cylinder T, ∀ ξ : E,
      ell * ‖ξ‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, a p i j * ξ i * ξ j) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ × E → ℝ) (Fbound : ℝ),
      0 ≤ Fbound → parabolicBound α T Fbound f →
      ∃ u ut : ℝ × E → ℝ, ∃ Du : ℝ × E → E →L[ℝ] ℝ,
        ∃ DDu : ℝ × E → Bilin,
          (∀ x, u (0, x) = 0) ∧
          (∀ p ∈ cylinder T,
            HasDerivWithinAt (fun s => u (s, p.2)) (ut p) (Icc 0 T) p.1 ∧
            HasFDerivAt (fun x => u (p.1, x)) (Du p) p.2 ∧
            HasFDerivAt (fun x => Du (p.1, x)) (DDu p) p.2 ∧
            ut p = linearRate a DDu p + f p) ∧
          parabolicBound α T (C * Fbound) u ∧
          parabolicBound α T (C * Fbound) ut ∧
          parabolicBound α T (C * Fbound) Du ∧
          parabolicBound α T (C * Fbound) DDu

section Banach
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
def linearInverseGoal (L : X →L[ℝ] Y) : Prop :=
  ∃ S : Y →L[ℝ] X, L.comp S = ContinuousLinearMap.id ℝ Y

def residualEstimateGoal (S : Y →L[ℝ] X) (N : X → Y) (b : X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ q : ℝ≥0, (q : ℝ) < 1 ∧
    MapsTo (fun v => b + S (N v)) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
    LipschitzOnWith q (fun v => b + S (N v)) (Metric.closedBall 0 r)
end Banach
#print compactCoercivityGoal
#print principalIdentityGoal
#print linearSchauderGoal
#print linearInverseGoal
#print residualEstimateGoal
#print regularDeTurckGoal
#print regularPullbackGoal
#print minimalFlowGoal
#print strongFlowGoal
#print normalizedFlowGoal
#print regularRicciFlowGoal
#print normalizationGoal
end RicciExistenceSurvey
```

Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/ricci-existence-survey/Targets.lean
```

Actual final output, exit 0:

```text
def RicciExistenceSurvey.compactCoercivityGoal.{u_1} : {K : Type u_1} →
  [inst : TopologicalSpace K] → [CompactSpace K] → (K → Bilin) → Prop :=
fun {K} [TopologicalSpace K] [CompactSpace K] A =>
  Continuous A →
    (∀ (x : K) (v : E), v ≠ 0 → 0 < ((A x) v) v) → ∃ c, 0 < c ∧ ∀ (x : K) (v : E), c * ‖v‖ ^ 2 ≤ ((A x) v) v
def RicciExistenceSurvey.principalIdentityGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] → ClosedSmoothRiemannianMetric 3 M → M → E → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] bg anchor
    z =>
  z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target →
    (∀ᶠ (y : ClosedSmoothModel 3) in 𝓝 z, GeodesicTransport.cutoff anchor y = 1) →
      ∃ lower,
        ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
          ((deTurckChartMetricEvolutionBilin (fun x => g) bg anchor 0 z) v) w =
            spatialPrincipal (CovariantDerivative.chartMetric g.inner anchor) z v w +
              ((lower (CovariantDerivative.chartMetric g.inner anchor z)
                    (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z))
                  v)
                w
def RicciExistenceSurvey.linearSchauderGoal : Prop :=
∀ (α T ell Λ : ℝ),
  0 < α →
    α < 1 →
      0 < T →
        T ≤ 1 →
          0 < ell →
            ∀ (a : ℝ × E → Matrix (Fin 3) (Fin 3) ℝ),
              (∀ p ∈ cylinder T, ∀ (i j : Fin 3), a p i j = a p j i) →
                (∀ (i j : Fin 3), parabolicBound α T Λ fun p => a p i j) →
                  (∀ p ∈ cylinder T, ∀ (ξ : E), ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a p i j * ξ.ofLp i * ξ.ofLp j) →
                    ∃ C,
                      0 < C ∧
                        ∀ (f : ℝ × E → ℝ) (Fbound : ℝ),
                          0 ≤ Fbound →
                            parabolicBound α T Fbound f →
                              ∃ u ut Du DDu,
                                (∀ (x : E), u (0, x) = 0) ∧
                                  (∀ p ∈ cylinder T,
                                      HasDerivWithinAt (fun s => u (s, p.2)) (ut p) (Icc 0 T) p.1 ∧
                                        HasFDerivAt (fun x => u (p.1, x)) (Du p) p.2 ∧
                                          HasFDerivAt (fun x => Du (p.1, x)) (DDu p) p.2 ∧
                                            ut p = linearRate a DDu p + f p) ∧
                                    parabolicBound α T (C * Fbound) u ∧
                                      parabolicBound α T (C * Fbound) ut ∧
                                        parabolicBound α T (C * Fbound) Du ∧ parabolicBound α T (C * Fbound) DDu
def RicciExistenceSurvey.linearInverseGoal.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : NormedAddCommGroup X] →
      [inst_1 : NormedSpace ℝ X] → [inst_2 : NormedAddCommGroup Y] → [inst_3 : NormedSpace ℝ Y] → (X →L[ℝ] Y) → Prop :=
fun {X} {Y} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] L =>
  ∃ S, L.comp S = ContinuousLinearMap.id ℝ Y
def RicciExistenceSurvey.residualEstimateGoal.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : NormedAddCommGroup X] →
      [inst_1 : NormedSpace ℝ X] →
        [inst_2 : NormedAddCommGroup Y] → [inst_3 : NormedSpace ℝ Y] → (Y →L[ℝ] X) → (X → Y) → X → Prop :=
fun {X} {Y} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] S N b =>
  ∃ r,
    0 < r ∧
      ∃ q,
        ↑q < 1 ∧
          MapsTo (fun v => b + S (N v)) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
            LipschitzOnWith q (fun v => b + S (N v)) (Metric.closedBall 0 r)
def RicciExistenceSurvey.regularDeTurckGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] → ClosedSmoothRiemannianMetric 3 M → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] g₀ =>
  ∃ T,
    0 < T ∧
      ∃ gt,
        gt 0 = g₀ ∧
          (∀ t ∈ Ico 0 T, ∀ (x : M), IsDeTurckGaugedFlowAt gt g₀ t x) ∧
            ∀ t ∈ Ico 0 T, ∀ (x : M), MetricEntriesJointContDiffAt gt t x ∞
def RicciExistenceSurvey.regularPullbackGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] →
          ClosedSmoothRiemannianMetric 3 M → ℝ → (ℝ → ClosedSmoothRiemannianMetric 3 M) → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] g₀ T gt =>
  0 < T →
    gt 0 = g₀ →
      (∀ t ∈ Ico 0 T, ∀ (x : M), IsDeTurckGaugedFlowAt gt g₀ t x) →
        (∀ t ∈ Ico 0 T, ∀ (x : M), MetricEntriesJointContDiffAt gt t x ∞) →
          ∃ S,
            0 < S ∧
              S ≤ T ∧
                ∃ ht,
                  ht 0 = g₀ ∧
                    (∀ t ∈ Ico 0 S, ∀ (x : M), IsClosedRicciFlowSolutionAt ht t x) ∧
                      ∀ t ∈ Ico 0 S, ∀ (x : M), MetricEntriesJointContDiffAt ht t x 3
def RicciExistenceSurvey.minimalFlowGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] → ClosedSmoothRiemannianMetric 3 M → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] g₀ =>
  ∃ T, 0 < T ∧ ∃ gt, gt 0 = g₀ ∧ ∀ t ∈ Ico 0 T, ∀ (x : M), IsClosedRicciFlowSolutionAt gt t x
def RicciExistenceSurvey.strongFlowGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] → ClosedSmoothRiemannianMetric 3 M → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] g₀ =>
  ∃ T,
    0 < T ∧
      ∃ gt,
        gt 0 = g₀ ∧
          ∀ t ∈ Ico 0 T,
            ∀ (x : M) (v w : TangentSpace (closedSmoothModelWithCorners 3) x),
              HasDerivAt (fun s => (((gt s).inner x) v) w) (-2 * (gt t).ricciAt x v w) t
def RicciExistenceSurvey.normalizedFlowGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] →
          [CompactSpace M] →
            [ConnectedSpace M] →
              [inst_6 : MeasurableSpace M] → [BorelSpace M] → ClosedSmoothRiemannianMetric 3 M → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] g₀ =>
  ∃ T, 0 < T ∧ ∃ gt, gt 0 = g₀ ∧ ∀ t ∈ Ico 0 T, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x
def RicciExistenceSurvey.regularRicciFlowGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [inst_3 : IsManifold (closedSmoothModelWithCorners 3) ∞ M] → ClosedSmoothRiemannianMetric 3 M → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] g₀ =>
  ∃ T,
    0 < T ∧
      ∃ gt,
        gt 0 = g₀ ∧
          (∀ t ∈ Ico 0 T, ∀ (x : M), IsClosedRicciFlowSolutionAt gt t x) ∧
            ∀ t ∈ Ico 0 T, ∀ (x : M), MetricEntriesJointContDiffAt gt t x 3
def RicciExistenceSurvey.normalizationGoal.{u} : {M : Type u} →
  [inst : TopologicalSpace M] →
    [T2Space M] →
      [inst_2 : ChartedSpace E M] →
        [IsManifold (closedSmoothModelWithCorners 3) ∞ M] →
          [CompactSpace M] → [ConnectedSpace M] → [inst_6 : MeasurableSpace M] → [BorelSpace M] → Prop :=
fun {M} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] =>
  (∀ (g₀ : ClosedSmoothRiemannianMetric 3 M), regularRicciFlowGoal g₀) →
    ∀ (g₀ : ClosedSmoothRiemannianMetric 3 M), normalizedFlowGoal g₀
```

