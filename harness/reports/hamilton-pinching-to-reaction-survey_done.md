# Hamilton pinching to reaction survey

Date: 2026-09-10. Base commit: `c46220fb2dea444a71cfdca3764dcb0370a2afee`.

> Orchestrator note (2026-09-10): this landed copy keeps sections 1-4 and Appendix C (proposed targets and the strongest compiled partial reductions) from the worker report (lines 1-369 and 4014-4529). Appendices A-B and D-F (complete landed signatures, expanded definitions, coefficient calculations, failed probes, search evidence) stay unmerged on branch `worker/hamilton-pinching-to-reaction-survey` at its head commit because of their size.

Branch: `worker/hamilton-pinching-to-reaction-survey`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The survey is complete. Neither Hamilton-analysis clause is discharged from initial pinching alone. The main corrections are:

- The negative pinching reaction belongs to a scalar-normalized quotient. The raw cubic reaction of squared traceless Ricci need not be negative, even for positive Ricci eigenvalues.
- The landed eigenvalue preservation result loses the constant: initial `epsilon` gives `2 * epsilon - 1/3`. The ordinary quotient is `|Ric|²/R²`, so the traceless quotient bound is smaller by `1/3`.
- Normalized scalar, lower-Ricci, and absolute traceless-energy evolution are already automatic from the stated flow and joint C³ entries. The two normalized quotient predicate producers are absent from the public API searched here, but their missing work is algebra and assembly.
- S9 needs both moving integral derivatives and `V ≤ 6E`. Volume differentiation is automatic. The total-scalar route also needs closed Laplacian Stokes; the supplied-geometry Stokes theorem is landed, but a producer from the current hypotheses was not found.
- A uniform scalar upper bound only gives a decaying scalar lower profile through the landed comparison. It does not turn that profile into a uniform positive floor on the infinite ray.

Three named scratch theorems compile: moving derivatives with an explicit Stokes premise, the S9 mean floor with that premise and energy domination, and a constant reaction rate from a quantitative coefficient gap. Their full proofs and actual compiler output are included below. They are evidence inside this report, not landed Lean modules. All three dependency lists are exactly `[propext, Classical.choice, Quot.sound]`.

The task-specific branch and report-only scope override the general branch-naming and HANDOFF-edit rules. Only this report is delivered. No repository Lean file, frozen contract, audit, mission, ledger, or HANDOFF was changed. No task was marked accepted or merged.

## 1. Landed inventory and exact hypothesis audit

### 1.1 Definitions and notation

Throughout the mathematical discussion, on a slice `g` write `R(x)=g.scalarAt x`, `r=meanScalar g`, `N(x)=g.ricciNormSqAt x`, and `U(x)=g.tracelessRicciNormSqAt x`. In dimension three, `U=N-R²/3`. Use `Q=N/R²` and `F_delta=U/R^(2-delta)` only where `R>0`. `E=∫U dμ_g` and `V=∫(R-r)² dμ_g` are unnormalized integrals, not spatial averages.

The literal core and all predicates below are expanded by `#print` in Appendix B. Every public declaration in every `*Pinching*.lean` module was selected for the signature probe, including record conversion methods and downstream consumers. Appendix A contains the full printed hypotheses, not shortened signatures. In particular, universe and manifold instances, all-time versus forward-time quantifiers, measurability, noncollapse, derivative bounds, and integral assumptions remain visible there.

`GlobalRicciEigenvalueFloor3 g epsilon` means, for every point, every basis indexed by `Fin 3`, and every eigenvalue function for that basis, `epsilon * R ≤ mu i`. It is the eigenbasis formulation of the floor, not an initial-data or preservation theorem. `GlobalPinchingQuotientBound3 g kappa` means `∀ x, Q(x) ≤ kappa`. The trace/rpow definitions are total Lean functions, but the analytic comparisons require positive scalar curvature.

### 1.2 What the three preservation results actually say

The basic preservation theorems are in `ScalarEvolution.lean`. Their geometric ambient assumptions are a smooth charted `n`-manifold with T2 topology, compactness and nonemptiness, together with a C¹ Levi-Civita connection instance for each real-time slice. They accept `hn : n = 3`. Their exact additional hypotheses are as follows.

1. `hamilton_pinching_preserved`: `T ≥ 0`; joint continuity of `(tau,x) ↦ Q(gt(t0+tau),x)` on all of `ℝ × M`; spatial C² of Q at every point of the slab `tau ∈ Icc 0 T`; and `SatisfiesPinchingQuotientEvolutionAt` at every point of that slab with the actual invariant cubic motion trace. Conclusion: `pinchingMaximumTrack gt t0 tau ≤ pinchingMaximumTrack gt t0 0`. It preserves an upper bound on Q. By `ClosedSmoothRiemannianMetric.pinchingQuotientAt_sub_one_third_eq_relativeTracelessRicciAt`, this also preserves the corresponding upper bound on `U/R²`. If `Q(0) ≤ kappa`, the latter bound is `kappa-1/3`, not kappa.
2. `hamilton_eigenvalue_pinching_floor_preserved`: all the previous inputs, `epsilon ≤ 1/3`, scalar positivity throughout the slab, and an eigenbasis floor at time t0. Conclusion: the eigenbasis floor with coefficient `2*epsilon-1/3` throughout the slab. There is no hypothesis `epsilon>0` in this theorem; a positive output requires `epsilon>1/6`. It does not prove preservation of an arbitrary positive initial coefficient unchanged.
3. `hamilton_pinching_improvement`: `T ≥ 0`; `0<epsilon≤1/3`; `0≤delta≤pinchedTracelessAdmissibleDelta3 epsilon`; all-real-time joint continuity of F_delta; spatial C² of F_delta on the slab; `SatisfiesTracelessPinchingImprovementEvolutionAt` on the slab; and the epsilon eigenbasis floor on every slab slice. Conclusion: the maximum of F_delta is at most its initial maximum. This is an upper bound, not convergence to zero or a uniform decay rate. Although the explicit delta premise is nonnegative, the evolution predicate itself requires `0<delta≤1` and `R>0`.

`hamilton_pinching_preserved_continuousOn` and `hamilton_pinching_improvement_continuousOn` in `MetricFlowJointPinchingEvolution.lean` replace the all-time continuity premise by continuity on `Icc 0 T ×ˢ univ`. These are the right maximum principles for a forward-only flow. There is no corresponding public continuousOn eigenvalue theorem in the searched source; its proof can be assembled from ordinary preservation and `ClosedSmoothRiemannianMetric.eigenvalue_pinched_of_pinchingQuotientAt_le`.

The automatic `hamilton_pinching_preserved_of_ricciFlow_joint_metric_entries_three` and improvement counterpart assume **unnormalized** `IsClosedRicciFlowSolutionAt` on the slab, joint C³ entries there, and scalar positivity there. The improvement counterpart also assumes the slab eigenvalue floor and `0<delta≤1` with the admissible bound. Their `_global_joint_metric_entries_three` variants require all-time joint C³ entries and all-time scalar positivity, while still only requiring the unnormalized flow equation on the slab. None can be applied by substituting the normalized flow predicate.

`hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor` packages these implications for an initial `1/4` floor. It still takes both quotient evolution predicates and both joint/spatial regularity inputs. Its output floor is `1/6`; it requires `0<delta≤2/9`. The initial Ricci quotient bound `3/8` follows from the initial floor. The word “normalized” in the containing filename does not discharge its evolution hypotheses.

### 1.3 Which evolution and regularity inputs are automatic

Here A means bounded assembly from landed mathematical results. “Landed” means a public declaration already proves the claim. “Missing producer” means that the searched source does not provide the implication; it is not an assertion of logical independence.

| Input | Status from forward normalized flow and all-time joint C³ entries |
| --- | --- |
| C¹ connection on each slice | Landed instance `Poincare.LeviCivitaExistence.closedLeviCivitaConnection_contMDiff`. No extra analytic premise. |
| Global Lichnerowicz assembly | Landed `globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree`. |
| Normalized scalar evolution | Landed `satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz`. The flow equation is needed only on the slice being used. |
| Lower-Ricci evolution | Landed `satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three`. Joint C³ entries and the normalized equation on that slice suffice. The spatially constant metric scaling contributes zero to the lower tensor evolution. |
| Ricci-norm motion trace | Landed `ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization`: the cubic motion trace acquires `-(4/3) r N`. |
| Absolute U evolution | Landed `hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries`. It gives the exact ordinary time derivative, including at time zero. |
| Joint scalar and N continuity | Landed joint-metric continuity results; the Q and F_delta continuity theorems additionally require nonzero or positive R at the point. |
| Spatial C² scalar and U | Landed normalized-flow regularity; see `scalarAt_contMDiffAt_two_of_normalizedRicciFlow` and `contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three`. |
| Spatial C² Q | A: normalized Ricci entries and scalar C², then the generic `contMDiffAt_two_ricciNormSqAt_of_ricci_entries` and `contMDiffAt_two_pinchingQuotientAt`. Scalar positivity supplies the nonzero denominator. |
| Spatial C² F_delta | Landed `contMDiffAt_two_tracelessPinchingAt_of_normalizedRicciFlow_joint_metric_entries_three`; requires positive scalar on the slice. |
| `SatisfiesPinchingQuotientEvolutionAt` with invariant cubic | A, missing normalized producer. The landed `_of_ricciFlow_joint_metric_entries_three_cubic` producer requires the unnormalized equation. In the normalized quotient calculation, `-(4/3)rN` and the contribution of `-(2/3)rR` cancel. |
| `SatisfiesTracelessPinchingImprovementEvolutionAt` with invariant cubic | A, missing normalized producer. The remaining normalization correction is `-(2/3)delta*r*F_delta`. It can be dropped when `r≥0`, which follows from positive scalar on the compact slice. The predicate also requires `0<delta≤1`. |
| Positive scalar at every finite forward time | A from the landed primitive/profile construction and initial pointwise positivity. The proof inside `meanScalar_lower_profile_of_initial_scalar_pos` already constructs the pointwise exponential comparison before integrating it. No uniform ray floor is claimed. |

The quotient predicates are inequalities with an existential ordinary derivative witness. The ordinary predicate contains Laplacian, drift, completed-gradient damping and cubic remainder. The improved predicate contains Laplacian, drift and improved reaction; it does not contain the older full-gradient damping expression. The last gradient contribution is bounded by `ClosedSmoothRiemannianMetric.tracelessPinchingGradientNumerator3At_nonpos`. The full definitions and the lower-Ricci predicate are printed in Appendix B.

### 1.4 Every module with Pinching in its name

The table describes the role of every matching module at this base. Appendix A probes **all** its public theorem/definition/structure declarations, including all their extra hypotheses.

| Module in `Poincare/Global` | What it proves or retains |
| --- | --- |
| `MetricFlowJointPinchingEvolution` | Spatial and joint regularity; automatic unnormalized quotient evolution; slab-local preservation and improvement. |
| `NormalizedFlowJointPinchingRegularity` | Normalized-flow spatial scalar, U and improved-quotient regularity. It does not supply quotient time evolution. |
| `NormalizedFlowFiniteTimeHamiltonPinching` | Eigenfloor and quotient predicates; initial `1/4` algebra; conditional forward `1/6` preservation and improvement; entry-time selection from finite absolute dissipation and concentration controls. |
| `NormalizedFlowHamiltonPinchingQuotientFromEigenFloor` | `GlobalPinchingQuotientBound3 g (1-4epsilon+6epsilon²)` from scalar positivity and the global eigenfloor; positivity of that quadratic coefficient. |
| `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination` | Exact cubic coefficient, normalization gap, quotient/scalar-mean sufficient condition, and exponential/finite-energy consumers. The positive gap is an input. |
| `NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay` | Derives a quotient bound and some scalar/mean factor from a compact realization plus an already positive mean floor. Its analytic record separately requires a positive coefficient gap; its rate is gap times mean floor. It does not remove P2. |
| `NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay` | The analogous conditional tail construction and finite-head/tail energy assembly. Tail domination does not assert P1 on all of `Ici 0`. |
| `NormalizedFlowFiniteTimeMeanScalarPinching` | Finite-time entry into a `1/4` pinched slice from finite absolute dissipation, mean lower bounds and concentration/derivative controls. It already assumes inputs unavailable from initial pinching alone. |
| `NormalizedFlowImprovedPinchingDecay` | Relates Q minus `1/3`, relative U and F_delta; derives relative decay from a scalar profile tending to infinity, or decay of an antitone improved maximum from its integrability. A bounded or exponentially decreasing lower profile is not a profile tending to infinity. |
| `NormalizedFlowImprovedPinchingSubsequenceDecay` | An antitone maximum tends to zero from suitable samples; sample generation retains finite dissipation, derivative and noncollapse hypotheses. |
| `NormalizedFlowImprovedPinchingSampleScalarFloorDecay` | Replaces an everywhere scalar floor by an eventual floor along samples; still needs the samples/decay and antitone controls. |
| `NormalizedFlowPinchingLimit` | Selects a positive Einstein limit from the appropriate compactly realized invariant pairs and relative/absolute pinching convergence. It does not produce the convergence or positive limiting scalar floor from initial pinching. |

All this Ricci-flow material is in the repository. The targeted search in pinned Mathlib found none of the named flow/pinching/energy predicates. Mathlib supplies the ordinary derivative, integral monotonicity, rpow, compactness, and mean-value machinery. Its `monotoneOn_of_deriv_nonneg`, `MeasureTheory.integral_mono`, and `MeasureTheory.integral_const_mul` are separately probed.

## 2. Exact algebra for P1, rates, and the infinite ray

### 2.1 The sign is attached to the quotient reaction

The definitions give

```text
CubicN = 10 R N - 2 R³ - 8 tr(Ric³)
T      = CubicN - (4/3) R N
       = (26/3) R N - 2 R³ - 8 tr(Ric³)
A_norm = -2 |∇Ric|² + (2/3)|∇R|² + T - (4/3) r U.
```

Here T is the exact `pinchingTracelessRicciReactionTrace3At` applied to `pinchingRicciNormReactionMotionTraceCubicAt`. The contraction estimate `scalarGradNormSqAt_le_three_covRicciNormSqAt` makes the first two terms nonpositive. Consequently the landed cubic-domination theorem turns `T ≤ ((4/3)r-rate)U` into P1 pointwise. It does not prove its cubic premise from pinching.

The task's proposed negative raw-U reaction is not the statement proved by `TracelessPinchingEigenvalueImprovementLemma3_holds`. At eigenvalues `(1,2,2)`, `R=5`, `N=9`, `U=2/3`, and `T=4>0`. These values are compiler-checked against the repository's diagonal definitions in Appendix D. More strongly, the eigenvalues `(1,9/2,9/2)` have epsilon `1/10`, `R=10`, and

```text
T - (4/3) * 10 * U = 196/9 > 0.
```

Thus even setting the mean equal to this scalar does not give a negative **cubic-minus-normalization** expression for arbitrary positive pinching. These are algebraic counterexamples to the proposed coefficient implication. They are not claims that these numbers, together with zero covariant derivatives, have been realized by a closed simply connected flow; the full A_norm also contains gradient terms.

The exact landed admissibility function is

```text
delta_max(epsilon) = 6 epsilon² / (1 - 2epsilon + 3epsilon²).
```

For `0<epsilon≤1/3`, `0≤delta≤delta_max`, positive R, and the epsilon eigenbasis floor, the landed `pinchingTracelessRicciReactionTrace3At_le_two_mul_two_sub_delta_mul_ricciNorm_div_scalar_mul_traceless` gives

```text
T ≤ 2(2-delta) (N/R) U.
```

Subtracting the denominator reaction of `U/R²` gives instead

```text
T - 4(N/R)U ≤ -2delta(N/R)U ≤ -(2delta/3) R U.
```

The second inequality uses `N≥R²/3`, `R>0` and `U≥0`. This identifies precisely the negative term: the scalar-normalized quotient reaction, not T. With the largest admissible delta its coefficient `2delta/3` is `4epsilon²/(1-2epsilon+3epsilon²)`. The landed form is quadratic in epsilon near zero; it is not an unnamed positive constant times epsilon for the raw U reaction.

The source comments identify this as the Hamilton section-10 improved pinching algebra. A web lookup confirmed the paper's contents separate pinching, scalar-ratio control, normalized estimates and exponential convergence. The publisher's PDF body was unavailable in this session, so no uninspected sentence in section 10 is used as a proof. The coefficient conclusions above come from Lean's definitions and probes, not a historical attribution. [Hamilton paper DOI](https://doi.org/10.4310/jdg/1214436922); [accessible contents-page reproduction](https://www.studocu.com/en-us/document/university-of-california-berkeley/algebraic-topology/three-manifolds-with-positive-ricci-curvature/100981781).

### 2.2 Exactly what the landed P1 bridge needs

There are two useful sufficient conditions already proved in `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean`.

The direct coefficient gap is

```lean
2 * (2 - delta) * g.ricciNormSqAt x / g.scalarAt x + rate ≤
  (4 / 3 : ℝ) * meanScalar g
```

Together with the epsilon/delta/scalar/eigenfloor hypotheses above, it yields the desired pointwise reaction bound. Rate need not be positive for this pointwise implication; P1 and S6 require positivity and one common rate for the entire ray.

Alternatively assume `0≤delta≤2`, `Q≤kappa`, `0≤kappa`, and `R≤C*r`. Define

```text
gamma = 4/3 - 2(2-delta) kappa C.
```

If `r(t)≥c>0` on the ray and `gamma>0`, the exact uniform choice is

```text
rate = gamma*c > 0.
```

This is the landed global domination/record rate, and `constantRateFromGap` compiles its existential P1 form in Appendix C. If P2 comes from S9, one can take `c=meanScalar(gt 0)` exactly. If the only scalar comparison is `R≤S` and `r≥c`, then `C=S/c` gives the sufficient rate `(4/3)c-2(2-delta)kappa*S`, which must be strictly positive. Merely knowing that S is finite does not prove this inequality.

A pointwise floor `R≥rho>0` can imply the required mean floor, but is not needed by the quotient/scalar-mean bridge if a positive mean floor is supplied directly. Conversely, a pointwise scalar floor alone does not control the upper cubic coefficient relative to r. No universally positive P1 rate follows from that floor and arbitrary positive epsilon by these landed inequalities.

Preserve the better initial quotient coefficient when applying the lossy eigenfloor theorem. An initial epsilon0 floor gives `kappa0=1-4epsilon0+6epsilon0²` and a later epsilon `2epsilon0-1/3`. Recomputing kappa from the smaller later epsilon unnecessarily worsens the estimate. Even the better choice has a boundary: epsilon0 `1/4` gives epsilon `1/6`, kappa0 `3/8`, and delta at most `2/9`. At delta `2/9` and `C=1`, gamma is exactly zero. For smaller delta or larger C it cannot be positive. On any positive-scalar slice an all-point comparison `R≤C*r` forces `C≥1` by integration. Thus this specific landed `1/4 → 1/6` chain cannot furnish a positive coefficient gap on its own. Stronger quantitative pinching or a sharper evolution/decay argument is needed. This does not invalidate its non-strict pinching conclusions.

### 2.3 What S6 consumes

The full signature of `normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici` is printed in Appendix A. In addition to the dimension-three ambient instances and nonemptiness, it takes:

- the normalized flow equation on `Ici 0`;
- the moving-volume derivative on `Ici 0`;
- AEStrong measurability of the energy track for Lebesgue measure restricted to `Ici 0`;
- joint C³ metric entries at all real times and points;
- one real `rate>0` and the actual pointwise reaction domination with that rate everywhere on the ray.

Its conclusion is `IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)`. Its proof uses a constant-rate exponential bound and constant volume. The corresponding non-global-joint version retains additional scalar-evolution input. Neither takes a time-dependent rate. The scoped variable-rate search in these pointwise energy modules had no matches.

The pointwise profile `(rho/2)exp(-P(t))` proves positivity at every finite t and positive minima on compact time intervals. It need not have a positive infimum on `Ici 0`. Substituting it into a putative damping coefficient supplies a time-dependent lower rate only. Even a new comparison theorem with rate a(t) would need integrability of `exp(-∫₀ᵗ a)` to conclude finite energy from that bound; `a(t)>0` alone is insufficient. Even divergence of `∫a` is insufficient for integrability, as `a(t)=1/(1+t)` gives the nonintegrable envelope `1/(1+t)`. These are calculus explanations, not new geometric counterexamples.

A route through exponential decay of the relative quotient, a uniform scalar floor and a scalar upper bound could establish finite energy without proving P1 for the absolute reaction. Such a route would require its own consumer theorem. It is not an unchanged-core proof of P1, and no such substitution is made here. Likewise the landed eventual-pinching route can integrate an initial finite interval separately but does not establish the frozen all-ray P1 clause.

## 3. P2: moving integrals, energy domination, and scalar comparison

### 3.1 S9's exact inputs and what is derivable

S9 is `meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack`. It assumes a compact connected nonempty smooth 3-manifold with compatible Borel measure structure. Second countability is omitted from its own signature, though the automatic finite-atlas producers use it. It assumes, for each `t : Ici 0`, the normalized equation at `t.1`,

```lean
HasDerivAt (fun s ↦ totalScalar (gt s))
  (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1
HasDerivAt (fun s ↦ totalVolume (gt s))
  (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1
normalizedFlowScalarVarianceTrack gt t.1 ≤
  6 * normalizedFlowTracelessRicciEnergyTrack gt t.1
```

It concludes nonnegative ordinary derivative of the mean at every such time. The exact derivative is `(2E-V/3)/totalVolume`; all these definitions and `hasDerivAt_meanScalar_three_of_normalizedFlow` are probed.

The automatic prerequisites break down as follows.

1. `HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries` plus `HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound` construct finite-atlas density data from joint C³ entries. `CompactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation` converts it. Its `hasDerivAt_totalVolume_of_normalizedFlowAt` gives the required volume derivative from the normalized equation on the single slice. No scalar-energy estimate or Stokes premise is needed for this part.
2. `scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three` supplies joint continuity of the actual scalar time derivative. This is already proved in `NormalizedFlowHausdorffScalarTimeDerivativeAutomatic.lean`, stronger than the older conditional continuity report. Combined with the density data, `hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative` supplies the moving total-scalar derivative **with** `ClosedLaplacianStokes (gt t) scalarAt` and the automatically constructed Lichnerowicz package. The dominated differentiation part is landed; Stokes is the remaining geometric prerequisite of this route.
3. `FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes` is a proved supplied-geometry theorem. Its record, printed in Appendix B, includes the partition, coordinate density and metric coefficients, smooth compactly supported representatives, density/inverse-metric compatibility, and equality with the intrinsic coordinate Laplacian. The searched source has no constructor of this complete record from just the present metric/regularity assumptions. Searching its two compatibility field names found their declarations and uses only. It would be dishonest to count a theorem accepting this record as automatic Stokes.
4. `ClosedRicciFlowNormalization.continuousOn_integral_of_ricciFlow` is a continuity theorem for an **unnormalized** flow on a finite interval, with a jointly continuous test integrand. It is not the needed normalized total-scalar derivative. The normalized mean-continuity theorem in `HamiltonMeanFloorReduction.lean` uses the flow trace identity and does not require moving scalar differentiation. Neither theorem removes Stokes from the derivative-to-energy conversion.

The compiled `movingDerivatives` scratch theorem proves exactly this conjunction with Stokes still explicit. No additional integral differentiation premise remains. This is the strongest verified assembly here, rather than a proposed unconditional derivative identity.

### 3.2 What `V ≤ 6E` does and does not follow from

`V ≤ 6E` is an integrated slice inequality. It is not definitionally pointwise. The stronger pointwise condition

```lean
((gt t).scalarAt x - meanScalar (gt t)) ^ 2 ≤
  6 * (gt t).tracelessRicciNormSqAt x
```

implies it by the landed `normalizedFlowScalarVarianceTrack_le_six_tracelessRicciEnergyTrack_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq`. That theorem requires no separate slice-integrability premise because compact smoothness supplies it.

Pointwise, in terms of N and R, the exact condition is

```text
3R² - 2rR + r² ≤ 6N.
```

When R is positive it is equivalently

```text
N/R² ≥ 1/3 + (1/6)(1-r/R)².
```

Pinching instead supplies the upper bound `N/R² ≤ 1-4epsilon+6epsilon²`, along with the universal lower bound `N/R² ≥ 1/3`. Neither supplies the required stronger lower bound involving the global mean. In particular, at an isotropic point `U=0`, the pointwise condition forces `R=r`. Algebraically `(mu1,mu2,mu3)=(1,1,1)` and `r=1` satisfy every epsilon floor with `epsilon≤1/3`, but give `(R-r)²=4>0=6U`. Appendix D checks this calculation. It is a pointwise algebra test, not a construction of a globally Einstein metric with nonconstant scalar curvature.

Failure of this pointwise inference does not by itself disprove every possible integrated geometric estimate. What is absent is a proved derivation of the required `V≤6E` from this initial pinching/flow input. Such a derivation would need additional spatial or evolution analysis. No assertion of an integrated counterexample under the full flow hypotheses is made. S9 supplies the sign after that estimate is provided, not the estimate itself.

With Stokes and energy domination supplied, all the remaining work for P2 is A. `meanFloorFromEnergy` compiles the exact conclusion

```lean
0 < meanScalar (gt 0) ∧
  ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1)
```

from initial pointwise scalar positivity, normalized forward flow and global joint C³ entries. It uses the positive initial numerical scalar floor, the mean derivative identity, S9 and Mathlib's derivative criterion for monotonicity. Hence P2 holds with the precise witness `c=meanScalar(gt 0)`. Initial positive mean would suffice for this final monotonicity step, but it does not supply pointwise scalar positivity for the separate pinching route.

### 3.3 Why the scalar upper bound does not finish P2 by comparison

The normalized scalar equation is

```text
R_t = ΔR + 2N - (2/3)rR,   N≥R²/3.
```

At a spatial minimum the formal comparison inequality is `m'≥(2/3)m(m-r)`. The minimum track need not be classically differentiable; the landed maximum principle implements the argument through smooth test profiles instead. Since `r≥m`, this reaction has no uniform positive sign at the minimum.

`normalizedFlow_scalarAt_gt_of_normalization_profile` already absorbs the normalization term exactly through `phi'=-(2/3)r*phi`. The exponential primitive version does not need an upper bound on R or r for finite-time positivity. If `R≤S`, then `r≤S` and, with the primitive normalized to zero at time zero, `P(t)≤(2/3)St`. This yields at best the comparison floor `(rho/2)exp(-(2/3)St)`, which decreases toward zero for positive S.

Retaining the m² term does not repair that inference. For fixed `S>0`, `y(t)=(S/2)exp(-St/3)` is positive, bounded above by S, tends to zero, and satisfies `y'≥(2/3)y(y-S)`. The required coefficient inequality for `0≤y≤S/2` is checked in Appendix D. This demonstrates the limitation of the differential inequality, not a counterexample to the full geometric flow theorem.

The earlier mean-floor report proves positive floors on each `Icc 0 T`, with quantifiers `∀ T≥0, ∃ c_T>0`. It does not prove `∃ c>0, ∀ T≥0`. Its `not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos` also rules out reviving the globally bounded primitive as a viable residual under these hypotheses. A uniform positive mean floor forces its primitive to grow at least linearly.

For the **frozen final core**, a scalar upper bound itself follows from its retained compact K-realization and continuous third-jet profiles: the landed curvature-continuity theorem gives continuous scalar on compact `K×M`, and `exists_pos_uniform_abs_scalarAt_bound_of_compact_joint_scalar` gives a uniform positive bound S. So this is A in that context, even though obtaining such a bound for an otherwise unparameterized Ricci flow is a B analytic task. Compactness supplies no suitably small value of S, no positive lower floor, and no positive reaction gap by itself.

### 3.4 Honest residual input set

There is no demonstrated reduction of both P1 and P2 to “initial positivity plus a scalar upper bound.” A sufficient route using the current machinery retains:

- the normalized forward flow, all-time joint C³ entries, compact realization and continuous jet profiles already in the final core;
- initial pointwise scalar positivity and an initial eigenfloor strong enough for the chosen preservation route, with its explicit loss;
- a uniform quantitative cubic/normalization gap, or the scalar/mean comparison and strictly positive gamma in section 2;
- the integrated inequality `V≤6E` for S9;
- closed Laplacian Stokes on the forward slices, or actual supplied subordinate geometry proving it.

The last item is a geometric-library prerequisite, not a new Hamilton pinching estimate. It remains explicit because the unconditional producer was not found. Once it is supplied, differentiation, S9-to-floor and gap-to-rate assembly are compiler-verified A work. A future proof of scalar comparison or convergence may replace the energy-domination route entirely, but must state and prove its own uniform floor. Existence of an initially positively pinched metric on every manifold in the universal core also remains an existence obligation; this conditional survey does not settle it.

## 4. Numbered A plan and the exact further-core boundary

### 4.1 Shared dispatch and verification contract

The base for the first implementation is `c46220fb2dea444a71cfdca3764dcb0370a2afee`. After an item lands, freeze a new exact base containing it before dispatching dependent work. Do not invent future commit hashes. Each item below owns only its proposed new module. All existing Lean files, the root import, contracts, audits, missions, ledgers and this survey's evidence remain read-only unless the orchestrator explicitly changes the task scope.

For each proposed module, the acceptance gate is `LEAN_NUM_THREADS=1 lake env lean <module>`, the task's forbidden-token search with empty output, dependency printing for every new declaration with exactly the three allowed dependencies, and `git diff --check`. Compile the displayed target against the implementation. A type-checked proposition is not a proof of it. Items 1, 2 and 4 below are plans with checked target propositions; item 3 has a complete scratch proof. Appendix C distinguishes these and preserves every failed probe. No full build is needed for this report; integration remains the orchestrator's job.

The common context is the dimension-three context in `targets.lean` in Appendix C: T2, second countable, compatible measurable/Borel, smooth charted, compact connected simply connected M. No extra connection instance is assumed in the proposed targets; the landed instance supplies it. The target probe uses `autoImplicit false`.

### 4.2 Item 1: normalized quotient evolution

Proposed file: `Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Imports: `NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay`, `NormalizedFlowJointPinchingRegularity`, and the joint Lichnerowicz/scalar evolution dependencies already exposed there.

Objective: from all-time joint C³ entries, the normalized equation on one slice, and positive scalar on that slice, prove the existing ordinary quotient evolution predicate with the invariant cubic trace. Under `0<delta≤1`, prove the existing improved predicate too. These are the first two proposition probes in `targets.lean`; neither is a currently landed normalized producer.

Use the landed lower-Ricci evolution and cubic-minus-normalization motion identity for N; the normalized scalar identity for R; and the exact U evolution for the improved quotient. Apply `ClosedSmoothRiemannianMetric.hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm` and `ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm`. Reuse the public spatial quotient expansion, improved numerator bridge and gradient sign lemmas in the template probe. Normalize the ordinary scaling contribution to zero. Normalize the improved scaling contribution to `-(2/3)delta*r*F_delta`, prove it nonpositive using positive scalar and the mean lower-bound theorem, and drop it.

The unnormalized implementation contains a private quotient algebra helper. Its bare-name probe failed; it is a proof template, not a callable public API. Prove the needed short normalization identity locally rather than importing that private name. Existing spatial identities and gradient estimates remain unchanged.

Stop only when both existing predicates are constructed at their checked types without a raw evolution premise, or report the exact resisting derivative/spatial identity. Do not replace the normalized scalar equation by the unnormalized one or add negative-time flow hypotheses.

### 4.3 Item 2: forward preservation from initial data

Proposed file: `Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean`.
Imports: item 1, `MetricFlowJointPinchingEvolution`, `HamiltonMeanFloorReduction`, and `NormalizedFlowHamiltonPinchingQuotientFromEigenFloor`.

Objective: prove the third target in `targets.lean`: initial scalar positivity, initial epsilon0 floor with `epsilon0≤1/3`, forward normalized flow and all-time joint C³ imply, on every forward slice,

```lean
GlobalRicciEigenvalueFloor3 (gt t) (2 * epsilon0 - 1/3) ∧
GlobalPinchingQuotientBound3 (gt t) (1 - 4 * epsilon0 + 6 * epsilon0^2)
```

First expose the pointwise exponential scalar profile already constructed inside the landed mean-profile proof. Construct spatial C² Q and continuity on each slab from the generic regularity theorems. Apply item 1 and `hamilton_pinching_preserved_continuousOn`. Bound the initial maximum using the initial eigenvalue algebra. Convert the preserved Q bound back through `eigenvalue_pinched_of_pinchingQuotientAt_le`, exactly as the original eigenfloor proof does. This avoids falsely requiring scalar positivity at negative times.

The exact improved-preservation target is also checked in `residuals.lean`. For improved preservation, take the positive later epsilon `2epsilon0-1/3`, require the admissible delta and `0<delta≤1`, then use item 1 and `hamilton_pinching_improvement_continuousOn` on each slab. Record an upper bound, not convergence to zero. This improved maximum result is optional for the core adapter in item 4, which only needs the pointwise eigenvalue algebra; it is included to close the task's inventory-to-flow interface.

Stop with the exact degraded constant and initial quotient coefficient. Preserving epsilon0 unchanged for arbitrary small positive epsilon0 is a different tensor maximum-principle task and is not claimed A here. A nonpositive degraded floor cannot be fed into the improved pinching lemma.

### 4.4 Item 3: S9 mean floor with its actual geometric prerequisites

Proposed file: `Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean`.
Imports: `HamiltonChartDensityLocalDomination`, `HamiltonMeanFloorReduction`, `NormalizedFlowHausdorffScalarTimeDerivativeAutomatic`, `NormalizedFlowHausdorffScalarDominationJointC1Reduction`, and `NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination`.

Objective: prove `movingDerivatives` and `meanFloorFromEnergy` at the exact signatures and proof bodies in Appendix C. The latter conclusion is the positive initial mean and its forward lower-bound property. The permitted residuals are `ClosedLaplacianStokes` on each forward slice and the integrated energy domination. Neither is hidden in a larger record.

The proof already compiles against this base: construct finite-atlas density data, differentiate volume, use automatic scalar-derivative joint continuity and supplied Stokes for total scalar, apply S9, and use the mean-value monotonicity criterion. The initial numerical scalar floor gives positive initial mean. This is one substantive module that removes the two derivative premises from the mean-floor boundary, with the Stokes exception recorded explicitly.

Stop with the exact `meanScalar(gt 0)` witness and no all-negative-time flow equation. Do not label Stokes automatically proved without constructing it. The separate Stokes producer is an open library task: the exact resisting definition is `ClosedLaplacianStokes g f`, namely integrability of the intrinsic Laplacian and its zero integral. The supplied-geometry record and both compatibility fields are probed. This survey does not assign that unverified constructor a bounded A completion estimate.

### 4.5 Item 4: a checked sufficient core adapter

Proposed file: `Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`.
Imports: items 2 and 3, `HamiltonReactionCoreFinal`, and `NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination`.

Objective: the final proposition in `targets.lean`, printed in full in Appendix C, must imply the unchanged `HamiltonReactionCore3Final.{u,v} M`. It retains the original K, topology, compactness, metric family, parameter, realization equality, forward equation, joint C³ entries and third-jet profile continuity. In place of P1/P2 it takes initial pointwise scalar positivity, an initial epsilon0 eigenfloor with `1/6<epsilon0≤1/3`, `0<delta≤1`, admissibility for `2epsilon0-1/3`, forward Stokes and energy domination, plus the comparison/gap below.

Set `epsilon=2epsilon0-1/3`, `kappa=1-4epsilon0+6epsilon0²`, `c=meanScalar(gt 0)`, `gamma=4/3-2(2-delta)kappa*C`, and `rate=gamma*c`. Item 2 gives epsilon and kappa on every forward slice; item 3 gives c; the landed global reaction bridge gives rate. The scratch `constantRateFromGap` proves this last existential conversion. Preserve all original existential witnesses when constructing the final core. The sole new work after prerequisites is the mathematical input reduction, not another endpoint alias.

The exact B estimate statements used by this sufficient route are these checked expressions, with the predicates expanded in Appendix B:

```lean
-- energy domination, indexed by the forward subtype
∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
  6 * normalizedFlowTracelessRicciEnergyTrack gt t.1

-- quantitative scalar-to-mean comparison and coefficient gap
(∀ t ∈ Ici (0 : ℝ), ∀ x,
  (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
0 < (4/3 : ℝ) - 2 * (2-delta) * kappa * C

-- separately retained geometric-library prerequisite
∀ t ∈ Ici (0 : ℝ),
  ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)
```

A weaker sufficient algebraic residual for P1, avoiding the quotient/comparison overestimate but retaining a constant positive eta, is also checked:

```lean
∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
  2 * (2-delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
    (4/3 : ℝ) * meanScalar (gt t)
```

Use the initial-data preservation and positive-scalar inputs with it; it yields P1 with `rate=eta`. The complete positive-existential residual is checked in `residuals.lean`, as is the comparison/gap conjunction. No theorem derives this residual or the energy inequality from initial pinching in this report. Replacing it by an unbounded-time exponential lower profile is not valid. This sufficient adapter is stronger than the frozen core and is not asserted equivalent to it or universally inhabited.

First missing public assembly is item 1's normalized quotient predicate. After that A work, the first missing Hamilton estimate for P1 is the strict uniform normalization gap; for P2 via S9 it is `V≤6E`, with Stokes still a separately explicit library prerequisite. These are the exact stop boundaries, rather than a claim that “pinching implies decay.”

### 4.6 Verification and next action

The initial worktree was clean on the task's named branch and exact base. The worktree inventory included the main checkout and other worker branches; none was edited. The README, HANDOFF top section, project map, task contract, requested report sections, current core, Pinching module sources/imports and relevant moving-integral modules were inspected. The legacy handoff's dates were not used as proof of current declarations.

The final successful signature probe checks 257 declarations across all 12 matching Pinching modules plus 11 additional context modules and selected declarations from ScalarEvolution, ScalarVariation and RicciNorm. Support and template probes expand the exact core/predicates and check additional calculus/assembly lemmas. Proposed statements and all arithmetic checks elaborate. The three named scratch proofs elaborate and print the required dependency lists. Their unused-section-variable warnings are retained in the log. No repository Lean source was introduced.

Every Lean invocation in this attempt is recorded below, including failed option/name probes. The forbidden-token scans are empty with exit 1 as expected. The report whitespace gate exits 0. No root build, completion check, service operation, or acceptance/merge action was run for this report-only task.

First action for the orchestrator: independently reproduce Appendix C's `partial-dependencies.lean` in `/tmp` and run `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-pinching-to-reaction-survey/partial-dependencies.lean` against the recorded base. Then dispatch item 1 with the exact normalized predicates, and retain Stokes, energy domination and the strict coefficient gap as explicit unresolved inputs.


## Appendix C. Proposed targets and strongest compiled partial reductions

`targets.lean` and `residuals.lean` check proposition expressions only. They do not prove items 1, 2 or 4. `partial.lean` contains three complete proofs; `partial-dependencies.lean` repeats those exact proofs and prints their dependencies. No scratch declaration was installed into the repository.

### Proposed theorem-shaped targets



Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-pinching-to-reaction-survey/targets.lean`. Exit: 0.

```lean
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
set_option pp.universes false
open Poincare
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

#check (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ),
  (∀ s x, MetricEntriesJointContDiffAt gt s x 3) →
  (∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt t).scalarAt x) →
  ∀ x, ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
    gt t x ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
#check (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t delta : ℝ),
  (∀ s x, MetricEntriesJointContDiffAt gt s x 3) →
  (∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt t).scalarAt x) → 0 < delta → delta ≤ 1 →
  ∀ x, ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
    gt t x delta ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x))
#check (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon : ℝ),
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) → epsilon ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
  ∀ t ∈ Ici (0 : ℝ),
    GlobalRicciEigenvalueFloor3 (gt t) (2 * epsilon - 1/3) ∧
    GlobalPinchingQuotientBound3 (gt t) (1 - 4 * epsilon + 6 * epsilon^2))
#check (fun (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (delta eta : ℝ) ↦
  ∀ t ∈ Ici (0 : ℝ), ∀ x,
    2 * (2 - delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
      (4/3 : ℝ) * meanScalar (gt t))
#check (fun (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) ↦
  ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
    6 * normalizedFlowTracelessRicciEnergyTrack gt t.1)
#check (fun (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) ↦
  ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
#check (∀ (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (epsilon delta C : ℝ),
  Continuous parameter →
  (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) →
  (∀ slot : MetricEntryThirdJetSlot 3 M,
    Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2)) →
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) →
  1/6 < epsilon → epsilon ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
  0 < delta → delta ≤ 1 →
  delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) →
  (∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) →
  (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
    6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) →
  0 < (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C →
  HamiltonReactionCore3Final.{u,v} M)
```

Actual output:

```text
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ),
  (∀ (s : ℝ) (x : M), MetricEntriesJointContDiffAt gt s x 3) →
    (∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt t).scalarAt x) →
        ∀ (x : M),
          ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t x
            ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) : Prop
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t delta : ℝ),
  (∀ (s : ℝ) (x : M), MetricEntriesJointContDiffAt gt s x 3) →
    (∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt t).scalarAt x) →
        0 < delta →
          delta ≤ 1 →
            ∀ (x : M),
              ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt t x delta
                ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) : Prop
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon : ℝ),
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt 0).scalarAt x) →
        epsilon ≤ 1 / 3 →
          GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
            ∀ t ∈ Ici 0,
              GlobalRicciEigenvalueFloor3 (gt t) (2 * epsilon - 1 / 3) ∧
                GlobalPinchingQuotientBound3 (gt t) (1 - 4 * epsilon + 6 * epsilon ^ 2) : Prop
fun gt delta eta =>
  ∀ t ∈ Ici 0,
    ∀ (x : M),
      2 * (2 - delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        4 / 3 * meanScalar (gt t) : (ℝ → ClosedSmoothRiemannianMetric 3 M) → ℝ → ℝ → Prop
fun gt =>
  ∀ (t : ↑(Ici 0)),
    normalizedFlowScalarVarianceTrack gt ↑t ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt ↑t : (ℝ → ClosedSmoothRiemannianMetric 3 M) → Prop
fun gt =>
  ∀ t ∈ Ici 0, ClosedLaplacianStokes (gt t) fun x => (gt t).scalarAt x : (ℝ → ClosedSmoothRiemannianMetric 3 M) → Prop
∀ (K : Type v) [inst : TopologicalSpace K] [CompactSpace K] (metric : K → ClosedSmoothRiemannianMetric 3 M)
  (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (parameter : ↑(Ici 0) → K) (epsilon delta C : ℝ),
  Continuous parameter →
    (∀ (t : ↑(Ici 0)), metric (parameter t) = gt ↑t) →
      (∀ (slot : MetricEntryThirdJetSlot 3 M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2) →
        (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
          (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
            (∀ (x : M), 0 < (gt 0).scalarAt x) →
              1 / 6 < epsilon →
                epsilon ≤ 1 / 3 →
                  GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
                    0 < delta →
                      delta ≤ 1 →
                        delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1 / 3) →
                          (∀ t ∈ Ici 0, ClosedLaplacianStokes (gt t) fun x => (gt t).scalarAt x) →
                            (∀ (t : ↑(Ici 0)),
                                normalizedFlowScalarVarianceTrack gt ↑t ≤
                                  6 * normalizedFlowTracelessRicciEnergyTrack gt ↑t) →
                              (∀ t ∈ Ici 0, ∀ (x : M), (gt t).scalarAt x ≤ C * meanScalar (gt t)) →
                                0 < 4 / 3 - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon ^ 2) * C →
                                  HamiltonReactionCore3Final M : Prop
```

### Complete residual statements and improved preservation target



Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-pinching-to-reaction-survey/residuals.lean`. Exit: 0.

```lean
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
set_option pp.universes false
open Poincare
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]


#check (fun (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (delta : ℝ) ↦
  ∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
    2 * (2-delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
      (4/3 : ℝ) * meanScalar (gt t))
#check (fun (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (delta kappa C : ℝ) ↦
  (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
  0 < (4/3 : ℝ) - 2 * (2-delta) * kappa * C)
#check (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon0 delta : ℝ),
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) →
  1/6 < epsilon0 → epsilon0 ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon0 →
  0 < delta → delta ≤ 1 →
  delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon0 - 1/3) →
  ∀ t ∈ Ici (0 : ℝ), tracelessPinchingMaximumTrack gt 0 delta t ≤
    tracelessPinchingMaximumTrack gt 0 delta 0)
```

Actual output:

```text
fun gt delta =>
  ∃ eta,
    0 < eta ∧
      ∀ t ∈ Ici 0,
        ∀ (x : M),
          2 * (2 - delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
            4 / 3 * meanScalar (gt t) : (ℝ → ClosedSmoothRiemannianMetric 3 M) → ℝ → Prop
fun gt delta kappa C =>
  (∀ t ∈ Ici 0, ∀ (x : M), (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
    0 < 4 / 3 - 2 * (2 - delta) * kappa * C : (ℝ → ClosedSmoothRiemannianMetric 3 M) → ℝ → ℝ → ℝ → Prop
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon0 delta : ℝ),
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt 0).scalarAt x) →
        1 / 6 < epsilon0 →
          epsilon0 ≤ 1 / 3 →
            GlobalRicciEigenvalueFloor3 (gt 0) epsilon0 →
              0 < delta →
                delta ≤ 1 →
                  delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon0 - 1 / 3) →
                    ∀ t ∈ Ici 0,
                      tracelessPinchingMaximumTrack gt 0 delta t ≤ tracelessPinchingMaximumTrack gt 0 delta 0 : Prop
```

### Compiled conditional reductions



Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-pinching-to-reaction-survey/partial.lean`. Exit: 0.

```lean
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
set_option pp.universes false
open Poincare
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.PinchingReactionSurvey
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem movingDerivatives
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t) := by
  obtain ⟨D⟩ := HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
    gt hjoint (HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint)
  let V := D.toChartFrameDensityVariation
  constructor
  · intro t ht
    exact V.hasDerivAt_totalVolume_of_normalizedFlowAt t (hflow t ht)
  · intro t ht
    exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
      V hjoint (scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three hjoint)
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
      t (hflow t ht) (hstokes t ht)

theorem meanFloorFromEnergy
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
  obtain ⟨rho, hrho, hlower⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  exact ⟨meanScalar_pos_of_forall_scalarAt_ge (gt 0) hrho hlower,
    fun t ↦ hm (by simp) t.2 t.2⟩

theorem constantRateFromGap
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {epsilon delta kappa C c : ℝ}
    (he : 0 < epsilon) (he3 : epsilon ≤ 1 / 3)
    (hd : 0 ≤ delta) (hd2 : delta ≤ 2)
    (hadm : delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hk : 0 ≤ kappa) (hc : 0 < c)
    (hgap : 0 < (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C)
    (hr : ∀ t ∈ Ici (0 : ℝ), c ≤ meanScalar (gt t))
    (hR : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hpin : ∀ t ∈ Ici (0 : ℝ), GlobalRicciEigenvalueFloor3 (gt t) epsilon)
    (hq : ∀ t ∈ Ici (0 : ℝ), GlobalPinchingQuotientBound3 (gt t) kappa)
    (hcompare : ∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x := by
  let gamma : ℝ := (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C
  refine ⟨gamma * c, mul_pos hgap hc, ?_⟩
  intro t ht
  exact normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
    (gt t) he he3 hd hd2 hadm hk (hR t ht) (hpin t ht) (hq t ht)
    (hcompare t ht) (mul_le_mul_of_nonneg_left (hr t ht) hgap.le)
end Poincare.PinchingReactionSurvey
```

Actual output:

```text
/tmp/hamilton-pinching-to-reaction-survey/partial.lean:38:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-pinching-to-reaction-survey/partial.lean:82:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.constantRateFromGap`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Dependency verification for all named scratch declarations



Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-pinching-to-reaction-survey/partial-dependencies.lean`. Exit: 0.

```lean
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
set_option pp.universes false
open Poincare
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.PinchingReactionSurvey
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem movingDerivatives
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t) := by
  obtain ⟨D⟩ := HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
    gt hjoint (HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint)
  let V := D.toChartFrameDensityVariation
  constructor
  · intro t ht
    exact V.hasDerivAt_totalVolume_of_normalizedFlowAt t (hflow t ht)
  · intro t ht
    exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
      V hjoint (scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three hjoint)
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
      t (hflow t ht) (hstokes t ht)

theorem meanFloorFromEnergy
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
  obtain ⟨rho, hrho, hlower⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  exact ⟨meanScalar_pos_of_forall_scalarAt_ge (gt 0) hrho hlower,
    fun t ↦ hm (by simp) t.2 t.2⟩

theorem constantRateFromGap
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {epsilon delta kappa C c : ℝ}
    (he : 0 < epsilon) (he3 : epsilon ≤ 1 / 3)
    (hd : 0 ≤ delta) (hd2 : delta ≤ 2)
    (hadm : delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hk : 0 ≤ kappa) (hc : 0 < c)
    (hgap : 0 < (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C)
    (hr : ∀ t ∈ Ici (0 : ℝ), c ≤ meanScalar (gt t))
    (hR : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hpin : ∀ t ∈ Ici (0 : ℝ), GlobalRicciEigenvalueFloor3 (gt t) epsilon)
    (hq : ∀ t ∈ Ici (0 : ℝ), GlobalPinchingQuotientBound3 (gt t) kappa)
    (hcompare : ∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x := by
  let gamma : ℝ := (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C
  refine ⟨gamma * c, mul_pos hgap hc, ?_⟩
  intro t ht
  exact normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
    (gt t) he he3 hd hd2 hadm hk (hR t ht) (hpin t ht) (hq t ht)
    (hcompare t ht) (mul_le_mul_of_nonneg_left (hr t ht) hgap.le)
end Poincare.PinchingReactionSurvey

#print axioms Poincare.PinchingReactionSurvey.movingDerivatives
#print axioms Poincare.PinchingReactionSurvey.meanFloorFromEnergy
#print axioms Poincare.PinchingReactionSurvey.constantRateFromGap
```

Actual output:

```text
/tmp/hamilton-pinching-to-reaction-survey/partial-dependencies.lean:38:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-pinching-to-reaction-survey/partial-dependencies.lean:82:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.constantRateFromGap`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.PinchingReactionSurvey.movingDerivatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.meanFloorFromEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.constantRateFromGap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

