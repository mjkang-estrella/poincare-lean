# Buffered frozen nested cutoffs: proved

Date: 2026-09-15. Base: `330ec679dc5405534c6c9486034f57183936f8f0`.
Branch: `worker/buffered-frozen-nested-cutoff`.

## Result

All three task items are proved by appending to
`Poincare/Global/BufferedFrozenParabolicSolver.lean`. The 506 original lines
are byte-for-byte unchanged. No other existing Lean file, root import, catalog,
or frozen contract was edited. This worker result awaits independent review;
it has not been merged or marked accepted.

The exact nested-cutoff cancellation is committed as `74b3c59f`. The genuine
commutator carriers and uniform cutoff bound are committed as `28db24e4`.
The final single-chart estimate and solver-existence theorem are committed as
`de7bbe4325bf7940dedeec95e2b9d453ecfc39ed`.

## Item 1: nested supports and exact cancellation

`Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoffs` constructs an
open intermediate set with compact closure, an inner smooth compact cutoff
that is one near K, and an outer smooth compact cutoff that is one on the
closure of the intermediate set. Both have values in [0,1], and the outer
support lies in the prescribed open chart target. In particular the outer
cutoff is one on the entire closed inner support.

`Poincare.BufferedFrozenParabolicSolver.nested_coefficient_agreement` proves
that the frozen matrix plus the extended coefficient equals the actual chart
coefficient on the inner support.
`Poincare.BufferedFrozenParabolicSolver.cutoff_forcing_eq` proves that the
inner cutoff preserves forcing supported in its one-set.
`Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoff_chart_residual`
uses the actual product jets from
`Poincare.ParabolicCutoffCommutator.exists_cutoff_operator` to prove that the
residual contains precisely the commutator. The weighted coefficient identity
holds on the support by agreement and off the support because the inner cutoff
vanishes. No principal mismatch remains.

## Item 2: actual commutator carriers and the constant 24

`Poincare.BufferedFrozenParabolicSolver.cutoffDrift` and
`Poincare.BufferedFrozenParabolicSolver.cutoffPotential` are the explicit
spatial coefficient functions

    beta_k(x) = -sum_j (a_jk(x) + a_kj(x)) D_j psi(x)
    c(x)      = -sum_ij a_ij(x) D_i D_j psi(x).

Both mixed terms are retained; this identity does not assume matrix symmetry.
`Poincare.BufferedFrozenParabolicSolver.cutoff_firstOrder_value` identifies
the first-order carrier with the full product-rule commutator.

`Poincare.BufferedFrozenParabolicSolver.exists_commutator_carriers` constructs
these functions in the genuine Hölder space for every time interval and chooses
one finite constant B before time such that

    sum_k ||beta_k||_Y + ||c||_Y <= B.

The proof extends the smooth entries using the outer cutoff, constructs the
smooth compact coefficient products, and proves that they equal the displayed
functions everywhere. The support of the cutoff derivatives is contained in
the cutoff support. Thus the outer extension has no effect on those functions.
The bounds come from boundedness and Lipschitz control of the compact smooth
products. They use the coefficients and their first spatial derivatives on
the buffer, along with the fixed cutoff derivatives. This is an existence
bound, not an explicit numerical formula in a named C1 norm.

`Poincare.BufferedFrozenParabolicSolver.commutator_solver_bound` proves both
requested inequalities using
`Poincare.ParabolicCutoffCommutator.firstOrder_time_bound`:

    ||[L,psi](Sf)||_Y
      <= 24 (sum_k ||beta_k||_Y T^((1-alpha)/2)
             + ||c||_Y T^(1-alpha/2)) ||Sf||_X
      <= 24 B C_S (T^((1-alpha)/2) + T^(1-alpha/2)) ||f||_Y.

`Poincare.BufferedFrozenParabolicSolver.cutoffGraph_norm_le` exposes the
explicit dependence of the product graph norm on the three cutoff carriers.
`Poincare.BufferedFrozenParabolicSolver.exists_uniform_cutoff_bound` then
chooses D before time and proves that every operator with the actual cutoff
value has norm at most D for positive time. The proof uses genuine graph
uniqueness via `Poincare.ParabolicSolutionGraph.Graph.ext_of_u`.

## Item 3: uniform single-chart error and actual solver existence

`Poincare.BufferedFrozenParabolicSolver.chartValue` is the genuine coordinate
expression for the principal variable-coefficient operator.
`Poincare.BufferedFrozenParabolicSolver.single_chart_error` chooses

    C_psi = 24 B C_S,   C' = D C_S

before T. For every T in (0,tau_0], every near-frozen solver with the specified
uniform bound and actual extended equation, and every forcing supported in K,
it constructs the cutoff operator and a bounded linear Hölder residual R with

    (R f)(p) = L_chart(psi Sf)(p) - f(p)       for every spacetime point p,
    ||R f||_Y <= C_psi (T^((1-alpha)/2) + T^(1-alpha/2)) ||f||_Y,
    ||psi Sf||_X <= C' ||f||_Y.

The pointwise identity includes times outside the cylinder, where the carriers
vanish. The norm is the actual Hölder carrier norm, and the solution norm is
the original four-component graph norm. The theorem does not substitute a
pointwise absolute-value estimate for either norm.

`Poincare.BufferedFrozenParabolicSolver.exists_small_time_interval` converts
the Hölder smallness condition into one positive time interval.
`Poincare.BufferedFrozenParabolicSolver.exists_single_chart_parametrix`
discharges the supplied-solver premise: a positive frozen matrix and smooth
entries give an oscillation threshold; cutoffs satisfying that threshold give
constants and a positive time interval on which actual bounded linear solution
and residual maps exist. Its proof constructs P as cutoff multiplication
composed with the near-frozen inverse, using
`Poincare.BufferedFrozenParabolicSolver.exists_chart_operator` and
`Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries`.
It also proves spatial support of P in the closed inner cutoff support.

For this near-frozen route, the survey's leading C0 C_S omega(rho) error term
is replaced by the small-oscillation condition required for local solver
existence. The additional Hölder smallness condition is enforced by shortening
time. Neither oscillation nor a coefficient-extension error appears in the
single-chart residual bound. This is also stated in the theorem docstrings.
Finite-atlas assembly and its transport estimates remain separate work.

## Preparation and scope

The worker read the repository instructions, task, worker-contract update,
required report and survey context, and the actual imported definitions.
Initial status was clean, and the commit and worktree inventory were checked.
The global declaration catalog was searched first. It listed the commutator,
multiplier, and compact-cutoff tools; it had no entry for the newly landed
buffered solver chain, so that module was inspected directly.

All temporary probes and failed compiler outputs remain under
`/tmp/buffered-frozen-nested-cutoff`. The failed diagnostics and final source
diff are also preserved below. Root integration and acceptance belong to the
orchestrator, so no root build or root acceptance audit was run here.

Exact next first action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Then independently review the actual appended diff against the recorded base
and rerun the module dependency audit before integration.

## Final verification

Source SHA-256: `e0f02a3674f1fa1acabb07e5e2647167ee69759630d063b3af978cb8cd85a992`.

All 101 emitted declarations have exactly `[propext, Classical.choice, Quot.sound]`. This covers all 37 new declarations, including generated declarations and local instances, as well as the 64 original declarations. The focused source command emitted no diagnostics. The module build replayed existing dependency warnings and completed successfully.

### lean

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Exit code: `0`.

```text
(empty stdout and stderr)
```

### tokens

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Exit code: `1`.

```text
(empty stdout and stderr)
```

### whitespace

```sh
git diff --check
```

Exit code: `0`.

```text
(empty stdout and stderr)
```

### build

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.BufferedFrozenParabolicSolver
```

Exit code: `0`.

Actual final five output lines are shown below. The complete 10,837-line dependency replay log is retained at `/tmp/buffered-frozen-nested-cutoff/final-build.log`.

```text
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3888/3888] Built Poincare.Global.BufferedFrozenParabolicSolver (55s)
Build completed successfully (3888 jobs).
```

### audit

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/buffered-frozen-nested-cutoff/Audit.lean
```

Exit code: `0`.

```text
'Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoffs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.nested_coefficient_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffPotential.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoff_chart_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedSpaceRealContinuousLinearMapId_poincare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedAddCommGroupContinuousLinearMapRealId_poincare_1._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedSpaceRealContinuousLinearMapId_poincare_1._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instIsBoundedSMulRealContinuousLinearMapId_poincare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedSpaceRealContinuousLinearMapId_poincare_1._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedAddCommGroupContinuousLinearMapRealId_poincare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.commutator_solver_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_forcing_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius._simp_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_uniform_cutoff_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_supremum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.single_chart_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_cutoff_chart_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.solves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedSpaceRealContinuousLinearMapId_poincare_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_small_time_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffPotential' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_firstOrder_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.S' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_single_chart_parametrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.nearFrozen_chart_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffPotential._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffDrift.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_commutator_carriers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffPotential._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.frozenCLMGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_spatial_carrier_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.instNormedAddCommGroupContinuousLinearMapRealId_poincare_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffGraph_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.chartValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_inverse_metric_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_buffered_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoffPotential._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=101
```

The token search exits 1 because it found no matches, which is the required result.

The append-only comparison against the recorded base also passed:

```text
APPEND_ONLY_CHECK passed: all 506 original lines are byte-for-byte unchanged
```

## Complete module audit source

```lean
import Poincare.Global.BufferedFrozenParabolicSolver
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.BufferedFrozenParabolicSolver
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}"
```

## Preserved failed compiler outputs

These diagnostics are from unsuccessful intermediate probes. Each failure was resolved before the final gate. Temporary probe files were not committed as project modules. In particular, the generated reverse-associativity helper was replaced with a real-scalar arithmetic proof so the exact dependency gate passes.

<details>
<summary>coefficients-01.log</summary>

```text
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:81:10: error(lean.unknownIdentifier): Unknown constant `HasCompactSupport.sum`
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:82:10: error: No goals to be solved
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:86:10: error(lean.unknownIdentifier): Unknown constant `HasCompactSupport.sum`
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:87:10: error: No goals to be solved
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:107:9: error: Tactic `rcases` failed: `right✝ : ∀ (T : ℝ),
  ∃ f, (∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = cutoffPotential A ψ p.2) ∧ ‖f‖ ≤ D` is not an inductive datatype
```

</details>

<details>
<summary>coefficients-02.log</summary>

```text
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:81:10: error(lean.unknownIdentifier): Unknown constant `Finset.hasCompactSupport_sum`
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:82:10: error: No goals to be solved
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:86:10: error(lean.unknownIdentifier): Unknown constant `Finset.hasCompactSupport_sum`
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:87:10: error: No goals to be solved
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:109:37: error: failed to prove positivity/nonnegativity/nonzeroness
```

</details>

<details>
<summary>coefficients-03.log</summary>

```text
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:83:4: error: Type mismatch: After simplification, term
  HasCompactSupport.neg (HasCompactSupport.add (h 0) (HasCompactSupport.add (h 1) (h 2)))
 has type
  HasCompactSupport
    (-((fun x => (A x 0 i + A x i 0) * (fderiv ℝ ψ x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 0)) +
        ((fun x => (A x 1 i + A x i 1) * (fderiv ℝ ψ x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 1)) + fun x =>
          (A x 2 i + A x i 2) * (fderiv ℝ ψ x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 2))))
but is expected to have type
  HasCompactSupport (cutoffDrift A ψ i)
/tmp/buffered-frozen-nested-cutoff/coefficients.lean:90:4: error: Type mismatch: After simplification, term
  HasCompactSupport.neg (HasCompactSupport.add (hh 0) (HasCompactSupport.add (hh 1) (hh 2)))
 has type
  HasCompactSupport
    (-((fun x =>
            A x 0 0 *
              ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 0))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) 0)) +
          ((fun x =>
              A x 0 1 *
                ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 0))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) 1)) +
            fun x =>
            A x 0 2 *
              ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 0))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) 2)) +
        ((fun x =>
              A x 1 0 *
                ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 1))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) 0)) +
            ((fun x =>
                A x 1 1 *
                  ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 1))
                    ((EuclideanSpace.basisFun (Fin 3) ℝ) 1)) +
              fun x =>
              A x 1 2 *
                ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 1))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) 2)) +
          ((fun x =>
              A x 2 0 *
                ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 2))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) 0)) +
            ((fun x =>
                A x 2 1 *
                  ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 2))
                    ((EuclideanSpace.basisFun (Fin 3) ℝ) 1)) +
              fun x =>
              A x 2 2 *
                ((fderiv ℝ (fderiv ℝ ψ) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) 2))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) 2))))))
but is expected to have type
  HasCompactSupport (cutoffPotential A ψ)
```

</details>

<details>
<summary>item1-01.log</summary>

```text
Poincare/Global/BufferedFrozenParabolicSolver.lean:529:54: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  hξV x hx
has type
  (𝓝 x).1 {x | (fun y => ξ y = 1) x}
which does not have the necessary form.
Poincare/Global/BufferedFrozenParabolicSolver.lean:556:86: error: unexpected token 'set_option'; expected 'lemma'
```

</details>

<details>
<summary>item1-audit.log</summary>

```text
'Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoffs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.nested_coefficient_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoff_chart_residual._simp_1_1' does not depend on any axioms
/tmp/buffered-frozen-nested-cutoff/Audit.lean:3:0: error: Unexpected foundational dependencies for Poincare.BufferedFrozenParabolicSolver.exists_nested_cutoff_chart_residual._simp_1_1: []
```

</details>

<details>
<summary>item1-compile.log</summary>

```text
Poincare/Global/BufferedFrozenParabolicSolver.lean:529:54: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  hξV x hx
has type
  (𝓝 x).1 {x | (fun y => ξ y = 1) x}
which does not have the necessary form.
Poincare/Global/BufferedFrozenParabolicSolver.lean:556:86: error: unexpected token 'set_option'; expected 'lemma'
```

</details>

<details>
<summary>single-01.log</summary>

```text
/tmp/buffered-frozen-nested-cutoff/single.lean:103:9: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

</details>

<details>
<summary>uniform-01.log</summary>

```text
/tmp/buffered-frozen-nested-cutoff/uniform.lean:22:8: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Norm (ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/buffered-frozen-nested-cutoff/uniform.lean:23:8: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Norm (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/buffered-frozen-nested-cutoff/uniform.lean:22:9: error: Type mismatch
  ContinuousLinearMap.lsmul ℝ ℝ
has type
  ℝ →L[ℝ]
    @ContinuousLinearMap ℝ ℝ Field.toSemifield.toDivisionSemiring.toSemiring
      Field.toSemifield.toDivisionSemiring.toSemiring (RingHom.id ℝ) ?m.248
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid ?m.248
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid
      NormedSpace.toModule NormedSpace.toModule
but is expected to have type
  ℝ →L[ℝ]
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid (E →L[ℝ] E →L[ℝ] ℝ)
      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid ContinuousLinearMap.module
      ContinuousLinearMap.module
/tmp/buffered-frozen-nested-cutoff/uniform.lean:113:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Norm (ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/buffered-frozen-nested-cutoff/uniform.lean:114:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Norm (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/buffered-frozen-nested-cutoff/uniform.lean:113:5: error: Type mismatch
  ContinuousLinearMap.lsmul ℝ ℝ
has type
  ℝ →L[ℝ]
    @ContinuousLinearMap ℝ ℝ Field.toSemifield.toDivisionSemiring.toSemiring
      Field.toSemifield.toDivisionSemiring.toSemiring (RingHom.id ℝ) ?m.224
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid ?m.224
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid
      NormedSpace.toModule NormedSpace.toModule
but is expected to have type
  ℝ →L[ℝ]
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid (E →L[ℝ] E →L[ℝ] ℝ)
      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid ContinuousLinearMap.module
      ContinuousLinearMap.module
```

</details>

## Final proof diff against the recorded base

<details>
<summary>Appended verified Lean declarations</summary>

```diff
diff --git a/Poincare/Global/BufferedFrozenParabolicSolver.lean b/Poincare/Global/BufferedFrozenParabolicSolver.lean
index 314a94ca..b0863a97 100644
--- a/Poincare/Global/BufferedFrozenParabolicSolver.lean
+++ b/Poincare/Global/BufferedFrozenParabolicSolver.lean
@@ -504,3 +504,536 @@ theorem exists_cutoff_chart_residual {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
   linear_combination hf'
 
 end Poincare.BufferedFrozenParabolicSolver
+
+
+noncomputable section
+open Set
+open scoped ContDiff Topology
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph
+
+/-- Two compact buffers separate the coefficient extension from the solution cutoff. -/
+theorem exists_nested_cutoffs {K U : Set (ClosedSmoothModel 3)} (hK : IsCompact K)
+    (hU : IsOpen U) (hKU : K ⊆ U) :
+    ∃ (U₁ : Set (ClosedSmoothModel 3)) (ψ ξ : (ClosedSmoothModel 3) → ℝ),
+      IsOpen U₁ ∧ IsCompact (closure U₁) ∧ closure U₁ ⊆ U ∧
+      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U₁ ∧
+      (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ψ y = 1) ∧ (∀ x, ψ x ∈ Icc 0 1) ∧
+      ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U ∧
+      (∀ x ∈ closure U₁, ξ x = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) ∧
+      (∀ x ∈ tsupport ψ, ξ x = 1) := by
+  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
+    exists_open_between_and_isCompact_closure hK hU hKU
+  obtain ⟨ψ, hψ, hcψ, hψV, hψK, hψ01⟩ := exists_buffered_cutoff hK hV hKV
+  obtain ⟨ξ, hξ, hcξ, hξU, hξV, hξ01⟩ := exists_buffered_cutoff hcV hU hVU
+  have hone : ∀ x ∈ closure V, ξ x = 1 := fun x hx => Filter.EventuallyEq.eq_of_nhds (hξV x hx)
+  exact ⟨V, ψ, ξ, hV, hcV, hVU, hψ, hcψ, hψV, hψK, hψ01,
+    hξ, hcξ, hξU, hone, hξ01, fun x hx => hone x (subset_closure (hψV hx))⟩
+
+/-- The outer extension agrees with the original entries on the inner support. -/
+theorem nested_coefficient_agreement {α T : ℝ}
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
+    (ψ ξ : (ClosedSmoothModel 3) → ℝ)
+    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) :
+    ∀ t ∈ Icc 0 T, ∀ x ∈ tsupport ψ, ∀ i j,
+      a anchor i j + b i j (t,x) = a x i j := by
+  intro t ht x hx i j
+  rw [heq t ht x i j, hnest x hx, one_mul, add_sub_cancel]
+
+/-- Support in the cutoff one-set makes multiplication preserve the forcing. -/
+theorem cutoff_forcing_eq {α T : ℝ} {K : Set (ClosedSmoothModel 3)}
+    (ψ : (ClosedSmoothModel 3) → ℝ) (hone : ∀ x ∈ K, ψ x = 1)
+    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hf : ∀ p, p.2 ∉ K → f p = 0) : ∀ p, ψ p.2 * f p = f p := by
+  intro p
+  by_cases hp : p.2 ∈ K
+  · rw [hone p.2 hp, one_mul]
+  · rw [hf p hp, mul_zero]
+
+set_option maxHeartbeats 1600000 in
+/-- Nested cutoffs remove the principal mismatch exactly. Oscillation is needed only
+for existence of the near-frozen solver; it contributes no single-chart error term. -/
+theorem exists_nested_cutoff_chart_residual {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) {ψ : (ClosedSmoothModel 3) → ℝ}
+    (ξ : (ClosedSmoothModel 3) → ℝ)
+    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1)
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j))
+    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
+      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∃ C : Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ, (∀ p, ψ p.2 * f p = f p) →
+      ∀ t ∈ Icc 0 T, ∀ x,
+        (C (S f)).ut (t,x) -
+          (∑ i, ∑ j, a x i j * (C (S f)).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
+        -(∑ i, ∑ j, a x i j *
+          (fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+            (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+            (S f).u (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) := by
+  obtain ⟨C, hu, hjets⟩ := ParabolicCutoffCommutator.exists_cutoff_operator hψ hc hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro f hf t ht x
+  obtain ⟨hut, _, hddu⟩ := hjets (S f) t ht x
+  have hweighted (i j : Fin 3) :
+      ψ x * (a anchor i j + b i j (t,x)) = ψ x * a x i j := by
+    by_cases hx : x ∈ tsupport ψ
+    · rw [nested_coefficient_agreement a anchor ψ ξ hnest b heq t ht x hx i j]
+    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
+  rw [hut, hddu, hS f t ht x]
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
+  have hmul (r s v : ℝ) : r * (s * v) = r * s * v := by ring
+  simp only [mul_add, Finset.mul_sum, hmul, hweighted]
+  have hf' := hf (t,x)
+  dsimp only at hf'
+  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at *
+  linear_combination hf'
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped ContDiff Topology
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph ParabolicCutoffCommutator
+
+/-- The explicit spatial first-order coefficients retain both terms for nonsymmetric matrices. -/
+def cutoffDrift (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ψ : (ClosedSmoothModel 3) → ℝ) (k : Fin 3) (x : (ClosedSmoothModel 3)) : ℝ :=
+  -(∑ j : Fin 3, (a x j k + a x k j) *
+    fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
+
+/-- The explicit spatial zero-order coefficient contains the cutoff Hessian. -/
+def cutoffPotential (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ψ : (ClosedSmoothModel 3) → ℝ) (x : (ClosedSmoothModel 3)) : ℝ :=
+  -(∑ i : Fin 3, ∑ j : Fin 3, a x i j *
+    fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
+      ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
+
+/-- The coefficient formula equals the full product-rule commutator. -/
+theorem cutoff_firstOrder_value {α T : ℝ}
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ψ : (ClosedSmoothModel 3) → ℝ)
+    (b : Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (c : Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hb : ∀ p ∈ cylinder T, ∀ i, b i p = cutoffDrift a ψ i p.2)
+    (hc : ∀ p ∈ cylinder T, c p = cutoffPotential a ψ p.2)
+    (G : Graph («E» := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3))
+    (hp : p ∈ cylinder T) :
+    firstOrderForcing b c G p =
+      -(∑ i : Fin 3, ∑ j : Fin 3, a p.2 i j *
+        (fderiv ℝ ψ p.2 ((EuclideanSpace.basisFun (Fin 3) ℝ) i) *
+            G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+          G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) *
+            fderiv ℝ ψ p.2 ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+          G.u p * fderiv ℝ (fderiv ℝ ψ) p.2
+            ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) := by
+  rw [firstOrderForcing_apply]
+  simp only [hb p hp, hc p hp, cutoffDrift, cutoffPotential,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+/-- Smooth coefficients on a buffered chart give genuine commutator carriers,
+with a single finite norm bound chosen before the time interval. -/
+theorem exists_commutator_carriers {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U)
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
+    {ψ ξ : (ClosedSmoothModel 3) → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hξ : ContDiff ℝ ∞ ξ) (hcξ : HasCompactSupport ξ)
+    (hξU : tsupport ξ ⊆ U) (hnest : ∀ x ∈ tsupport ψ, ξ x = 1) :
+    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ,
+      ∃ (b : Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+        (c : Y («E» := (ClosedSmoothModel 3)) α T ℝ),
+      (∀ p ∈ cylinder T, ∀ i, b i p = cutoffDrift a ψ i p.2) ∧
+      (∀ p ∈ cylinder T, c p = cutoffPotential a ψ p.2) ∧
+      (∑ i : Fin 3, ‖b i‖) + ‖c‖ ≤ B := by
+  let A := fun x i j => ξ x * a x i j
+  have hA (i j : Fin 3) : ContDiff ℝ ∞ (fun x => A x i j) :=
+    ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul hU hξ hξU (ha i j)
+  have hcA (i j : Fin 3) : HasCompactSupport (fun x => A x i j) := hcξ.mul_right
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
+  have hbsm (i : Fin 3) : ContDiff ℝ ∞ (cutoffDrift A ψ i) := by
+    apply ContDiff.neg
+    apply ContDiff.sum
+    intro j _
+    exact ((hA j i).add (hA i j)).mul (hdψ.clm_apply contDiff_const)
+  have hcsm : ContDiff ℝ ∞ (cutoffPotential A ψ) := by
+    apply ContDiff.neg
+    apply ContDiff.sum
+    intro i _
+    apply ContDiff.sum
+    intro j _
+    exact (hA i j).mul ((hddψ.clm_apply contDiff_const).clm_apply contDiff_const)
+  have hbc (i : Fin 3) : HasCompactSupport (cutoffDrift A ψ i) := by
+    have h (j : Fin 3) : HasCompactSupport (fun x => (A x j i + A x i j) *
+        fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :=
+      ((hcA j i).add (hcA i j)).mul_right
+    convert ((h 0).add ((h 1).add (h 2))).neg using 1
+    funext x
+    simp [cutoffDrift, Fin.sum_univ_succ]
+  have hcc : HasCompactSupport (cutoffPotential A ψ) := by
+    have h (i j : Fin 3) : HasCompactSupport (fun x => A x i j *
+        fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
+          ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) := (hcA i j).mul_right
+    have hh (i : Fin 3) := (h i 0).add ((h i 1).add (h i 2))
+    convert ((hh 0).add ((hh 1).add (hh 2))).neg using 1
+    funext x
+    simp [cutoffPotential, Fin.sum_univ_succ]
+  have hbval (i : Fin 3) : cutoffDrift A ψ i = cutoffDrift a ψ i := by
+    funext x
+    by_cases hx : x ∈ tsupport ψ
+    · simp [cutoffDrift, A, hnest x hx]
+    · have hd : fderiv ℝ ψ x = 0 := image_eq_zero_of_notMem_tsupport
+        (fun h => hx (tsupport_fderiv_subset ℝ h))
+      simp [cutoffDrift, hd]
+  have hcval : cutoffPotential A ψ = cutoffPotential a ψ := by
+    funext x
+    by_cases hx : x ∈ tsupport ψ
+    · simp [cutoffPotential, A, hnest x hx]
+    · have hd : fderiv ℝ (fderiv ℝ ψ) x = 0 := image_eq_zero_of_notMem_tsupport
+        (fun h => hx (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h)))
+      simp [cutoffPotential, hd]
+  have hex (i : Fin 3) := exists_cutoff_carrier (hbsm i) (hbc i) hα hα1
+  choose B hB b hb using hex
+  obtain ⟨D, hD, hexC⟩ := exists_cutoff_carrier hcsm hcc hα hα1
+  choose c hc using hexC
+  refine ⟨(∑ i : Fin 3, B i) + D, add_nonneg (Finset.sum_nonneg (fun i _ => hB i)) hD, ?_⟩
+  intro T
+  refine ⟨fun i => b i T, c T, ?_, ?_, ?_⟩
+  · intro p hp i
+    simpa only [hbval] using (hb i T).1 p hp
+  · intro p hp
+    simpa only [hcval] using (hc T).1 p hp
+  · exact add_le_add (Finset.sum_le_sum (fun i _ => (hb i T).2)) (hc T).2
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped ContDiff
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph ParabolicCutoffCommutator
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
+
+set_option maxHeartbeats 4000000 in
+/-- The product graph bound displays its dependence on the three cutoff carriers. -/
+theorem cutoffGraph_norm_le {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    ∀ G : Graph (E := E) α T,
+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ 20 * (1 +
+        ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))‖ +
+        ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))‖ +
+        ‖ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)‖) *
+        (‖f‖ + ‖df‖ + ‖ddf‖) * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
+  let A := ‖f‖ + ‖df‖ + ‖ddf‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  have hA : 0 ≤ A := by dsimp [A]; positivity
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
+  intro G
+  have hGu := norm_u_le G
+  have hGut := norm_ut_le G
+  have hGdu := norm_du_le G
+  have hGddu := norm_ddu_le G
+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  rw [ParabolicSolutionGraph.norm_eq]
+  change ‖f * G.u‖ + ‖f * G.ut‖ +
+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
+  nlinarith
+
+
+/-- Every operator with the cutoff value has a time-uniform graph norm bound. -/
+theorem exists_uniform_cutoff_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
+    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 0 < T →
+      ∀ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) → ‖C‖ ≤ D := by
+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
+  let B : ℝ := 20 * (1 +
+    ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))‖ +
+    ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))‖ +
+    ‖ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)‖)
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  refine ⟨B * K, mul_nonneg hB hK, ?_⟩
+  intro T hT C hC
+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
+  have hf := fun p hp => (heq p hp).1
+  have hdf := fun p hp => (heq p hp).2.1
+  have hddf := fun p hp => (heq p hp).2.2
+  apply ContinuousLinearMap.opNorm_le_bound C (mul_nonneg hB hK)
+  intro G
+  have hsame : C G = cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G := by
+    apply Graph.ext_of_u hT
+    apply ParabolicHolder.ext
+    intro p hp
+    change (C G).u p = f p * G.u p
+    rw [hC, hf p hp]
+  rw [hsame]
+  exact (cutoffGraph_norm_le hψ f df ddf hf hdf hddf G).trans
+    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hB) (norm_nonneg G))
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped ContDiff
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph ParabolicCutoffCommutator
+
+/-- The actual variable-coefficient principal operator, evaluated in the host frame. -/
+def chartValue {α T : ℝ} (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (G : Graph («E» := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) : ℝ :=
+  G.ut p - ∑ i : Fin 3, ∑ j : Fin 3,
+    a p.2 i j * G.ddu p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
+      ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
+
+/-- The residual carrier has the explicit coefficient estimate with constant 24. -/
+theorem commutator_solver_bound {α T C_S B : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (b : Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (c : Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hB : (∑ i : Fin 3, ‖b i‖) + ‖c‖ ≤ B)
+    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (hS : ‖S‖ ≤ C_S) (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
+    ‖firstOrderForcing b c (S f)‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖S f‖ ∧
+    ‖firstOrderForcing b c (S f)‖ ≤
+      (24 * B * C_S) * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ := by
+  have hfirst := firstOrder_time_bound b c (S f) hα hα1 hT hT1
+  refine ⟨hfirst, ?_⟩
+  have hb0 : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
+  have hB0 : 0 ≤ B := (add_nonneg hb0 (norm_nonneg c)).trans hB
+  have hbB : (∑ i : Fin 3, ‖b i‖) ≤ B := by linarith [norm_nonneg c]
+  have hcB : ‖c‖ ≤ B := by linarith
+  have hSf : ‖S f‖ ≤ C_S * ‖f‖ :=
+    (S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg f))
+  calc
+    _ ≤ 24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖S f‖ := hfirst
+    _ ≤ 24 * (B * T ^ ((1-α)/2) + B * T ^ (1-α/2)) * (C_S * ‖f‖) := by
+      apply mul_le_mul _ hSf (norm_nonneg _) (by positivity)
+      gcongr
+    _ = _ := by ring
+
+set_option maxHeartbeats 1600000 in
+/-- Uniform single-chart error for the actual near-frozen equation and nested cutoffs.
+The returned Hölder carrier evaluates to the genuine chart residual everywhere.
+Oscillation enters only the smallness conditions ensuring existence of the supplied
+near-frozen solver. There is no oscillation term in this error estimate. -/
+theorem single_chart_error {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    {U K : Set (ClosedSmoothModel 3)} (hU : IsOpen U)
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
+    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
+    {ψ ξ : (ClosedSmoothModel 3) → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
+    (hξ : ContDiff ℝ ∞ ξ) (hcξ : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ U)
+    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1) (hone : ∀ x ∈ K, ψ x = 1)
+    {C_S τ₀ : ℝ} (hCS : 0 ≤ C_S) (hτ₀ : τ₀ ≤ 1) :
+    ∃ C_ψ C' : ℝ, 0 ≤ C_ψ ∧ 0 ≤ C' ∧
+    ∀ T ∈ Ioc 0 τ₀,
+    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+      (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T),
+      ‖S‖ ≤ C_S →
+      (∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) →
+      (∀ f t, t ∈ Icc 0 T → ∀ x,
+        (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+          (a anchor i j + b i j (t,x)) * (S f).ddu (t,x)
+            ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) →
+      ∃ (C : Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+        (R : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ),
+        (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+        ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+          (∀ p, p.2 ∉ K → f p = 0) →
+          (∀ p, R f p = chartValue a (C (S f)) p - f p) ∧
+          ‖R f‖ ≤ C_ψ * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ ∧
+          ‖C (S f)‖ ≤ C' * ‖f‖ := by
+  obtain ⟨B, hB, hcarriers⟩ := exists_commutator_carriers hα hα1 hU a ha hψ hξ hcξ hξU hnest
+  obtain ⟨D, hD, hcutoff⟩ := exists_uniform_cutoff_bound hψ hcψ hα hα1
+  refine ⟨24 * B * C_S, D * C_S, by positivity, by positivity, ?_⟩
+  intro T hT b S hS heq hsolves
+  obtain ⟨C, hC, hres⟩ := exists_nested_cutoff_chart_residual hα hα1 a anchor ξ
+    hnest hψ hcψ b S heq hsolves
+  obtain ⟨β, c, hβ, hc, hbc⟩ := hcarriers T
+  let q := 24 * ((∑ i : Fin 3, ‖β i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let F := (firstOrderLinearMap β c).mkContinuous q
+    (fun G => firstOrder_common_time_bound β c G hα hα1 hT.1 (hT.2.trans hτ₀))
+  let R := F.comp S
+  have hR (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
+      R f = firstOrderForcing β c (S f) := rfl
+  refine ⟨C, R, hC, ?_⟩
+  intro f hf
+  refine ⟨?_, ?_, ?_⟩
+  · intro p
+    by_cases hp : p ∈ cylinder T
+    · rw [hR, cutoff_firstOrder_value a ψ β c hβ hc (S f) p hp]
+      exact (hres f (cutoff_forcing_eq ψ hone f hf) p.1 hp.1 p.2).symm
+    · have hut := zero_off (C (S f)).ut hp
+      have hddu := zero_off (C (S f)).ddu hp
+      simp [chartValue, zero_off (R f) hp, zero_off f hp, hut, hddu]
+  · rw [hR]
+    exact (commutator_solver_bound hα hα1 hT.1 (hT.2.trans hτ₀) β c hbc S hS f).2
+  · calc
+      ‖C (S f)‖ ≤ ‖C‖ * ‖S f‖ := C.le_opNorm _
+      _ ≤ D * (C_S * ‖f‖) := mul_le_mul (hcutoff T hT.1 C hC)
+        ((S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg f)))
+        (norm_nonneg _) hD
+      _ = _ := by ring
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped ContDiff Topology
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph
+
+/-- A positive Hölder power satisfies the solver smallness condition on a whole short interval. -/
+theorem exists_small_time_interval {α ε Λ τ : ℝ}
+    (hα : 0 < α) (hε : 0 < ε) (hτ : 0 < τ) :
+    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ τ ∧
+      ∀ T ∈ Ioc 0 δ, Λ * T ^ (α / 2) ≤ ε := by
+  have hc : ContinuousAt (fun t : ℝ => Λ * t ^ (α / 2)) 0 :=
+    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (α / 2) (Or.inr (by linarith)))
+  have hz : Λ * (0 : ℝ) ^ (α / 2) < ε := by
+    simpa [Real.zero_rpow (show α / 2 ≠ 0 by linarith)] using hε
+  have hev := hc.eventually (gt_mem_nhds hz)
+  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
+  refine ⟨min 1 (min τ (r / 2)), lt_min zero_lt_one (lt_min hτ (by linarith)),
+    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
+  intro T hT
+  apply le_of_lt
+  apply hball
+  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hT.1]
+  have := hT.2.trans ((min_le_right _ _).trans (min_le_right _ _))
+  linarith
+
+set_option maxHeartbeats 1600000 in
+/-- Construct a single-chart parametrix from smooth entries and a positive frozen matrix.
+The patch oscillation is only an existence condition. After choosing the nested cutoffs,
+the residual has only the two positive commutator time powers, with constants fixed
+before time. The maps take values in the original unweighted derivative graph and
+Hölder spaces, and the residual is identified with the actual chart operator. -/
+theorem exists_single_chart_parametrix {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U)
+    (a : (ClosedSmoothModel 3) → Matrix (Fin 3) (Fin 3) ℝ) (anchor : (ClosedSmoothModel 3))
+    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (hpos : (a anchor).PosDef) :
+    ∃ ε₀ : ℝ, 0 < ε₀ ∧
+    ∀ (K : Set (ClosedSmoothModel 3)) (ψ ξ : (ClosedSmoothModel 3) → ℝ),
+      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
+      ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
+      (∀ x, ξ x ∈ Icc 0 1) →
+      (∀ x ∈ tsupport ψ, ξ x = 1) → (∀ x ∈ K, ψ x = 1) →
+      (∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε₀) →
+      ∃ C_ψ C' τ₀ : ℝ, 0 ≤ C_ψ ∧ 0 ≤ C' ∧ 0 < τ₀ ∧
+      ∀ T ∈ Ioc 0 τ₀,
+        ∃ (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+          (R : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ),
+          (∀ f p, p.2 ∉ tsupport ψ → (P f).u p = 0) ∧
+          ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+            (∀ p, p.2 ∉ K → f p = 0) →
+            (∀ p, R f p = chartValue a (P f) p - f p) ∧
+            ‖R f‖ ≤ C_ψ * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ ∧
+            ‖P f‖ ≤ C' * ‖f‖ := by
+  obtain ⟨lam, Λell, hlam, hlamΛ, hlo, hhi⟩ := matrixBilin_ellipticity hpos
+  obtain ⟨C_S, ε₀, τ, hCS, hε₀, hτ, hsolver⟩ :=
+    exists_chart_operator α hα hα1 lam Λell hlam hlamΛ
+  refine ⟨ε₀, hε₀, ?_⟩
+  intro K ψ ξ hψ hcψ hξ hcξ hξU hξ01 hnest hone hosc
+  obtain ⟨Λb, _, hext⟩ := oscillation_extension_entries hα hα1 hU a ha anchor
+    hξ hcξ hξU hξ01 hε₀.le hosc
+  obtain ⟨δ, hδ, hδ1, hδτ, hsmall⟩ :=
+    exists_small_time_interval (Λ := Λb) hα hε₀ hτ
+  obtain ⟨C_ψ, C', hCψ, hC', herror⟩ := single_chart_error hα hα1 hU a anchor ha
+    hψ hcψ hξ hcξ hξU hnest hone hCS.le (τ₀ := 1) le_rfl
+  refine ⟨C_ψ, C', δ, hCψ, hC', hδ, ?_⟩
+  intro T hT
+  obtain ⟨b, heq, hb, hbα⟩ := hext T
+  obtain ⟨S, hS, hsolves, _⟩ := hsolver a anchor ξ hpos.isHermitian hlo hhi T
+    hT.1 (hT.2.trans hδτ) b Λb hb hbα (hsmall T hT) heq
+  obtain ⟨C, R, hC, hR⟩ := herror T ⟨hT.1, hT.2.trans hδ1⟩ b S hS heq hsolves
+  refine ⟨C.comp S, R, ?_, ?_⟩
+  · intro f p hp
+    change (C (S f)).u p = 0
+    rw [hC, image_eq_zero_of_notMem_tsupport hp, zero_mul]
+  · exact hR
+
+end Poincare.BufferedFrozenParabolicSolver
```

</details>
