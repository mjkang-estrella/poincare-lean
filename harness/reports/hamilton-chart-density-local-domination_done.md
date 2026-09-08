# Hamilton chart density local domination

Date: 2026-09-08. Base: `b358db205a55844fa09cf253630ec4cc6525d406`.
Branch: `worker/hamilton-chart-density-local-domination`.
Verified proof head: `7bbe4fb4b74eb0d2b142272ea79cdf856578bfc0`.

The task is complete at the worker gate. The exact local domination theorem
compiles without an additional analytic hypothesis. The reduced core removes
only the final domination conjunct and reconstructs the original core, with
both requested Hamilton endpoint implications. This result awaits independent
orchestrator review. It proves no flow-existence statement or unconditional
Poincare endpoint.

Only the new Lean module `Poincare/Global/HamiltonChartDensityLocalDomination.lean` and this report are added. No existing
Lean source, frozen contract, root import, HANDOFF, mission, or ledger was
edited. The task-specific branch and file scope override the general branch
prefix and HANDOFF-edit instructions. The worktree was clean at the recorded
base. Initial `git status --short --branch`, `git worktree list --porcelain`,
and `git rev-parse HEAD` confirmed this isolated worker checkout and base.

Required context read: HANDOFF top section; reaction-record-decomposition
report sections 2, 3, 4 and its evidence appendix; README; PROJECT_MAP; AGENTS;
the supplied worker task; the reaction-core module and its actual imports;
the Gram-continuity and finite-chart-cover modules; and the nearby joint
regularity, metric-variation, and Gram-trace definitions used in the proof.
Mathlib is `7175569c842f9164564bd76ff8b207e7b4705522`, with toolchain
`leanprover/lean4:v4.30.0-rc2`.

## Result and proof

All declarations are in `Poincare.HamiltonChartDensityLocalDomination`.

1. `continuous_trace_timeDeriv` proves joint continuity of the intrinsic
   metric time-variation trace. In a fixed canonical extension frame, joint
   entries give continuous Gram entries and continuous actual time partials.
   The Gram determinant is nonzero at the anchor and remains nonzero nearby.
   The landed Gram-inverse trace formula identifies the continuous finite sum
   with the intrinsic trace on that neighborhood.
2. `hasDerivAt_log_inverseChartDensity` derives the logarithmic density
   derivative, exactly one half of the intrinsic trace, from positive density
   and the landed first variation.
3. `inverseChartDensity_le_exp_mul` applies the mean-value inequality to this
   logarithm on `[t - 1, t + 1]`. A bound `K` on half the trace gives
   `density(τ) ≤ exp K * density(t)` throughout the strip. The trace bound is
   an explicit intermediate hypothesis here; the target theorem proves it.
4. `localBound_of_jointMetricEntries` uses compactness of
   `[t - 1, t + 1] × M` and joint trace continuity to choose a nonnegative K.
   It sets `s = [t - 1, t + 1]` and
   `B i z = (K * exp K) * C.inverseChartDensity (gt t) i z`.
   The existing density-integrability theorem proves integrability of B.
   The derivative bound holds at every coordinate point, hence almost
   everywhere, with precisely the requested quantifier order.

The selected finite cover is extracted from whole extended-chart sources,
then disjointized. Its definition does not supply precompact coordinate
pieces, closure containment in chart targets, or finite coordinate Lebesgue
measure. No such property is asserted or used here. The intrinsic trace and
fixed-time density comparison avoid all three issues. No chart-closure
continuity theorem is needed.

The exact target signature is:

```lean
theorem localBound_of_jointMetricEntries
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z)
```

It is stated with the task's dimension-three manifold section variables.
The unused simply-connected instance is explicitly omitted for this theorem;
the imported example in Appendix B checks the requested signature with that
instance present. No hypothesis was added and no conclusion was weakened.

## Reduced core and endpoints

The new core is literally the original definition with its final domination
conjunct removed. A source comparison also checked this equality after only
renaming the definition.

```lean
def HamiltonReactionCore3' (M : Type u)
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
      Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
```

`hamiltonReactionCore3_of_core'` keeps the same witnesses and supplies the
removed clause with `localBound_of_jointMetricEntries`.
`hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'` composes that
reconstruction with the landed endpoint theorem.
`UniversalHamiltonReactionCoreStatement'` preserves the independent
universes u and v and the original compatible manifold structures.
`universalHamiltonConvergence_of_universalHamiltonReactionCore'` installs
the canonical Borel structure and applies the new pointwise endpoint.

## Validation

- Direct task gate: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean`, exit 0,
  no output for the final file.
- Exact forbidden-token scan, including `opaque`, has empty output, exit 1
  as expected for an `rg` search with no matches.
- `git diff --check`, exit 0, empty output.
- Focused `harness/gate.sh`, exit 0: build succeeds with 3861 jobs;
  `GATE_SCAN declarations=10 nonstandard=[]`; final `GATE: PASS`.
  The displayed unused-variable warning comes from an existing dependency.
- Every one of the nine explicit declarations has `#print axioms` exactly
  `[propext, Classical.choice, Quot.sound]`.
- The tenth module declaration is a compiler-generated congruence theorem
  for the imported inverse-chart definition. Its printed closure is also
  exactly the same three names. The imported module scan checks set equality
  and size three for all ten declarations, rather than just rejecting
  nonstandard names.
- The exact target is checked again as an imported `example` with the full
  supplied section variables. The three consequence signatures and the
  reduced core body are printed from the built module.
- The base-to-head source diff adds exactly the named module. Frozen files
  and all existing sources are unchanged.

No full root build, root import edit, or integration acceptance was performed
by this worker. One exact first review action is:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

## Proof commits

Each theorem was compiled before its commit. Definitions were committed
with their verified reconstruction or endpoint theorem.

```text
73e5f21a Prove joint continuity of intrinsic metric time-variation trace
98e4a90c Prove logarithmic first variation of inverse chart density
185191b0 Bound moving inverse chart densities by a fixed-time density
dbf7d578 Discharge local chart density domination from joint metric entries
5f9fe347 Remove local chart domination from the Hamilton reaction core
39af7098 Derive the Hamilton endpoint from the smaller reaction core
7bbe4fb4 Derive universal Hamilton convergence from the reduced core
```

## Appendix A. Commands and actual output

All Lean attempts, including failed attempts, are retained below. Each block
records the actual command, exit status, and complete captured output. Empty
output is stated outside its output fence. Source searches record literal
repo or pinned Mathlib locations; generated additive declarations are
verified through their `to_additive` source annotations and Lean elaboration.
The first continuity attempts failed on local instance inference, composition
inference, matrix theorem arguments, and finite-sum naming. The logarithmic
variation attempt first compiled with redundant-tactic warnings; those were
removed. No failed attempt was committed.

### Command 1

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

```text
Poincare/Global/HamiltonChartDensityLocalDomination.lean:32:11: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Module.Finite ℝ (TangentSpace I x)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/HamiltonChartDensityLocalDomination.lean:35:62: error: Application type mismatch: The argument
  continuousAt_snd
has type
  ContinuousAt Prod.snd ?m.154
but is expected to have type
  ContinuousAt (↑((chartAt M x).symm.restr (ModelWithCorners.toPartialEquiv ?m.139).source).symm) x
in the application
  ContinuousAt.comp (continuousAt_extChartAt x) continuousAt_snd
Poincare/Global/HamiltonChartDensityLocalDomination.lean:41:60: error: Application type mismatch: The argument
  hchart
has type
  ContinuousAt.{u, 0} (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
but is expected to have type
  ContinuousAt.{0, 0} (Prod.mk t) (↑(extChartAt I x) x)
in the application
  ContinuousAt.comp (ContDiffAt.continuousAt (hjoint t x (b i) (b j))) hchart
Poincare/Global/HamiltonChartDensityLocalDomination.lean:42:4: error: Tactic `apply` failed: could not unify the conclusion of `ContinuousAt.congr_of_eventuallyEq hc`
  ContinuousAt.{0, 0} ?m.278 (↑(extChartAt I x) x)
with the goal
  ContinuousAt.{u, 0} (fun p => gramMatrix (gt p.1) x p.2 i j) (t, x)

Note: The full type of `ContinuousAt.congr_of_eventuallyEq hc` is
  ?m.278 =ᶠ[𝓝 (↑(extChartAt I x) x)] metricEntryJointChart gt x (b i) (b j) ∘ Prod.mk t →
    ContinuousAt ?m.278 (↑(extChartAt I x) x)

n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : SecondCountableTopology M
inst✝⁵ : MeasurableSpace M
inst✝⁴ : BorelSpace M
inst✝³ : ChartedSpace E M
inst✝² : IsManifold I ∞ M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
gt : ℝ → ClosedSmoothRiemannianMetric n M
hjoint : ∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3
t : ℝ
x : M
b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) := sorry
hchart : ContinuousAt (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
hsource : ∀ᶠ (p : ℝ × M) in 𝓝 (t, x), p.2 ∈ (extChartAt I x).source
i j : Fin (Module.finrank ℝ (TangentSpace I x))
hc : ContinuousAt (metricEntryJointChart gt x (b i) (b j) ∘ Prod.mk t) (↑(extChartAt I x) x)
⊢ ContinuousAt (fun p => gramMatrix (gt p.1) x p.2 i j) (t, x)
Poincare/Global/HamiltonChartDensityLocalDomination.lean:51:80: error: Application type mismatch: The argument
  hchart
has type
  ContinuousAt.{u, 0} (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
but is expected to have type
  ContinuousAt.{0, 0} (Prod.mk t) (↑(extChartAt I x) x)
in the application
  ContinuousAt.comp
    (continuousAt_joint_timeDeriv_of_joint_contDiffAt_one (fun τ z => metricEntryJointChart gt x (b i) (b j) (τ, z)) t
      (↑(extChartAt I x) x) (ContDiffAt.of_le (hjoint t x (b i) (b j)) ?m.380))
    hchart
Poincare/Global/HamiltonChartDensityLocalDomination.lean:52:4: error: Tactic `apply` failed: could not unify the conclusion of `ContinuousAt.congr_of_eventuallyEq hc`
  ContinuousAt.{0, 0} ?m.397 (↑(extChartAt I x) x)
with the goal
  ContinuousAt.{u, 0} (fun p => timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x)

Note: The full type of `ContinuousAt.congr_of_eventuallyEq hc` is
  ?m.397 =ᶠ[𝓝 (↑(extChartAt I x) x)]
      (fun p => deriv (fun t => metricEntryJointChart gt x (b i) (b j) (t, p.2)) p.1) ∘ Prod.mk t →
    ContinuousAt ?m.397 (↑(extChartAt I x) x)

n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : SecondCountableTopology M
inst✝⁵ : MeasurableSpace M
inst✝⁴ : BorelSpace M
inst✝³ : ChartedSpace E M
inst✝² : IsManifold I ∞ M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
gt : ℝ → ClosedSmoothRiemannianMetric n M
hjoint : ∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3
t : ℝ
x : M
b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) := sorry
hchart : ContinuousAt (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
hsource : ∀ᶠ (p : ℝ × M) in 𝓝 (t, x), p.2 ∈ (extChartAt I x).source
hentry :
  ∀ (i j : Fin (Module.finrank ℝ (TangentSpace I x))), ContinuousAt (fun p => gramMatrix (gt p.1) x p.2 i j) (t, x)
i j : Fin (Module.finrank ℝ (TangentSpace I x))
hc :
  ContinuousAt ((fun p => deriv (fun t => metricEntryJointChart gt x (b i) (b j) (t, p.2)) p.1) ∘ Prod.mk t)
    (↑(extChartAt I x) x)
⊢ ContinuousAt (fun p => timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x)
Poincare/Global/HamiltonChartDensityLocalDomination.lean:60:27: error(lean.unknownIdentifier): Unknown constant `Matrix.isUnit_iff_isUnit_det.mp`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:64:10: error(lean.invalidField): Invalid field `matrix_det`: The environment does not contain `Function.matrix_det`, so it is not possible to project the field `matrix_det` from an expression
  hG
of type
  ?m.483 ∈ 𝓝 (G (t, x)) → ?m.483 ∈ map G (𝓝 (t, x))
Poincare/Global/HamiltonChartDensityLocalDomination.lean:66:23: error(lean.invalidField): Invalid field `matrix_det`: The environment does not contain `Function.matrix_det`, so it is not possible to project the field `matrix_det` from an expression
  hG
of type
  ?m.503 ∈ 𝓝 (G (t, x)) → ?m.503 ∈ map G (𝓝 (t, x))
Poincare/Global/HamiltonChartDensityLocalDomination.lean:67:10: error(lean.unknownIdentifier): Unknown constant `Matrix.isUnit_iff_isUnit_det.mpr`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:71:10: error(lean.unknownIdentifier): Unknown identifier `continuousAt_finset_sum`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:72:10: error: No goals to be solved
Poincare/Global/HamiltonChartDensityLocalDomination.lean:24:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv`:
  [SecondCountableTopology M]
  [MeasurableSpace M]
  [BorelSpace M]
  [CompactSpace M]
  [ConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 2

```sh
rg -n 'exists_bound_of_continuousOn|norm_image_sub_le_of_norm_deriv_le|theorem HasDerivAt.log|theorem exp_log|theorem log_le' .lake/packages/mathlib/Mathlib/Analysis/Normed .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:23:* `Convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:326:theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:337:theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:340:  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:346:theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:350:    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:354:theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:358:    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:371:    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:429:    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:440:  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:725:theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:55:theorem exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = |x| := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:58:theorem exp_log (hx : 0 < x) : exp (log x) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:62:theorem exp_log_of_neg (hx : x < 0) : exp (log x) = -x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:146:theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:160:theorem log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [← exp_le_exp, exp_log hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:294:theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:112:theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean:96:@[to_additive IsCompact.exists_bound_of_continuousOn]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean:97:lemma IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
```

### Command 3

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

```text
Poincare/Global/HamiltonChartDensityLocalDomination.lean:48:4: error: Tactic `rfl` failed: The left-hand side
  gramMatrix (gt p.1) x p.2 i j
is not definitionally equal to the right-hand side
  (((gt p.1).inner (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))
      (FiberBundle.extend E (b i) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
    (FiberBundle.extend E (b j) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))

case h
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : SecondCountableTopology M
inst✝⁵ : MeasurableSpace M
inst✝⁴ : BorelSpace M
inst✝³ : ChartedSpace E M
inst✝² : IsManifold I ∞ M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
gt : ℝ → ClosedSmoothRiemannianMetric n M
hjoint : ∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3
t : ℝ
x : M
this : FiniteDimensional ℝ (TangentSpace I x) := continuous_trace_timeDeriv._proof_1_1 x
b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
  Module.finBasis ℝ (TangentSpace I x)
hchart : ContinuousAt (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
hsource : ∀ᶠ (p : ℝ × M) in 𝓝 (t, x), p.2 ∈ (extChartAt I x).source
i j : Fin (Module.finrank ℝ (TangentSpace I x))
hc :
  ContinuousAt (fun x_1 => metricEntryJointChart gt x (b i) (b j) ((fun p => (p.1, ↑(extChartAt I x) p.2)) x_1)) (t, x)
p : ℝ × M
hp : p.2 ∈ (extChartAt I x).source
⊢ gramMatrix (gt p.1) x p.2 i j =
    (((gt p.1).inner (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))
        (FiberBundle.extend E (b i) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
      (FiberBundle.extend E (b j) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))
Poincare/Global/HamiltonChartDensityLocalDomination.lean:59:4: error: Tactic `rfl` failed: The left-hand side
  timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)
is not definitionally equal to the right-hand side
  deriv
    (fun t =>
      (((gt t).inner (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))
          (FiberBundle.extend E (b i) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
        (FiberBundle.extend E (b j) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
    p.1

case h
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : SecondCountableTopology M
inst✝⁵ : MeasurableSpace M
inst✝⁴ : BorelSpace M
inst✝³ : ChartedSpace E M
inst✝² : IsManifold I ∞ M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
gt : ℝ → ClosedSmoothRiemannianMetric n M
hjoint : ∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3
t : ℝ
x : M
this : FiniteDimensional ℝ (TangentSpace I x) := continuous_trace_timeDeriv._proof_1_1 x
b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
  Module.finBasis ℝ (TangentSpace I x)
hchart : ContinuousAt (fun p => (p.1, ↑(extChartAt I x) p.2)) (t, x)
hsource : ∀ᶠ (p : ℝ × M) in 𝓝 (t, x), p.2 ∈ (extChartAt I x).source
hentry :
  ∀ (i j : Fin (Module.finrank ℝ (TangentSpace I x))), ContinuousAt (fun p => gramMatrix (gt p.1) x p.2 i j) (t, x)
i j : Fin (Module.finrank ℝ (TangentSpace I x))
hc :
  ContinuousAt
    (fun x_1 =>
      deriv (fun t => metricEntryJointChart gt x (b i) (b j) (t, ((fun p => (p.1, ↑(extChartAt I x) p.2)) x_1).2))
        ((fun p => (p.1, ↑(extChartAt I x) p.2)) x_1).1)
    (t, x)
p : ℝ × M
hp : p.2 ∈ (extChartAt I x).source
⊢ timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j) =
    deriv
      (fun t =>
        (((gt t).inner (↑(extChartAt I x).symm (↑(extChartAt I x) p.2)))
            (FiberBundle.extend E (b i) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
          (FiberBundle.extend E (b j) (↑(extChartAt I x).symm (↑(extChartAt I x) p.2))))
      p.1
Poincare/Global/HamiltonChartDensityLocalDomination.lean:75:10: error(lean.unknownIdentifier): Unknown constant `ContinuousAt.fun_sum`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:76:10: error: No goals to be solved
Poincare/Global/HamiltonChartDensityLocalDomination.lean:47:38: warning: This simp argument is unused:
  (extChartAt I x).left_inv hp

Hint: Omit it from the simp argument list.
  simp only [metricEntryJointChart,̵ ̵(̵e̵x̵t̵C̵h̵a̵r̵t̵A̵t̵ ̵I̵ ̵x̵)̵.̵l̵e̵f̵t̵_̵i̵n̵v̵ ̵h̵p̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:58:38: warning: This simp argument is unused:
  (extChartAt I x).left_inv hp

Hint: Omit it from the simp argument list.
  simp only [metricEntryJointChart,̵ ̵(̵e̵x̵t̵C̵h̵a̵r̵t̵A̵t̵ ̵I̵ ̵x̵)̵.̵l̵e̵f̵t̵_̵i̵n̵v̵ ̵h̵p̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Command 4

```sh
rg -n 'ContinuousAt.*sum|ContinuousAt.*prod|continuousAt.*sum' .lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean:851:  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
```

### Command 5

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

```text
Poincare/Global/HamiltonChartDensityLocalDomination.lean:77:10: error(lean.unknownIdentifier): Unknown constant `ContinuousAt.sum`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:78:10: error: No goals to be solved
```

### Command 6

```sh
rg -n 'ContinuousAt\.(sum|prod)|continuousAt_(sum|prod)' .lake/packages/mathlib/Mathlib/Topology
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:347:theorem ContinuousAt.prodMk {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:351:theorem ContinuousAt.prodMap {f : X → Z} {g : Y → W} {p : X × Y} (hf : ContinuousAt f p.fst)
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:355:/-- A version of `ContinuousAt.prodMap` that avoids `Prod.fst`/`Prod.snd`
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:357:theorem ContinuousAt.prodMap' {f : X → Z} {g : Y → W} {x : X} {y : Y} (hf : ContinuousAt f x)
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:563:theorem lowerSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:576:  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1129:theorem upperSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
.lake/packages/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean:1142:  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x
.lake/packages/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean:475:    <| ContinuousAt.comp _ (ContinuousAt.prodMap (Continuous.continuousAt continuous_neg)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:645:theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {x : α × β} :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:649:theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {x : α × β} :
```

### Command 7

```sh
rg -n 'continuousAt.*prod|[Cc]ontinuousAt.*[Pp]rod|Tendsto.*finset_prod|fun_prod' .lake/packages/mathlib/Mathlib/Topology/Algebra
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:250:    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
.lake/packages/mathlib/Mathlib/Topology/Algebra/Ring/Basic.lean:344:      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Floor.lean:212:  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Floor.lean:223:    refine (h.continuousAt ?_).comp (continuousAt_id.prodMap (continuousAt_fract ht))
.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Group.lean:35:    simp only [continuous_iff_continuousAt, Prod.forall, ContinuousAt,
.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/Basic.lean:851:  simp only [ContinuousAt, nhds_prod_eq, ← map_mul_left_nhds_one x, ← map_mul_left_nhds_one y,
```

### Command 8

```sh
rg -n 'continuous_finset|continuousAt_finset|continuousAt_sum|continuousAt_prod|fun_sum|fun_prod' .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid* .lake/packages/mathlib/Mathlib/Topology/Algebra/Group* .lake/packages/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:940:theorem continuous_finsetProd {f : ι → X → M} (s : Finset ι) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:944:@[deprecated (since := "2026-04-08")] alias continuous_finset_sum := continuous_finsetSum
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:947:alias continuous_finset_prod := continuous_finsetProd
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid/FunOnFinite.lean:28:  exact continuous_finsetSum _ (fun _ _ ↦ continuous_apply _)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:231:  apply HasDerivAt.fun_sum (fun i _ => this i) |>.congr_deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/SmoothSeries.lean:55:  exact HasFDerivAt.fun_sum fun i _ => hf i y hy
.lake/packages/mathlib/Mathlib/Analysis/Calculus/SmoothSeries.lean:84:    exact HasFDerivAt.fun_sum fun n _ => hf n y hy
.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:512:lemma iteratedDerivWithin_fun_sum {s : Set 𝕜} (hx : x ∈ s) (hs : UniqueDiffOn 𝕜 s)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean:521:lemma iteratedDeriv_fun_sum (hf : ∀ i ∈ I, ContDiffAt 𝕜 n (f i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:988:  apply Finset.analyticOn_fun_sum _ (fun c _ ↦ ?_)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:1093:      HasFDerivWithinAt.fun_sum (fun c _ ↦ A c)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:403:theorem iteratedFDerivWithin_fun_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:417:theorem iteratedFDeriv_fun_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {n : ℕ} {x : E}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:427:    iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:186:theorem HasDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) L) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:188:  simpa using (HasFDerivAtFilter.fun_sum h).hasDerivAtFilter
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:192:  convert HasDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:195:theorem HasStrictDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:197:  HasDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:203:theorem HasDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:205:  HasDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:211:theorem HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:213:  HasDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:219:theorem derivWithin_fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:222:  · exact (HasDerivWithinAt.fun_sum fun i hi ↦ (h i hi).hasDerivWithinAt).derivWithin hsx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:232:theorem deriv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:234:  (HasDerivAt.fun_sum fun i hi ↦ (h i hi).hasDerivAt).deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:402:theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:411:  convert HasStrictFDerivAt.fun_sum h; simp
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:413:theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:421:  convert HasFDerivAtFilter.fun_sum h; simp
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:424:theorem HasFDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:426:  HasFDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:434:theorem HasFDerivAt.fun_sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:436:  HasFDerivAtFilter.fun_sum h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:444:theorem DifferentiableWithinAt.fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:447:    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:456:theorem DifferentiableAt.fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:458:  HasFDerivAt.differentiableAt <| HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:466:theorem DifferentiableOn.fun_sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:468:  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:476:theorem Differentiable.fun_sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:478:  fun x => DifferentiableAt.fun_sum fun i hi => h i hi x
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:484:theorem fderivWithin_fun_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:487:  (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:494:theorem fderiv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:496:  (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:735:        apply HasFDerivAt.fun_sum (fun s _hs ↦ ?_)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:771:    apply continuous_finsetSum _ (fun e _ ↦ ?_)
```

### Command 9

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

```text
Poincare/Global/HamiltonChartDensityLocalDomination.lean:77:10: error(lean.unknownIdentifier): Unknown constant `ContinuousAt.finsetSum`
Poincare/Global/HamiltonChartDensityLocalDomination.lean:78:10: error: No goals to be solved
```

### Command 10

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 0.

```text
Poincare/Global/HamiltonChartDensityLocalDomination.lean:24:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv`:
  [SecondCountableTopology M]
  [MeasurableSpace M]
  [BorelSpace M]
  [CompactSpace M]
  [ConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 11

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/trace-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 12

```sh
rg -n 'theorem HasDerivAt.log|norm_image_sub_le_of_norm_hasDerivWithin_le|theorem abs_le|Icc_mem_nhds|theorem norm_mul|theorem exp_add' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean .lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean
```

Exit 0.

```text
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:441:    · exact ⟨c, hc.1.le, Icc_mem_nhdsGE hc.1, (Icc_subset_Ico_right hc.2).trans hbs⟩
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:738:theorem pi_Icc_mem_nhds (ha : ∀ i, a i < x i) (hb : ∀ i, x i < b i) : Icc a b ∈ 𝓝 x :=
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:739:  pi_univ_Icc a b ▸ set_pi_mem_nhds finite_univ fun _ _ => Icc_mem_nhds (ha _) (hb _)
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:742:theorem pi_Icc_mem_nhds' (ha : ∀ i, a' i < x' i) (hb : ∀ i, x' i < b' i) : Icc a' b' ∈ 𝓝 x' :=
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:743:  pi_Icc_mem_nhds ha hb
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:95:    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:332:  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:392:    (Icc_mem_nhdsGE_of_mem hy)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:395:    (Icc_mem_nhdsGE_of_mem hy)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:692:theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:712:  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:728:  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:112:theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:249:    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:312:    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
```

### Command 13

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

Output was empty.

### Command 14

```sh
git diff --check
```

Exit 0.

Output was empty.

### Command 15

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/log-axioms.lean
```

Exit 0.

```text
/tmp/hamilton-density-evidence/log-axioms.lean:104:6: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/hamilton-density-evidence/log-axioms.lean:104:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/hamilton-density-evidence/log-axioms.lean:102:76: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 16

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 0.

Output was empty.

### Command 17

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/comparison-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.inverseChartDensity_le_exp_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 18

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/local-axioms.lean
```

Exit 0.

```text
/tmp/hamilton-density-evidence/local-axioms.lean:149:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 19

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 0.

Output was empty.

### Command 20

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/core-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 21

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/endpoint-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 22

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/final-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.inverseChartDensity_le_exp_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 23

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 0.

Output was empty.

### Command 24

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/hamilton-chart-density-local-domination Poincare.Global.HamiltonChartDensityLocalDomination
```

Exit 0.

```text
=== GATE: forbidden tokens in Poincare/Global/HamiltonChartDensityLocalDomination.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.HamiltonChartDensityLocalDomination ===
warning: Poincare/Global/NormalizedFlowHausdorffScalarDominationJointC1Reduction.lean:117:28: unused variable `hQ`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [3861/3861] Built Poincare.Global.HamiltonChartDensityLocalDomination (3.2s)
Build completed successfully (3861 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=10 nonstandard=[]
=== GATE: PASS ===
```

### Command 25

```sh
rg --pcre2 -n '(^|[^A-Za-z0-9_])(?:continuous_trace_timeDeriv|hasDerivAt_log_inverseChartDensity|inverseChartDensity_le_exp_mul|localBound_of_jointMetricEntries|HamiltonReactionCore3|HamiltonReactionCore3'"'"'|hamiltonReactionCore3_of_core'"'"'|hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3|hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'"'"'|UniversalHamiltonReactionCoreStatement'"'"'|universalHamiltonConvergence_of_universalHamiltonReactionCore'"'"'|continuousAt_joint_timeDeriv_of_joint_contDiffAt_one|traceMetricVariationAt_eq_sum_gram_inv|gramMatrix|gramFrame|metricEntryJointChart|MetricEntriesJointContDiffAt|timeDerivAt|timeDerivBilinAt|timeDifferentiableAt_of_metricEntriesJointContDiffAt_one|gramMatrix_at_base_isUnit|inverseChartDensity_integrable|inverseChartPullbackVolumeDensity_pos|hasDerivAt_inverseChartDensity|inverseChartDensity_nonneg|finiteExtendedChartFrameDensityDerivative|compactFiniteExtendedChartCover|exists_finiteExtendedChartCover|coordinateDomain|coordinateTargetPoint|inverseChartDensity|FiniteExtendedChartCover|coordinateLebesgueMeasure|ClosedSmoothRiemannianMetric|IsClosedNormalizedRicciFlowSolutionAt|meanScalar|normalizedTracelessRicciEvolutionReactionAt|closedMetricFiniteVolumeMeasure|HamiltonConvergencePinchedLimit3|UniversalHamiltonConvergenceStatement|continuous_iff_continuousAt|finBasis|finrank|continuousAt_extChartAt|continuousAt_fst|continuousAt_snd|extChartAt_source_mem_nhds|continuousAt_pi|isUnit_iff_ne_zero|isUnit_iff_isUnit_det|inv_def|inverse_eq_inv|matrix_det|matrix_adjugate|tendsto_finsetSum|tendsto_finsetProd|norm_image_sub_le_of_norm_hasDerivWithin_le|convex_Icc|norm_eq_abs|abs_le|le_trans|le_abs_self|mul_le_mul_of_nonneg_left|mul_le_mul_of_nonneg_right|mul_one|exp_le_exp|exp_add|exp_log|isCompact_Icc|isCompact_univ|exists_bound_of_continuousOn|exists_bound_of_continuousOn'"'"'|le_max_right|le_max_left|mem_univ|Icc_mem_nhds|norm_mul|norm_of_nonneg)(?=[^A-Za-z0-9_'"'"']|$)' Poincare/Global/HamiltonChartDensityLocalDomination.lean Poincare/Global/HamiltonReactionCoreReduction.lean Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean Poincare/Global/NormalizedFlowHausdorffScalarTimeDerivativeAutomatic.lean Poincare/Global/ScalarVariation.lean Poincare/Global/MetricFlowJointRegularity.lean Poincare/Global/MetricVariation.lean .lake/packages/mathlib/Mathlib | rg ':(?:[0-9]+):.*(theorem |lemma |def |structure |class |abbrev |to_additive|alias )'
```

Exit 0.

```text
Poincare/Global/NormalizedFlowHausdorffScalarTimeDerivativeAutomatic.lean:36:theorem continuousAt_joint_timeDeriv_of_joint_contDiffAt_one
Poincare/Global/HamiltonReactionCoreReduction.lean:31:theorem inverseChartDensity_integrable
Poincare/Global/HamiltonReactionCoreReduction.lean:132:def HamiltonReactionCore3 (M : Type u)
Poincare/Global/HamiltonReactionCoreReduction.lean:208:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3
Poincare/Global/HamiltonChartDensityLocalDomination.lean:28:theorem continuous_trace_timeDeriv
Poincare/Global/HamiltonChartDensityLocalDomination.lean:95:theorem hasDerivAt_log_inverseChartDensity
Poincare/Global/HamiltonChartDensityLocalDomination.lean:109:theorem inverseChartDensity_le_exp_mul
Poincare/Global/HamiltonChartDensityLocalDomination.lean:151:theorem localBound_of_jointMetricEntries
Poincare/Global/HamiltonChartDensityLocalDomination.lean:197:def HamiltonReactionCore3' (M : Type u)
Poincare/Global/HamiltonChartDensityLocalDomination.lean:221:theorem hamiltonReactionCore3_of_core'
Poincare/Global/HamiltonChartDensityLocalDomination.lean:231:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'
Poincare/Global/HamiltonChartDensityLocalDomination.lean:239:def UniversalHamiltonReactionCoreStatement' : Prop :=
Poincare/Global/HamiltonChartDensityLocalDomination.lean:248:theorem universalHamiltonConvergence_of_universalHamiltonReactionCore'
Poincare/Global/MetricVariation.lean:41:def timeDerivAt
Poincare/Global/MetricVariation.lean:153:noncomputable def timeDerivBilinAt
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:54:structure FiniteExtendedChartCover where
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:62:theorem exists_finiteExtendedChartCover :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:85:noncomputable def compactFiniteExtendedChartCover :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:92:def chartSource (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:97:def manifoldPiece (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:136:def coordinateDomain
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:152:def coordinateTargetPoint
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:243:def inverseChartDensity
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:251:theorem inverseChartDensity_nonneg
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:285:theorem hasDerivAt_inverseChartDensity
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:337:def finiteExtendedChartFrameDensityDerivative
Poincare/Global/MetricFlowJointRegularity.lean:190:noncomputable def metricEntryJointChart
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
Poincare/Global/MetricFlowJointRegularity.lean:204:theorem MetricEntriesJointContDiffAt.of_le
Poincare/Global/MetricFlowJointRegularity.lean:276:theorem timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:144:theorem of_finrank_pos (h : 0 < finrank K V) : FiniteDimensional K V :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:147:theorem of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:156:theorem of_fact_finrank_eq_succ (n : ℕ) [hn : Fact (finrank K V = n + 1)] :
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:160:lemma of_fact_finrank_eq_two [Fact (finrank K V = 2)] : FiniteDimensional K V :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:171:`finrank`. This is a copy of `finrank_eq_rank _ _` which creates easier typeclass searches. -/
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:172:theorem finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:177:theorem finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
.lake/packages/mathlib/Mathlib/Computability/Reduce.lean:384:private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:121:noncomputable def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:143:theorem basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0)
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:149:theorem range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:264:theorem eq_of_le_of_finrank_le (h_le : F ≤ E) (h_finrank : finrank K E ≤ finrank K F) : F = E :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:270:theorem eq_of_le_of_finrank_eq (h_le : F ≤ E) (h_finrank : finrank K F = finrank K E) : F = E :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:485:theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:541:theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:371:theorem Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) :
.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:92:lemma inv_def (f : ∀ i, G i) : f⁻¹ = fun i ↦ (f i)⁻¹ := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/FreeAndStrongRankCondition.lean:256:theorem eq_bot_of_finrank_one (h : finrank F S = 1) [Module.Free F S] : S = ⊥ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/FreeAndStrongRankCondition.lean:277:theorem finrank_eq_one_iff [Nontrivial E] [Module.Free F S] : finrank F S = 1 ↔ S = ⊥ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:65:theorem Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:238:theorem finrank_of_not_finite (h : ¬Module.Finite R M) : finrank R M = 0 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:242:theorem finite_of_finrank_pos (h : 0 < finrank R M) : Module.Finite R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:246:theorem finite_of_finrank_eq_succ {n : ℕ} (hn : finrank R M = n.succ) : Module.Finite R M :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:286:noncomputable def finBasis [Module.Finite R M] :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:292:noncomputable def finBasisOfFinrankEq [Module.Finite R M] {n : ℕ} (hn : finrank R M = n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:317:theorem nonempty_linearEquiv_of_finrank_eq_one (d1 : Module.finrank R M = 1) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean:353:noncomputable def _root_.LinearEquiv.smul_id_of_finrank_eq_one (d1 : Module.finrank R M = 1) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/RankNullity.lean:207:/-- Rank-nullity theorem using `finrank`. -/
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/RankNullity.lean:214:/-- Rank-nullity theorem using `finrank` and subtraction. -/
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/RankNullity.lean:240:lemma Submodule.exists_of_finrank_lt (N : Submodule R M) (h : finrank R N < finrank R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Localization.lean:56:lemma IsLocalizedModule.finrank_eq : finrank R N = finrank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Localization.lean:137:theorem finrank_eq_of_le_nonZeroDivisors : finrank T P = finrank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Localization.lean:178:theorem finrank_eq : finrank T P = finrank R M := by simpa using congr_arg toNat bc.lift_rank_eq
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:119:theorem finrank_ulift : finrank R (ULift M) = finrank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:244:theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ M) = card ι * finrank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:249:theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:324:theorem Module.finrank_fintype_fun_eq_card : finrank R (η → R) = Fintype.card η :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:328:theorem Module.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n := by simp
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:378:theorem Module.finrank_baseChange : finrank R (R ⊗[S] M') = finrank S M' := by simp
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:394:theorem lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finrank R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:442:protected noncomputable def Set.finrank (s : Set M) : ℕ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:445:theorem finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) ≤ s.toFinset.card :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:448:theorem finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R ≤ s.card :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean:555:theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:194:  mul_one := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:248:@[to_additive] theorem inv_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:477:theorem finrank_self : finrank R R = 1 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:524:theorem finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = Module.rank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:62:noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:65:@[simp] theorem finrank_subsingleton [Subsingleton R] : finrank R M = 1 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:68:theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank R M = ↑n) : finrank R M = n := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:71:lemma rank_eq_one_iff_finrank_eq_one : Module.rank R M = 1 ↔ finrank R M = 1 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:79:theorem finrank_le_of_rank_le {n : ℕ} (h : Module.rank R M ≤ ↑n) : finrank R M ≤ n := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:84:theorem finrank_lt_of_rank_lt {n : ℕ} (h : Module.rank R M < ↑n) : finrank R M < n := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:89:theorem lt_rank_of_lt_finrank {n : ℕ} (h : n < finrank R M) : ↑n < Module.rank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:96:theorem one_lt_rank_of_one_lt_finrank (h : 1 < finrank R M) : 1 < Module.rank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:108:theorem CommSemiring.finrank_self (R) [CommSemiring R] : Module.finrank R R = 1 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:116:theorem finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finrank R N := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean:139:theorem finrank_top : finrank R (⊤ : Submodule R M) = finrank R M := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:264:theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:267:protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:427:theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
.lake/packages/mathlib/Mathlib/RepresentationTheory/Character.lean:61:theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V := by
.lake/packages/mathlib/Mathlib/RepresentationTheory/Character.lean:160:theorem char_one (ρ : Representation k G V) : ρ.character 1 = Module.finrank k V := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:222:lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:230:lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:360:theorem Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:372:theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:511:theorem finrank_eq_one (v : M) (n : v ≠ 0) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M = 1 :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean:525:theorem finrank_le_one (v : M) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M ≤ 1 := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean:397:@[simp] lemma exp_log {x : Mᵐ⁰} (hx : x ≠ 0) : exp (log x) = x := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean:408:@[simp] lemma exp_add (a b : M) : exp (a + b) = exp a * exp b := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean:465:theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
.lake/packages/mathlib/Mathlib/RepresentationTheory/Irreducible.lean:82:@[simp] theorem finrank_intertwiningMap_self : Module.finrank k (IntertwiningMap ρ ρ) = 1 := by
.lake/packages/mathlib/Mathlib/RepresentationTheory/Irreducible.lean:91:theorem finrank_eq_one_of_isMulCommutative [IsMulCommutative G] : Module.finrank k V = 1 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/MulOpposite.lean:63:theorem finrank [DivisionRing R] [AddCommGroup H] [Module R H] :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:525:theorem ZLattice.rank [hs : IsZLattice K L] : finrank ℤ L = finrank K E := by
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:223:lemma tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:229:lemma summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:234:lemma tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:240:lemma summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:264:lemma summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:268:lemma summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:272:lemma summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:276:lemma summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:69:theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x
.lake/packages/mathlib/Mathlib/Algebra/Lie/CartanExists.lean:94:lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly R M x y).natDegree = finrank R M := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/CartanExists.lean:112:lemma lieCharpoly_coeff_natDegree [Nontrivial R] (i j : ℕ) (hij : i + j = finrank R M) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/CartanExists.lean:138:lemma engel_isBot_of_isMin (hLK : finrank K L ≤ #K) (U : LieSubalgebra K L)
.lake/packages/mathlib/Mathlib/Algebra/Lie/CartanExists.lean:357:lemma exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L ≤ #K) :
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:458:protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:439:protected theorem mul_one : M * 1 = M := by
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Polynomial.lean:383:lemma polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = finrank R M) [Nontrivial R] :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Polynomial.lean:488:lemma nilRank_le_finrank : nilRank φ ≤ finrank R M := by
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Polynomial.lean:540:lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
.lake/packages/mathlib/Mathlib/Algebra/Field/Defs.lean:195:@[simp] lemma smul_one_eq_cast (q : ℚ≥0) : q • (1 : K) = q := by rw [NNRat.smul_def, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Quaternion.lean:536:theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
.lake/packages/mathlib/Mathlib/Algebra/Quaternion.lean:972:theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 :=
.lake/packages/mathlib/Mathlib/Algebra/Field/Rat.lean:70:lemma inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def, num_coe, den_coe]
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Tower.lean:134:    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
.lake/packages/mathlib/Mathlib/Algebra/Lie/Rank.lean:81:lemma rank_le_finrank [Nontrivial R] : rank R L M ≤ finrank R M :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Rank.lean:113:lemma exists_isRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/Rank.lean:153:lemma rank_le_finrank [Nontrivial R] : rank R L ≤ finrank R L :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Rank.lean:185:lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hadamard.lean:129:theorem hadamard_one : M ⊙ 1 = diagonal M.diag := mul_one M.diag ▸ hadamard_diagonal M 1
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:127:theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:172:theorem inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate :=
Poincare/Global/ScalarVariation.lean:1679:noncomputable def gramMatrix
Poincare/Global/ScalarVariation.lean:1712:theorem gramMatrix_at_base_isUnit
Poincare/Global/ScalarVariation.lean:1825:noncomputable def gramFrame (x y : M) :
Poincare/Global/ScalarVariation.lean:2146:theorem traceMetricVariationAt_eq_sum_gram_inv
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Ring.lean:226:private nonrec theorem mul_one (x : ⨁ i, A i) : x * 1 = x := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean:320:lemma isUnit_iff_isUnit_det [Module.Finite R M] [Module.Free R M] (f : M →ₗ[R] M) :
.lake/packages/mathlib/Mathlib/Data/Set/Operations.lean:100:theorem mem_univ (x : α) : x ∈ @univ α := trivial
.lake/packages/mathlib/Mathlib/Algebra/AffineMonoid/Embedding.lean:36:noncomputable abbrev dim := Module.finrank ℤ <| GrothendieckAddGroup M
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Cardinality.lean:105:lemma card_of_finrank [Finite k] {n : ℕ} (h : Module.finrank k V = n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Cardinality.lean:126:lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Basic.lean:144:theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Basic.lean:164:noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Basic.lean:177:noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Basic.lean:181:theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean:120:noncomputable def quotientEquivDirectSum (h : Module.finrank R N = Module.finrank R M) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean:69:theorem Module.finrank_linearMap_self : finrank S (M →ₗ[R] S) = finrank R M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean:91:theorem card_algHom_le_finrank : Nat.card (M →ₐ[K] L) ≤ finrank K M := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/ModN.lean:108:@[simp] lemma natCard_eq : Nat.card (ModN G n) = n ^ Module.finrank ℤ G := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:31:theorem finrank_real_complex : finrank ℝ ℂ = 2 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:42:theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean:99:lemma inv_def : C⁻¹ = {
.lake/packages/mathlib/Mathlib/LinearAlgebra/SpecialLinearGroup.lean:74:theorem subsingleton_of_finrank_eq_one [Module.Free R V] (d1 : Module.finrank R V = 1) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/SpecialLinearGroup.lean:343:theorem center_eq_bot_of_finrank_le_one (h : Module.finrank R V ≤ 1) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/BooleanRing.lean:101:theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Basic.lean:159:theorem mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.lean:340:theorem inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean:510:theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:786:theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:792:theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean:357:theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean:361:theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:226:theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:230:theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean:195:theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:883:lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:884:lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:921:lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:922:lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Canonical.lean:536:@[simp] lemma exp_le_exp : exp a ≤ exp b ↔ a ≤ b := by simp [exp]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Trace.lean:188:theorem trace_one : trace R M 1 = (finrank R M : R) := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Trace.lean:197:theorem trace_id : trace R M id = (finrank R M : R) := by rw [← Module.End.one_eq_id, trace_one]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean:428:def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean:65:def sigPos : ℕ := max' {r ∈ Iic (Module.finrank R M) |
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean:73:lemma sigPos_le_finrank : sigPos Q ≤ Module.finrank R M := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Semiconj/Defs.lean:91:theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]
.lake/packages/mathlib/Mathlib/Algebra/Group/Even.lean:106:lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:414:theorem mul_one : ∀ a : M, a * 1 = a :=
.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:648:theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:652:theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal]
.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:655:theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal]
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:275:theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:284:protected theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:291:theorem finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:298:protected theorem finrank_top : finrank (⊤ : IntermediateField F E) E = 1 :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:304:@[simp] theorem finrank_top' : finrank F (⊤ : IntermediateField F E) = finrank F E :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:320:theorem isSimpleOrder_of_finrank_prime (hp : Nat.Prime (Module.finrank F E)) :
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:335:theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:349:theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:359:theorem subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:468:theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
.lake/packages/mathlib/Mathlib/Data/Part.lean:616:theorem inv_def [Inv α] (a : Part α) : a⁻¹ = Part.map (·⁻¹) a := rfl
.lake/packages/mathlib/Mathlib/Data/Fintype/Defs.lean:96:theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
.lake/packages/mathlib/Mathlib/Data/Fintype/Defs.lean:113:theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Algebraic.lean:60:theorem finrank_eq_finrank_subalgebra : finrank K F.toSubalgebra = finrank K F :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Algebraic.lean:112:theorem finrank_dvd_of_le_left (h : F ≤ E) : finrank E L ∣ finrank F L := by
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Algebraic.lean:117:theorem finrank_dvd_of_le_right (h : F ≤ E) : finrank K F ∣ finrank K E := by
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Algebraic.lean:121:theorem finrank_le_of_le_left [FiniteDimensional F L] (h : F ≤ E) : finrank E L ≤ finrank F L :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Algebraic.lean:124:theorem finrank_le_of_le_right [FiniteDimensional K E] (h : F ≤ E) : finrank K F ≤ finrank K E :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Int/Defs.lean:94:lemma zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := mul_one _
.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Luroth.lean:61:lemma φ_natDegree (h : E ≠ ⊥) : (φ E).natDegree = Module.finrank E K⟮X⟯ := by
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:113:theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:587:lemma mulRight_one : Equiv.mulRight (1 : α) = 1 := ext mul_one
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:665:theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:771:theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Basic.lean:156:  (inv_def _).symm
.lake/packages/mathlib/Mathlib/FieldTheory/RatFunc/Basic.lean:788:theorem finrank_ratFunc_ratFunc : Module.finrank k⟮X⟯ K⟮X⟯ = Module.finrank k K := by
.lake/packages/mathlib/Mathlib/Data/Semiquot.lean:217:theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Int.lean:61:lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)
.lake/packages/mathlib/Mathlib/FieldTheory/Fixed.lean:298:theorem finrank_le_card [Fintype G] : finrank (subfield G F) F ≤ Fintype.card G := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean:152:theorem multiplicity_le : multiplicity E ≤ 5 ^ finrank ℝ E := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:917:theorem tendsto_finsetProd {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:922:@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:925:alias tendsto_finset_prod := tendsto_finsetProd
.lake/packages/mathlib/Mathlib/FieldTheory/Galois/IsGaloisGroup.lean:239:theorem card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
.lake/packages/mathlib/Mathlib/FieldTheory/LinearDisjoint.lean:412:theorem finrank_sup (H : A.LinearDisjoint B) : finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
.lake/packages/mathlib/Mathlib/FieldTheory/LinearDisjoint.lean:608:theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) : A.LinearDisjoint L :=
.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Finite.lean:37:theorem natDegree_le [Module.Free A B] : (minpoly A x).natDegree ≤ Module.finrank A B := by
.lake/packages/mathlib/Mathlib/FieldTheory/Minpoly/Finite.lean:41:theorem degree_le [Module.Free A B] : (minpoly A x).degree ≤ Module.finrank A B :=
.lake/packages/mathlib/Mathlib/Algebra/Group/TransferInstance.lean:66:lemma inv_def [Inv β] (x : α) :
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:49:noncomputable def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:69:theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:114:theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:132:theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:166:theorem finrank_comap (f : L →+* E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:225:theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:314:theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:359:theorem finrank_comap (f : L →ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:433:theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:443:theorem finrank_bot_mul_relfinrank (h : A ≤ B) : finrank F A * relfinrank A B = finrank F B := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:451:theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:457:theorem relfinrank_dvd_finrank_bot : relfinrank A B ∣ finrank F B :=
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:508:theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
.lake/packages/mathlib/Mathlib/FieldTheory/Relrank.lean:516:theorem relfinrank_bot_left : relfinrank ⊥ A = finrank F A := by
.lake/packages/mathlib/Mathlib/FieldTheory/SeparableClosure.lean:306:def finInsepDegree : ℕ := finrank (separableClosure F E) E
.lake/packages/mathlib/Mathlib/FieldTheory/NormalizedTrace.lean:124:  IntermediateField.adjoin.finrank ha ▸ trace_adjoinSimpleGen ha ▸ normalizedTrace_def F K a
.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean:770:theorem isCompact_univ [h : CompactSpace X] : IsCompact (univ : Set X) :=
.lake/packages/mathlib/Mathlib/FieldTheory/KummerExtension.lean:441:lemma finrank_of_isSplittingField_X_pow_sub_C : Module.finrank K L = n := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Idempotent.lean:72:lemma one : IsIdempotentElem (1 : M) := mul_one _
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:587:theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b ∈ 𝓝 x :=
.lake/packages/mathlib/Mathlib/Topology/Order/IsLUB.lean:238:protected lemma ConditionallyCompleteLinearOrder.isCompact_Icc (a b : α) :
.lake/packages/mathlib/Mathlib/FieldTheory/PolynomialGaloisGroup.lean:348:theorem card_of_separable (hp : p.Separable) : Nat.card p.Gal = finrank F p.SplittingField :=
.lake/packages/mathlib/Mathlib/FieldTheory/SeparableDegree.lean:727:theorem finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E := by
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Polynomial.lean:206:theorem finrank_R [Fintype σ] : Module.finrank K (R σ K) = Fintype.card (σ → K) :=
.lake/packages/mathlib/Mathlib/Topology/VectorBundle/FiniteDimensional.lean:30:protected lemma finrank_eq (b : B) : Module.finrank R (E b) = Module.finrank R F :=
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/Class.lean:91:theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Basic.lean:370:theorem orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K L :=
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Extension.lean:80:theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/GaloisField.lean:81:theorem finrank {n} (h : n ≠ 0) : Module.finrank (ZMod p) (GaloisField p n) = n := by
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/GaloisField.lean:302:theorem nonempty_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
.lake/packages/mathlib/Mathlib/FieldTheory/Finite/GaloisField.lean:316:theorem natCard_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:361:lemma volume_ball_of_dim_even {k : ℕ} (hk : finrank ℝ E = 2 * k) (x : E) (r : ℝ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:367:lemma volume_closedBall_of_dim_even {k : ℕ} (hk : finrank ℝ E = 2 * k) (x : E) (r : ℝ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:373:lemma volume_ball_of_dim_odd {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (x : E) (r : ℝ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:383:lemma volume_closedBall_of_dim_odd {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (x : E) (r : ℝ) :
.lake/packages/mathlib/Mathlib/FieldTheory/PurelyInseparable/Basic.lean:580:theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:216:theorem Icc_mem_nhds (xt : x ≠ ∞) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
.lake/packages/mathlib/Mathlib/Topology/Constructions.lean:780:theorem continuousAt_pi {f : X → ∀ i, A i} {x : X} :
.lake/packages/mathlib/Mathlib/ModelTheory/Substructures.lean:72:theorem closedUnder_univ : ClosedUnder f (univ : Set M) := fun _ _ => mem_univ _
.lake/packages/mathlib/Mathlib/ModelTheory/PartialEquiv.lean:142:theorem le_trans (f g h : M ≃ₚ[L] N) : f ≤ g → g ≤ h → f ≤ h := by
.lake/packages/mathlib/Mathlib/Topology/Instances/Matrix.lean:212:theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
.lake/packages/mathlib/Mathlib/Topology/Instances/Matrix.lean:238:theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean:237:theorem MeasureTheory.volume_eq_of_finrank_eq_one (h : Module.finrank ℝ E = 1) {v : E}
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:70:lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:73:lemma ge_trans : b ≤ a → c ≤ b → c ≤ a := flip le_trans
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:80:theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
.lake/packages/mathlib/Mathlib/Topology/Constructions/SumProd.lean:116:theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:152:theorem continuous_iff_continuousAt : Continuous f ↔ ∀ x, ContinuousAt f x :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/House.lean:130:private def c := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/House.lean:304:private def c₁ := finrank ℚ K * c₂ K
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:132:lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:135:lemma sqrt_le_sqrt (h : m ≤ n) : sqrt m ≤ sqrt n := le_sqrt.2 (le_trans (sqrt_le _) h)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean:968:    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean:994:    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:500:theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source ∈ 𝓝 x :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:517:theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:57:natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`.  This may seem a
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:336:def stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:343:theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:347:theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:373:theorem stereographic'_symm_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:420:theorem contMDiff_coe_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:440:theorem ContMDiff.codRestrict_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] {f : M → E}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:462:theorem contMDiff_neg_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:470:private lemma stereographic'_neg {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:484:theorem range_mfderiv_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:520:theorem mfderiv_coe_sphere_injective {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:545:theorem finrank_real_complex_fact' : Fact (finrank ℝ ℂ = 1 + 1) :=
.lake/packages/mathlib/Mathlib/Order/Sublattice.lean:183:@[simp] lemma mem_top (a : α) : a ∈ (⊤ : Sublattice α) := mem_univ _
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:211:protected theorem finrank [NumberField K] : finrank ℝ (mixedSpace K) = finrank ℚ K := by
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:827:protected theorem finrank :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean:462:theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s ∈ 𝓝 x) : dimH s = finrank ℝ E := by
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean:472:theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank ℝ E :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean:491:theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean:527:theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense sᶜ := by
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean:554:theorem ContDiff.dimH_range_le {f : E → F} (h : ContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean:80:theorem rootDiscr_def : rootDiscr K = |discr K| ^ (finrank ℚ K : ℝ)⁻¹ := by
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean:242:theorem abs_discr_ge (h : 1 < finrank ℚ K) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean:273:theorem abs_discr_gt_two (h : 1 < finrank ℚ K) : 2 < |discr K| := by
.lake/packages/mathlib/Mathlib/Order/Lattice.lean:421:lemma inf_left_le_sup_right : (a ⊓ b) ≤ (b ⊔ c) := le_trans inf_le_right le_sup_left
.lake/packages/mathlib/Mathlib/Order/Lattice.lean:424:lemma inf_right_le_sup_right : (b ⊓ a) ≤ (b ⊔ c) := le_trans inf_le_left le_sup_left
.lake/packages/mathlib/Mathlib/Order/Lattice.lean:427:lemma inf_left_le_sup_left : (a ⊓ b) ≤ (c ⊔ b) := le_trans inf_le_right le_sup_right
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/DilationEquiv.lean:149:theorem inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Units/Basic.lean:246:theorem torsionOrder_eq_two_of_odd_finrank (h : Odd (Module.finrank ℚ K)) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean:415:theorem RingOfIntegers.rank : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean:95:protected theorem IsTotallyReal.finrank [NumberField K] [h : IsTotallyReal K] :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean:237:protected theorem IsTotallyComplex.finrank [NumberField K] [h : IsTotallyComplex K] :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:61:theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
.lake/packages/mathlib/Mathlib/Topology/DiscreteQuotient.lean:209:theorem ofLE_comp_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂) :=
.lake/packages/mathlib/Mathlib/Order/BooleanSubalgebra.lean:217:@[simp] lemma mem_top : a ∈ (⊤ : BooleanSubalgebra α) := mem_univ _
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:477:theorem nrComplexPlaces_eq_zero_of_finrank_eq_one (h : finrank ℚ K = 1) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:480:theorem nrRealPlaces_eq_one_of_finrank_eq_one (h : finrank ℚ K = 1) :
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:485:theorem nrRealPlaces_pos_of_odd_finrank (h : Odd (finrank ℚ K)) :
.lake/packages/mathlib/Mathlib/Order/Basic.lean:135:@[to_dual trans'] alias LE.le.trans := le_trans
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:171:@[simp] lemma mem_top : x ∈ (⊤ : ConvexCone R M) := mem_univ x
.lake/packages/mathlib/Mathlib/NumberTheory/Height/NumberField.lean:130:lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean:43:theorem finrank [NeZero k] [IsCyclotomicExtension {k} ℚ K] : Module.finrank ℚ K = k.totient :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Norm.lean:66:theorem norm_algebraMap (x : 𝓞 K) : norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L := by
.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:179:theorem finrank (hirr : Irreducible (cyclotomic n K)) : finrank K L = n.totient := by
.lake/packages/mathlib/Mathlib/Order/Interval/Set/ProjIcc.lean:42:def projIci (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩
.lake/packages/mathlib/Mathlib/Order/Interval/Set/ProjIcc.lean:165:theorem IciExtend_apply (f : Ici a → β) (x : α) : IciExtend f x = f ⟨max a x, le_max_left _ _⟩ :=
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Incenter.lean:914:lemma ExcenterExists.affineSpan_faceOpposite_eq_orthRadius [hf : Fact (Module.finrank ℝ V = n)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Incenter.lean:924:lemma affineSpan_faceOpposite_eq_orthRadius_insphere [Fact (Module.finrank ℝ V = n)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Incenter.lean:1324:lemma affineSpan_pair_eq_orthRadius [Fact (Module.finrank ℝ V = 2)] (signs : Finset (Fin 3))
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Incenter.lean:1332:lemma affineSpan_pair_eq_orthRadius_insphere [Fact (Module.finrank ℝ V = 2)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Basic.lean:176:theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2)
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:307:lemma inter_orthRadius_eq_of_dist_le_radius_of_norm_eq_one [hf2 : Fact (Module.finrank ℝ V = 2)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:348:lemma inter_orthRadius_eq_of_dist_le_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:361:lemma ncard_inter_orthRadius_eq_two_of_dist_lt_radius [hf2 : Fact (Module.finrank ℝ V = 2)]
.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:378:lemma ncard_inter_orthRadius_le_two [hf2 : Fact (Module.finrank ℝ V = 2)]
.lake/packages/mathlib/Mathlib/Order/Interval/Set/UnorderedInterval.lean:277:lemma Ioc_subset_uIoc : Ioc a b ⊆ Ι a b := Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
.lake/packages/mathlib/Mathlib/Order/Interval/Set/UnorderedInterval.lean:278:lemma Ioc_subset_uIoc' : Ioc a b ⊆ Ι b a := Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:273:protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:360:theorem norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm := by
.lake/packages/mathlib/Mathlib/Tactic/Ring/Common.lean:600:theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:440:theorem norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m := by
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:66:theorem mul_le_mul_of_nonneg_left [Mul α] [Zero α] [Preorder α] [PosMulMono α]
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:70:theorem mul_le_mul_of_nonneg_right [Mul α] [Zero α] [Preorder α] [MulPosMono α]
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Measure.lean:318:theorem inv_def (μ : Measure G) : μ.inv = Measure.map inv μ := rfl
.lake/packages/mathlib/Mathlib/Tactic/Translate/ToAdditive.lean:78:@[to_additive (attr := simp)] lemma mul_one' {G : Type*} [Group G] (x : G) : x * 1 = x := mul_one x
.lake/packages/mathlib/Mathlib/RingTheory/Adjoin/Dimension.lean:46:theorem finrank_sup_le_of_free : finrank R ↥(A ⊔ B) ≤ finrank R A * finrank R B := by
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:217:protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ENNRealLogExp.lean:47:@[simp] lemma ENNReal.exp_log (x : ℝ≥0∞) : exp (log x) = x := by
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:193:theorem exp_add (hI : DividedPowers I) (ha : a ∈ I) (hb : b ∈ I) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:58:theorem exp_log (hx : 0 < x) : exp (log x) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:160:theorem log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [← exp_le_exp, exp_log hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:162:theorem log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [← exp_lt_exp, exp_log hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:164:theorem le_log_iff_exp_le (hy : 0 < y) : x ≤ log y ↔ exp x ≤ y := by rw [← exp_le_exp, exp_log hy]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:166:theorem lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [← exp_lt_exp, exp_log hy]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:91:lemma exp_le_exp {a b : EReal} (h : a ≤ b) : exp a ≤ exp b := by simpa
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:109:lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:103:protected lemma mul_one (x : ⨂[R] i, A i) : mul x (tprod R 1) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:95:theorem finite_integral_one_add_norm {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:134:theorem integrable_one_add_norm {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:144:theorem integrable_rpow_neg_one_add_norm_sq {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
.lake/packages/mathlib/Mathlib/RingTheory/PowerBasis.lean:91:theorem finrank [StrongRankCondition R] (pb : PowerBasis R S) :
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/NonZeroDivisors.lean:68:protected theorem inv_def {r : R} {s : R⁰} :
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:384:protected theorem mul_one : I * 1 = I :=
.lake/packages/mathlib/Mathlib/RingTheory/IsAdjoinRoot.lean:482:theorem finrank [StrongRankCondition R] : Module.finrank R S = f.natDegree :=
.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:526:theorem finrank_of_isFractionRing : Module.finrank R' S' = Module.finrank R S := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean:171:lemma exp_log [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] (a : A)
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:379:protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
.lake/packages/mathlib/Mathlib/RingTheory/PicardGroup.lean:253:protected theorem finrank_eq_one [StrongRankCondition R] [Free R M] : finrank R M = 1 := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean:201:`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial.lean:55:theorem finrank_eq_zero [Nonempty σ] : Module.finrank K (MvPolynomial σ K) = 0 :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial.lean:59:theorem finrank_eq_one [IsEmpty σ] : Module.finrank K (MvPolynomial σ K) = 1 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:663:theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:275:protected theorem mul_one : φ * 1 = φ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:811:theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:41:theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Different.lean:456:      LinearMap.toSpanSingleton_apply, Algebra.smul_def m, mul_one,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean:65:lemma sinc_le_one (x : ℝ) : sinc x ≤ 1 := (abs_le.mp (abs_sinc_le_one x)).2
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean:67:lemma neg_one_le_sinc (x : ℝ) : -1 ≤ sinc x := (abs_le.mp (abs_sinc_le_one x)).1
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:1197:theorem exp_antiperiodic : Function.Antiperiodic exp (π * I) := by simp [exp_add, exp_mul_I]
.lake/packages/mathlib/Mathlib/GroupTheory/Coprod/Basic.lean:594:theorem inv_def (w : FreeMonoid (G ⊕ H)) :
.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Content.lean:139:theorem content_X : content (X : R[X]) = 1 := by rw [← mul_one X, content_X_mul, content_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:151:@[simp] lemma finrank_lattice : finrank ℤ L.lattice = 2 := finrank_eq_card_basis L.latticeBasis
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:217:lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:641:theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:700:@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:708:@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq <| norm_mul a b
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:692:theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:109:lemma integrableOn_ball_of_norm_le_rpow (hd : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α r : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:134:theorem locallyIntegrable_of_norm_le_rpow (hdim : 1 ≤ Module.finrank ℝ E) {f : E → F} {C α : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:254:theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean:241:theorem MemSobolev.fourier_memL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
.lake/packages/mathlib/Mathlib/Analysis/Complex/Circle.lean:128:theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:56:theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:62:theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:85:lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖ = q := norm_of_nonneg q.cast_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:126:lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Int.lean:30:theorem norm_eq_abs (n : ℤ) : ‖n‖ = |(n : ℝ)| :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Int.lean:33:theorem norm_natCast (n : ℕ) : ‖(n : ℤ)‖ = n := by simp [Int.norm_eq_abs]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean:72:def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean:78:theorem coe_toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean:83:theorem toLinearIsometryEquiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean:101:def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean:96:@[to_additive IsCompact.exists_bound_of_continuousOn]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean:97:lemma IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:238:lemma norm_fst_le (x : E × F) : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:240:lemma norm_snd_le (x : E × F) : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:108:lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:112:lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:61:theorem det_reflection : LinearMap.det K.reflection.toLinearMap = (-1) ^ finrank 𝕜 Kᗮ := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:77:theorem linearEquiv_det_reflection : K.reflection.det = (-1) ^ finrank 𝕜 Kᗮ := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:127:theorem finrank_orthogonal_span_singleton {n : ℕ} [_i : Fact (finrank 𝕜 E = n + 1)] {v : E}
.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean:514:theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Box/Basic.lean:197:protected theorem isCompact_Icc (I : Box ι) : IsCompact (Box.Icc I) :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:212:private noncomputable def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:217:private theorem hasEigenvalue_unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:224:private theorem exists_unsortedEigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:278:noncomputable irreducible_def eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:282:theorem exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:288:theorem card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:299:noncomputable irreducible_def eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:305:theorem hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:311:theorem eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:319:theorem hasEigenvalue_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:324:theorem apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:331:theorem eigenvectorBasis_apply_self_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:348:theorem toMatrix_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:356:theorem charpoly_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:361:theorem roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:368:theorem sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean:390:theorem det_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:107:theorem exp_add : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:207:nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:316:theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:73:protected theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:106:protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:113:lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := Complex.norm_of_nonneg n.cast_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:139:lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg q.cast_nonneg
.lake/packages/mathlib/Mathlib/GroupTheory/CoprodI.lean:224:theorem inv_def (x : CoprodI G) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:1060:irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:1145:def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean:40:def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| finrank ℝ E) :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:485:theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:629:theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Lemmas.lean:52:lemma RCLike.finrank_le_two : Module.finrank ℝ K ≤ 2 :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:114:theorem singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:119:theorem singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:123:theorem singularValues_of_finrank_le {i : ℕ} (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:127:theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:131:theorem sq_singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:135:theorem hasEigenvalue_adjoint_comp_self_sq_singularValues {n : ℕ} (hn : n < finrank 𝕜 E) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:172:theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:189:theorem support_singularValues : T.singularValues.support = Finset.range (finrank 𝕜 T.range) := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean:200:theorem singularValues_finrank_range_self : T.singularValues (finrank 𝕜 T.range) = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean:148:protected def finOrthonormalBasis (hn : 0 < n) (h : finrank ℝ E = n) (x : Orientation ℝ E (Fin n)) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean:156:theorem finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank ℝ E = n)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean:179:theorem volumeForm_zero_pos [_i : Fact (finrank ℝ E = 0)] :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean:184:theorem volumeForm_zero_neg [_i : Fact (finrank ℝ E = 0)] :
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean:70:lemma Hom.inv_def (f : X ⟶ G) : f⁻¹ = f ≫ ι := rfl
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean:181:lemma GrpObj.inv_eq_inv : ι = (𝟙 G)⁻¹ := by simp [Hom.inv_def]
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean:240:attribute [local simp] Hom.inv_def in
```

### Command 26

```sh
rg -n '^(noncomputable )?(def|theorem|structure) (inverseChartPullbackVolumeDensity_pos|ClosedSmoothRiemannianMetric|IsClosedNormalizedRicciFlowSolutionAt|meanScalar|normalizedTracelessRicciEvolutionReactionAt|closedMetricFiniteVolumeMeasure|HamiltonConvergencePinchedLimit3|UniversalHamiltonConvergenceStatement|coordinateLebesgueMeasure)\b' Poincare
```

Exit 0.

```text
Poincare/Global/NormalizedFlowPinchingLimit.lean:151:theorem ClosedSmoothRiemannianMetric.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero
Poincare/Global/HausdorffInverseChartGramContinuity.lean:135:theorem inverseChartPullbackVolumeDensity_pos
Poincare/Global/SphereTheorem.lean:118:def HamiltonConvergencePinchedLimit3 (M : Type u)
Poincare/Global/HausdorffCoordinateDensityVariation.lean:67:noncomputable def coordinateLebesgueMeasure
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:734:theorem ClosedSmoothRiemannianMetric.laplacianAt_finsetSum
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:127:def closedMetricFiniteVolumeMeasure
Poincare/Global/ScalarEvolution.lean:192:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
Poincare/Global/ScalarEvolution.lean:208:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:260:noncomputable def normalizedTracelessRicciEvolutionReactionAt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:117:theorem ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:149:theorem ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/ScalarIntegral.lean:65:noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:107:theorem ClosedSmoothRiemannianMetric.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:141:theorem ClosedSmoothRiemannianMetric.pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:168:theorem ClosedSmoothRiemannianMetric.hasPosRicciAt_of_scalar_lower_of_traceless_lt
Poincare/Global/HamiltonFrontStatements.lean:83:def UniversalHamiltonConvergenceStatement : Prop :=
```

### Command 27

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 1.

Output was empty.

### Command 28

```sh
git diff --check
```

Exit 0.

Output was empty.

### Command 29

```sh
git diff --name-status b358db205a55844fa09cf253630ec4cc6525d406
```

Exit 0.

```text
A	Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

### Command 30

```sh
git log --oneline b358db205a55844fa09cf253630ec4cc6525d406..HEAD
```

Exit 0.

```text
7bbe4fb4 Derive universal Hamilton convergence from the reduced core
39af7098 Derive the Hamilton endpoint from the smaller reaction core
5f9fe347 Remove local chart domination from the Hamilton reaction core
dbf7d578 Discharge local chart density domination from joint metric entries
185191b0 Bound moving inverse chart densities by a fixed-time density
98e4a90c Prove logarithmic first variation of inverse chart density
73e5f21a Prove joint continuity of intrinsic metric time-variation trace
```

### Command 31

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/import-probe.lean
```

Exit 0.

```text
DECL Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3' AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement' AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.FiniteExtendedChartCover.inverseChart.congr_simp AXIOMS [propext, Classical.choice, Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core' AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore' AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.inverseChartDensity_le_exp_mul AXIOMS [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3' AXIOMS [propext, Classical.choice, Quot.sound]
Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries.{u} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) :
  have C := Poincare.compactFiniteExtendedChartCover;
  ∀ (t : ℝ),
    ∃ s ∈ 𝓝 t,
      ∃ B,
        (∀ (i : Fin C.chartCount), Integrable (B i) (Poincare.coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
          ∀ (i : Fin C.chartCount),
            ∀ᵐ (z : ↑(C.coordinateDomain i)) ∂Poincare.coordinateLebesgueMeasure (C.coordinateDomain i),
              ∀ τ ∈ s, ‖Poincare.finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z
Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3' M) : Poincare.HamiltonReactionCore3 M
Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'.{u, v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3' M) :
  Poincare.HamiltonConvergencePinchedLimit3 M
Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore'.{u, v}
  (h : Poincare.HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement') :
  Poincare.UniversalHamiltonConvergenceStatement
def Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'.{u, v} : (M : Type u) →
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
                            Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2
```

### Command 32

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-density-evidence/import-axioms.lean
```

Exit 0.

```text
'Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.inverseChartDensity_le_exp_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteExtendedChartCover.inverseChart.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Command 33

```sh
git status --short --branch
```

Exit 0.

```text
## worker/hamilton-chart-density-local-domination
```

### Command 34

```sh
git rev-parse HEAD
```

Exit 0.

```text
7bbe4fb4b74eb0d2b142272ea79cdf856578bfc0
```

### Command 35

```sh
git -C .lake/packages/mathlib rev-parse HEAD
```

Exit 0.

```text
7175569c842f9164564bd76ff8b207e7b4705522
```

### Command 36

```sh
cat lean-toolchain
```

Exit 0.

```text
leanprover/lean4:v4.30.0-rc2
```

### Command 37

```sh
rg -n '^(theorem|def) ' Poincare/Global/HamiltonChartDensityLocalDomination.lean
```

Exit 0.

```text
28:theorem continuous_trace_timeDeriv
95:theorem hasDerivAt_log_inverseChartDensity
109:theorem inverseChartDensity_le_exp_mul
151:theorem localBound_of_jointMetricEntries
197:def HamiltonReactionCore3' (M : Type u)
221:theorem hamiltonReactionCore3_of_core'
231:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'
239:def UniversalHamiltonReactionCoreStatement' : Prop :=
248:theorem universalHamiltonConvergence_of_universalHamiltonReactionCore'
```

## Appendix B. Imported signature and axiom probe payloads

### import-probe.lean

```lean
import Poincare.Global.HamiltonChartDensityLocalDomination
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HamiltonChartDensityLocalDomination
    | throwError "module not found"
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"DECL {n} AXIOMS {axs}"
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "unexpected footprint for {n}"

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

example
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z) :=
  HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint
end Poincare
#check Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries
#check Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'
#check Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'
#check Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore'
#print Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'
```

### import-axioms.lean

```lean
import Poincare.Global.HamiltonChartDensityLocalDomination
#print axioms Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv
#print axioms Poincare.HamiltonChartDensityLocalDomination.hasDerivAt_log_inverseChartDensity
#print axioms Poincare.HamiltonChartDensityLocalDomination.inverseChartDensity_le_exp_mul
#print axioms Poincare.HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries
#print axioms Poincare.HamiltonChartDensityLocalDomination.HamiltonReactionCore3'
#print axioms Poincare.HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'
#print axioms Poincare.HamiltonChartDensityLocalDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'
#print axioms Poincare.HamiltonChartDensityLocalDomination.UniversalHamiltonReactionCoreStatement'
#print axioms Poincare.HamiltonChartDensityLocalDomination.universalHamiltonConvergence_of_universalHamiltonReactionCore'
#print axioms Poincare.FiniteExtendedChartCover.inverseChart.congr_simp
```

## Appendix C. Final source diff

```diff
diff --git a/Poincare/Global/HamiltonChartDensityLocalDomination.lean b/Poincare/Global/HamiltonChartDensityLocalDomination.lean
new file mode 100644
index 00000000..52174eb6
--- /dev/null
+++ b/Poincare/Global/HamiltonChartDensityLocalDomination.lean
@@ -0,0 +1,256 @@
+import Poincare.Global.HamiltonReactionCoreReduction
+import Poincare.Global.HausdorffInverseChartGramContinuity
+import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
+
+noncomputable section
+open Bundle FiberBundle Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+set_option autoImplicit false
+universe u v
+namespace Poincare.HamiltonChartDensityLocalDomination
+
+section DimensionGeneral
+
+variable {n : ℕ} {M : Type u}
+variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+variable [MeasurableSpace M] [BorelSpace M]
+variable [ChartedSpace (ClosedSmoothModel n) M]
+variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+variable [CompactSpace M] [ConnectedSpace M]
+
+local notation "I" => closedSmoothModelWithCorners n
+local notation "E" => ClosedSmoothModel n
+local notation "TM" => (TangentSpace I : M → Type _)
+
+omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
+  [CompactSpace M] [ConnectedSpace M] in
+/-- The intrinsic time-variation trace is jointly continuous. -/
+theorem continuous_trace_timeDeriv
+    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    Continuous (fun p : ℝ × M ↦
+      traceMetricVariationAt (gt p.1) (timeDerivAt gt p.1) p.2) := by
+  classical
+  apply continuous_iff_continuousAt.mpr
+  rintro ⟨t, x⟩
+  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
+  let b := Module.finBasis ℝ (TM x)
+  have hchart : ContinuousAt (fun p : ℝ × M ↦
+      (p.1, extChartAt I x p.2)) (t, x) :=
+    continuousAt_fst.prodMk (ContinuousAt.comp' (f := fun p : ℝ × M ↦ p.2)
+      (g := fun y ↦ extChartAt I x y) (continuousAt_extChartAt x) continuousAt_snd)
+  have hsource : ∀ᶠ p : ℝ × M in 𝓝 (t, x),
+      p.2 ∈ (extChartAt I x).source :=
+    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
+  have hentry (i j : Fin (Module.finrank ℝ (TM x))) :
+      ContinuousAt (fun p : ℝ × M ↦ gramMatrix (gt p.1) x p.2 i j) (t, x) := by
+    have hc := ContinuousAt.comp' (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
+      ((hjoint t x (b i) (b j)).continuousAt) hchart
+    apply hc.congr_of_eventuallyEq
+    filter_upwards [hsource] with p hp
+    dsimp only [metricEntryJointChart]
+    rw [(extChartAt I x).left_inv hp]
+    rfl
+  have hvariation (i j : Fin (Module.finrank ℝ (TM x))) :
+      ContinuousAt (fun p : ℝ × M ↦
+        timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x) := by
+    have hc := ContinuousAt.comp' (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
+      (continuousAt_joint_timeDeriv_of_joint_contDiffAt_one
+      (fun τ z ↦ metricEntryJointChart gt x (b i) (b j) (τ, z))
+      t (extChartAt I x x) ((hjoint t x (b i) (b j)).of_le (by norm_num))) hchart
+    apply hc.congr_of_eventuallyEq
+    filter_upwards [hsource] with p hp
+    dsimp only [metricEntryJointChart]
+    rw [(extChartAt I x).left_inv hp]
+    rfl
+  let G := fun p : ℝ × M ↦ gramMatrix (gt p.1) x p.2
+  have hG : ContinuousAt G (t, x) :=
+    continuousAt_pi.mpr fun i ↦ continuousAt_pi.mpr fun j ↦ hentry i j
+  have hdet : (G (t, x)).det ≠ 0 :=
+    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
+      (gramMatrix_at_base_isUnit (g := gt t) (x := x)))
+  have hinv : ContinuousAt (fun p ↦ (G p)⁻¹) (t, x) := by
+    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using
+      ((continuous_id.matrix_det.continuousAt.comp hG).inv₀ hdet).smul
+        (continuous_id.matrix_adjugate.continuousAt.comp hG)
+  have hunit : ∀ᶠ p in 𝓝 (t, x), IsUnit (G p) := by
+    filter_upwards [(continuous_id.matrix_det.continuousAt.comp hG).eventually_ne hdet] with p hp
+    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
+  have hsum : ContinuousAt (fun p : ℝ × M ↦
+      ∑ i, ∑ j, (G p)⁻¹ i j *
+        timeDerivAt gt p.1 p.2 (gramFrame x p.2 i) (gramFrame x p.2 j)) (t, x) := by
+    apply tendsto_finsetSum
+    intro i _
+    apply tendsto_finsetSum
+    intro j _
+    exact (continuousAt_pi.mp (continuousAt_pi.mp hinv i) j).mul (hvariation i j)
+  apply hsum.congr_of_eventuallyEq
+  filter_upwards [hunit] with p hp
+  exact traceMetricVariationAt_eq_sum_gram_inv (gt p.1) (timeDerivAt gt p.1) x p.2 hp
+    (timeDerivBilinAt gt p.1 p.2
+      (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
+        ((hjoint p.1 p.2).of_le (by norm_num)))) (by intro a c; rfl)
+
+/-- Taking the logarithm cancels the coordinate density from its first variation. -/
+theorem hasDerivAt_log_inverseChartDensity
+    (C : FiniteExtendedChartCover (n := n) (M := M))
+    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
+    {t : ℝ} (i : Fin C.chartCount) (z : C.coordinateDomain i)
+    (htime : TimeDifferentiableAt gt t (C.inverseChart i z)) :
+    HasDerivAt (fun τ ↦ Real.log (C.inverseChartDensity (gt τ) i z))
+      ((1 / 2 : ℝ) * traceMetricVariationAt (gt t) (timeDerivAt gt t)
+        (C.inverseChart i z)) t := by
+  have hpos : 0 < C.inverseChartDensity (gt t) i z :=
+    inverseChartPullbackVolumeDensity_pos (gt t) (C.anchor i) (C.coordinateTargetPoint i z)
+  convert (C.hasDerivAt_inverseChartDensity i z htime).log hpos.ne' using 1
+  field_simp
+
+/-- An intrinsic trace bound controls density ratios on a unit time strip. -/
+theorem inverseChartDensity_le_exp_mul
+    (C : FiniteExtendedChartCover (n := n) (M := M))
+    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (t K : ℝ) (hK : 0 ≤ K)
+    (hbound : ∀ τ ∈ Icc (t - 1) (t + 1), ∀ x : M,
+      ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ) x‖ ≤ K)
+    (i : Fin C.chartCount) (z : C.coordinateDomain i)
+    {τ : ℝ} (hτ : τ ∈ Icc (t - 1) (t + 1)) :
+    C.inverseChartDensity (gt τ) i z ≤ Real.exp K * C.inverseChartDensity (gt t) i z := by
+  have hderiv (s : ℝ) := hasDerivAt_log_inverseChartDensity C gt i z
+    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
+      ((hjoint s (C.inverseChart i z)).of_le (by norm_num)))
+  have hlog := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun s (_ : s ∈ Icc (t - 1) (t + 1)) ↦ (hderiv s).hasDerivWithinAt)
+    (fun s hs ↦ hbound s hs (C.inverseChart i z)) (convex_Icc (t - 1) (t + 1))
+    (show t ∈ Icc (t - 1) (t + 1) by constructor <;> linarith) hτ
+  have hdist : ‖τ - t‖ ≤ 1 := by
+    rw [Real.norm_eq_abs, abs_le]
+    constructor <;> linarith [hτ.1, hτ.2]
+  have hlogle : Real.log (C.inverseChartDensity (gt τ) i z) ≤
+      K + Real.log (C.inverseChartDensity (gt t) i z) := by
+    have := le_trans (le_abs_self _) (le_trans hlog (mul_le_mul_of_nonneg_left hdist hK))
+    rw [mul_one] at this
+    linarith
+  have hpos (s : ℝ) : 0 < C.inverseChartDensity (gt s) i z :=
+    inverseChartPullbackVolumeDensity_pos (gt s) (C.anchor i) (C.coordinateTargetPoint i z)
+  have := Real.exp_le_exp.mpr hlogle
+  simpa only [Real.exp_add, Real.exp_log (hpos τ), Real.exp_log (hpos t)] using this
+
+end DimensionGeneral
+
+section DimensionThree
+variable {M : Type u}
+variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+variable [MeasurableSpace M] [BorelSpace M]
+variable [ChartedSpace (ClosedSmoothModel 3) M]
+variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+omit [SimplyConnectedSpace M] in
+/-- Compactness and joint metric entries supply the local integrable envelope. -/
+theorem localBound_of_jointMetricEntries
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
+    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
+      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
+        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
+        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
+          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z) := by
+  classical
+  intro C t
+  have hcont := (continuous_trace_timeDeriv gt hjoint).const_mul (1 / 2 : ℝ)
+  obtain ⟨L, hL⟩ := ((isCompact_Icc : IsCompact (Icc (t - 1) (t + 1))).prod
+    (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hcont.continuousOn
+  let K := max L 0
+  have hK : 0 ≤ K := le_max_right _ _
+  have hbound (τ : ℝ) (hτ : τ ∈ Icc (t - 1) (t + 1)) (x : M) :
+      ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ) x‖ ≤ K :=
+    (hL (τ, x) ⟨hτ, mem_univ x⟩).trans (le_max_left _ _)
+  refine ⟨Icc (t - 1) (t + 1), Icc_mem_nhds (by linarith) (by linarith),
+    fun i z ↦ (K * Real.exp K) * C.inverseChartDensity (gt t) i z, ?_, ?_⟩
+  · intro i
+    exact (HamiltonReactionCoreReduction.inverseChartDensity_integrable C (gt t) i).const_mul _
+  · intro i
+    apply Eventually.of_forall
+    intro z τ hτ
+    have hdensity := inverseChartDensity_le_exp_mul C gt hjoint t K hK hbound i z hτ
+    have hnonneg := C.inverseChartDensity_nonneg (gt τ) i z
+    calc
+      ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ =
+          C.inverseChartDensity (gt τ) i z *
+            ‖(1 / 2 : ℝ) * traceMetricVariationAt (gt τ) (timeDerivAt gt τ)
+              (C.inverseChart i z)‖ := by
+        unfold finiteExtendedChartFrameDensityDerivative
+        rw [show (1 / 2 : ℝ) * C.inverseChartDensity (gt τ) i z *
+            traceMetricVariationAt (gt τ) (timeDerivAt gt τ) (C.inverseChart i z) =
+            C.inverseChartDensity (gt τ) i z * ((1 / 2 : ℝ) *
+              traceMetricVariationAt (gt τ) (timeDerivAt gt τ) (C.inverseChart i z)) by ring]
+        rw [norm_mul, Real.norm_of_nonneg hnonneg]
+      _ ≤ C.inverseChartDensity (gt τ) i z * K :=
+        mul_le_mul_of_nonneg_left (hbound τ hτ _) hnonneg
+      _ ≤ (Real.exp K * C.inverseChartDensity (gt t) i z) * K :=
+        mul_le_mul_of_nonneg_right hdensity hK
+      _ = (K * Real.exp K) * C.inverseChartDensity (gt t) i z := by ring
+
+/-- The reaction core with its now-derived chart domination clause removed. -/
+def HamiltonReactionCore3' (M : Type u)
+    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+    [MeasurableSpace M] [BorelSpace M]
+    [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
+  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (metric : K → ClosedSmoothRiemannianMetric 3 M)
+    (parameter : Ici (0 : ℝ) → K) (c rate : ℝ),
+      Continuous parameter ∧
+      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
+      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
+      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
+      0 < rate ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
+        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
+          -rate * (gt t).tracelessRicciNormSqAt x) ∧
+      Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) ∧
+      Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
+      Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
+
+/-- Joint entries reconstruct the removed domination clause on the same flow. -/
+theorem hamiltonReactionCore3_of_core'
+    (h : HamiltonReactionCore3'.{u, v} M) : HamiltonReactionCore3.{u, v} M := by
+  rcases h with ⟨K, topK, compactK, gt, metric, parameter, c, rate,
+    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction,
+    hmeasure, hscalar, htraceless⟩
+  exact ⟨K, topK, compactK, gt, metric, parameter, c, rate,
+    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction,
+    hmeasure, hscalar, htraceless, localBound_of_jointMetricEntries gt hjoint⟩
+
+/-- The reduced core reaches the existing Hamilton pinched-limit endpoint. -/
+theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'
+    (h : HamiltonReactionCore3'.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
+  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3
+    (hamiltonReactionCore3_of_core' h)
+
+end DimensionThree
+
+/-- Universal existence of the reaction core without chart domination. -/
+def UniversalHamiltonReactionCoreStatement' : Prop :=
+  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
+    [MeasurableSpace N] [BorelSpace N]
+    [ChartedSpace (ClosedSmoothModel 3) N]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
+      HamiltonReactionCore3'.{u, v} N
+
+/-- Universal existence of the smaller core implies universal Hamilton convergence. -/
+theorem universalHamiltonConvergence_of_universalHamiltonReactionCore'
+    (h : UniversalHamiltonReactionCoreStatement'.{u, v}) :
+    UniversalHamiltonConvergenceStatement.{u} := by
+  intro N _ _ _ _ _ _ _ _
+  letI : MeasurableSpace N := borel N
+  letI : BorelSpace N := ⟨rfl⟩
+  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3' (h N)
+
+end Poincare.HamiltonChartDensityLocalDomination
```
