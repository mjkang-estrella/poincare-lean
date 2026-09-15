# Hamilton auxiliary-quantity evolution: verified partial, strict damping blocked

Date: 2026-09-15. Base: `330ec679dc5405534c6c9486034f57183936f8f0`.
Branch: `worker/hamilton-auxiliary-quantity-evolution`.
Proof head: `56b75aeb`.

The exact stop condition for a blocked attempt is met. The intrinsic quotient
rule and normalized scalar-gradient quotient evolution are proved and committed.
Strict derivative-energy damping and the auxiliary-quantity inequality remain
open. This is a worker result awaiting independent review, not acceptance or
integration. No existing Lean file or frozen contract was edited.

## 1. Committed results

The only production module added is
`Poincare/Global/HamiltonScalarGradientEstimate.lean`.
It imports `Poincare.Global.IntrinsicBochnerScalarGradient`.

| Commit | Verified declarations |
| --- | --- |
| `67621ed8` | `Poincare.HamiltonScalarGradientEstimate.laplacian_div`, `Poincare.HamiltonScalarGradientEstimate.heatOperator_div`, `Poincare.HamiltonScalarGradientEstimate.gradient_div_pairing`, `Poincare.HamiltonScalarGradientEstimate.heatOperator_div_expanded` |
| `6f3ba110` | `Poincare.HamiltonScalarGradientEstimate.scalarGradientQuotient_evolution`, `Poincare.HamiltonScalarGradientEstimate.scalarGradientQuotient_evolution_of_normalizedFlow` |
| `56b75aeb` | `Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_le_cubic`, `Poincare.HamiltonScalarGradientEstimate.factorThree_damping_iff`, `Poincare.HamiltonScalarGradientEstimate.factorTwentySevenths_damping` |

All nine emitted declarations, including any compiler-generated declarations,
were checked with exact dependency equality. The final module emits only these
nine declarations. Each has `[propext, Classical.choice, Quot.sound]`.

### Quotient rules

Write `D = ∂t − Δ`. For spatial C² functions with a nowhere-zero denominator
on the slice and pointwise time derivatives, the proved drift rule is

```text
D(f/h) = Df/h − f Dh/h² + 2⟨∇(f/h),∇h⟩/h.
```

The expanded rule is

```text
D(f/h) = Df/h − f Dh/h²
         + 2⟨∇h,∇f⟩/h² − 2f|∇h|²/h³.
```

These are intrinsic Laplacian identities. The proof differentiates the product
`(f/h)h = f`, derives the gradient pairing from the same product, and combines
that spatial calculation with the actual time quotient derivative. There is no
assumed quotient-Laplacian identity.

### Normalized scalar-gradient quotient

Let `R` be scalar curvature, `S=|∇R|²`, `N=|Ric|²`, `Q=S/R`, and `r` the
mean scalar curvature. Let `H=|∇²R|²`, expressed literally in the theorem by
the metric-dual trace of the covariant derivative of the gradient.
The proved identity is

```text
D Q = −2H/R + 4⟨∇R,∇N⟩/R − 2SN/R²
      − (4/3)rQ + 2⟨∇R,∇S⟩/R² − 2S²/R³.
```

The first evolution theorem consumes
`Poincare.IntrinsicBochnerScalarGradient.SatisfiesScalarGradientEvolutionAt`,
`Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt`, spatial C³ scalar
regularity, and positivity everywhere on the slice. The second theorem obtains
these inputs from joint C⁵ metric entries and the actual normalized-flow equation.
The spatial C² regularity of `S` comes from
`Poincare.IntrinsicBochnerScalarGradient.gradientNormSq_contMDiffAt_two`.

The coefficient `−(4/3)rQ` is retained. It combines `−2rS` from the landed
gradient evolution and `−(2/3)rR` from scalar evolution.

No numerical `C₁` bound for this full quotient RHS is claimed. The Hessian-square
completion and mixed-gradient Cauchy–Schwarz estimate are still required. In
particular, discarding only `−2H/R` would leave the mixed Hessian term uncontrolled.

## 2. Traceless evolution and exact obstruction

The actual producer printed in `Inventory.out` is
`Poincare.hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries`.
The printed definition `Poincare.normalizedTracelessRicciEvolutionReactionAt`
gives, with `A=|∇Ric|²`, `U=N−R²/3`, and the actual invariant cubic trace `T`,

```text
D U = −2A + (2/3)S + T − (4/3)rU.
```

Here `T` is
`Poincare.ClosedSmoothRiemannianMetric.pinchingTracelessRicciReactionTrace3At`
applied to
`Poincare.ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceCubicAt`.
The proved geometric consequence is

```text
D U ≤ T − (4/3)rU.
```

It uses
`Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt`.
The exact coefficient supplied by this estimate is `c₂=0`.
The stronger claimed form with `T ≤ 4RU` is not proved here; that needs its
curvature/pinching hypotheses and a separate cubic estimate.

The numerical limitation is itself proved:

```text
(∀ A S : ℝ, 0 ≤ A → S ≤ 3A → −2A + (2/3)S ≤ −cA) ↔ c ≤ 0.
```

The test values `A=1`, `S=3` force `0 ≤ −c`. This is a counterexample to a
numerical implication from the factor-three bound, not a geometric
counterexample to the sharper contracted-Bianchi estimate.

The exact resisting geometric target is

```lean
-2 * Poincare.covRicciNormSqAt g x +
    (2 / 3 : ℝ) * Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt g x ≤
  -(2 / 21 : ℝ) * Poincare.covRicciNormSqAt g x
```

The saved `Residual.lean` probe tries the landed factor-three estimate and
linear arithmetic. Its actual compiler result, exit 1, includes

```text
htrace : g.scalarGradNormSqAt x ≤ 3 * Poincare.covRicciNormSqAt g x
a✝ : -(2 / 21) * Poincare.covRicciNormSqAt g x <
       -2 * Poincare.covRicciNormSqAt g x + 2 / 3 * g.scalarGradNormSqAt x
⊢ False
failed
```

The calibration theorem proves that `S ≤ (20/7)A` would imply the desired
`−(2/21)A` damping. Producing that sharper geometric input remains open here.
The declaration catalog was searched first. The nearest trace-bound and
contracted-Bianchi sources were then inspected. The existing theorem
`Poincare.eventually_closedContractedBianchiOneFormAt_canonical` supplies the
contracted divergence identity, but this attempt does not convert it to the
sharper norm inequality. No such sharper bound was found in that scoped search.

## 3. Combination and pinching: not proved

There is no verified positive `c₂`, no verified `C₁`, and no chosen cancellation
constant `K`. Lean division by zero would make `C₁/0=0`; that does not cancel
a positive derivative-energy term and is not used.

There are two further bookkeeping requirements for the next attempt.
The scalar-square evolution gives

```text
D(−ηR²) = 2ηS − 4ηRN + (4/3)ηrR².
```

Consequently, if `D Q ≤ C₁A − (4/3)rQ` and
`D U ≤ −c₂A + 4RU − (4/3)rU` are eventually proved, then for
`F=Q−ηR²+KU` the resulting bound is

```text
D F ≤ (C₁−Kc₂)A + 2ηS − 4ηRN + 4KRU − (4/3)rF.
```

Using `S≤3A` and `N≥R²/3`, with `η≥0`, changes this to

```text
D F ≤ (C₁+6η−Kc₂)A − (4/3)ηR³ + 4KRU − (4/3)rF.
```

Thus cancellation must also account for `2ηS`. One can incorporate it into the
coefficient named `C₁`, or use `K=(C₁+6η)/c₂` after estimating the quotient
alone. This report does not silently reinterpret the task's coefficient.

The checked signature of
`Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement`
is saved in `17-residual.out`. It preserves the improved pinching maximum under
its stated global flow, topology, initial eigenvalue-floor, and admissible
exponent hypotheses. After passing to a pointwise bound `U≤C R^(2−δ)`, the
scalar expression

```text
−(4/3)ηR³ + 4KC R^(3−δ)
```

is bounded above for `η>0`, `δ>0`, and fixed nonnegative `K,C` on `R≥R₀>0`.
The domination argument is not formalized in this module.

On normalized flow, the additional term is `−(4/3)rF`. Positivity of the scalar
curvature makes `r≥0`, so this term is nonpositive where `F≥0`. A maximum-barrier
argument can exploit that sign. A lower scalar floor and improved pinching alone
do not give a time-uniform upper bound for this term where `F<0`; a bound on `r`
or a barrier that handles the zeroth-order term is still needed. The full
normalized RHS is therefore not asserted to have the requested uniform bound.

## 4. Maximum principle and rescaling residual

A maximum-comparison engine already exists. The checked theorem
`Poincare.closedRiemannian_parabolic_exp_decay_continuousOn` proves
`Q(t,x)≤B exp(−rate t)` from slab continuity, spatial C² regularity, time
derivatives, and `∂t Q≤ΔQ−rate Q` on a compact manifold.
For `D F≤C`, set `Q(t,x)=F(t,x)−Ct` and `rate=0`. Spatial constants have zero
Laplacian, giving `F(t,x)≤B+Ct` from an initial uniform bound `F(0,x)≤B`.
This specialization and the regularity inputs for the eventual `F` remain to
be supplied. A new minimum/maximum proof engine is not necessary.

The checked `Poincare.closed_parabolic_min_principle_var` also supports the
variable zeroth-order coefficient. It is used by
`Poincare.hamilton_pinching_preserved` through a constant-minus-quantity barrier.
This is the relevant route for keeping `−(4/3)rF` in the normalized comparison.
A linear-in-time bound on an infinite normalized ray is not a time-uniform
Hamilton estimate.

For the rescaling calculation, let `g̃(s)=a(t)g(t)` with `a>0`, `ds/dt=a`,
and `a'/a=(2/3)r` on the unnormalized flow. Then

```text
R̃=a⁻¹R,   Ñ=a⁻²N,   S̃=a⁻³S,
Q̃=a⁻²Q,   Ũ=a⁻²U,   F̃=a⁻²F,   r̃=a⁻¹r,
(∂s−Δg̃)F̃ = a⁻³(∂t−Δg)F − (4/3)r̃F̃.
```

This calculation explains the explicit normalization term in the proved
quotient identity. It is mathematical bookkeeping here, not a Lean rescaling
theorem. A finite unnormalized lifespan, the time/metric reparameterization,
and the corresponding curvature/gradient transport still need formal proofs.
An unnormalized `S≤ηR³+Cη` becomes `S̃≤ηR̃³+a⁻³Cη`. Removing its additive error
asymptotically requires the scale-growth and scalar-floor inputs; bounded
normalized jets alone do not supply that transfer.

Even after an upper bound `F≤B`, multiplying by `R` first gives
`S≤ηR³+BR` when `K,U≥0`. To obtain the final constant additive error, reserve
part of the requested cubic coefficient and absorb `BR` into that cubic plus
a constant. This final scalar absorption also remains outside the committed
partial result.

## 5. Verification and evidence

Every proof item was compiled, built, dependency-checked, and committed.
Final focused command, exit 0, empty stdout/stderr:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonScalarGradientEstimate.lean
```

Final token command, exit 1 meaning no matches, empty output:

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonScalarGradientEstimate.lean
```

`git diff --check` exited 0 with empty output. The worker gate was also run:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/hamilton-auxiliary-quantity-evolution Poincare.Global.HamiltonScalarGradientEstimate
```

Actual final output, exit 0:

```text
=== GATE: forbidden tokens in Poincare/Global/HamiltonScalarGradientEstimate.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.HamiltonScalarGradientEstimate ===
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3871/3871] Built Poincare.Global.HamiltonScalarGradientEstimate (3.4s)
Build completed successfully (3871 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=9 nonstandard=[]
=== GATE: PASS ===
```

The stricter module-wide audit calls `#print axioms` for every declaration
emitted by the module and requires equality with the three-element set.
It includes internal names and does not merely test that dependencies are allowed.
Command:

```sh
LEAN_NUM_THREADS=1 lake env lean harness/reports/hamilton-auxiliary-quantity-evolution_evidence/Audit.lean
```

Actual final output, exit 0:

```text
'Poincare.HamiltonScalarGradientEstimate.scalarGradientQuotient_evolution_of_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.heatOperator_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.heatOperator_div_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.factorThree_damping_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.scalarGradientQuotient_evolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_le_cubic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.gradient_div_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.laplacian_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.factorTwentySevenths_damping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES_PASS declarations=9
```

Evidence directory:
`harness/reports/hamilton-auxiliary-quantity-evolution_evidence/`.
It retains inventory and residual probe sources, failed compiler outputs,
intermediate dependency diagnostics, successful outputs, and `final-proof.diff`.
The large replayed build logs and the first evolution failure contain compiler-
emitted trailing whitespace. Byte-exact `.gz` copies are tracked; their original
local `.out` files are retained and ignored by Git. Decompress with `gzip -dc`.
The early diagnostic audit intentionally printed failures as warnings and is not
an acceptance record. The final exact audit above is the acceptance evidence.
Local notation and default denominator-discharge helpers initially emitted
extra declarations with smaller dependency sets; the final code avoids those
helpers using direct denominator proofs. No artificial dependency was inserted.
The final build's displayed linter warning comes from replayed imported modules;
the focused new-module compilation is silent.

No root integration checks or full-project acceptance are claimed.

## 6. Exact next action

First rerun:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonScalarGradientEstimate.lean
```

Then append the geometric estimate
`Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt g x ≤
(20/7 : ℝ) * Poincare.covRicciNormSqAt g x`
to this chain, deriving its finite-dimensional tensor estimate from the
contracted-Bianchi identity and symmetric Ricci covariant derivative.
Use `Poincare.HamiltonScalarGradientEstimate.factorTwentySevenths_damping`
to recover `2/21`. The mixed-gradient/Hessian quotient bound is the other
remaining input before choosing `K`.
