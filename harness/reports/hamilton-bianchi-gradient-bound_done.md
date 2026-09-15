# Hamilton Bianchi gradient bound: proved

Date: 2026-09-15.
Base: `8883a941cc3039b585c3e02facd6999555a0a5ec`.
Branch: `worker/hamilton-bianchi-gradient-bound`.
Proof head: `248bed8108857dc48ff4597285b3bd9c47d44832`.

Both requested theorems are proved. This is a worker result awaiting independent
review, not acceptance or integration. The only production Lean edit appends to
`Poincare/Global/HamiltonScalarGradientEstimate.lean`. All existing declarations
and their statements are byte-for-byte preserved. No frozen contract or other
existing Lean file was changed.

## Committed results

Commit `07d5b690` proves:

- `Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_trace_pairing`
- `Poincare.HamiltonScalarGradientEstimate.contractedBianchi_orthogonal_trace`
- `Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_gradient_bound`
- `Poincare.HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq`

Commit `248bed81` proves:

- `Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_damped`

The first target has the dimension-three specialization of the existing
`Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt_le_three_covRicciNormSqAt`
hypotheses, including the Levi-Civita regularity instance. It needs no compactness,
connectedness, measure, or second-countability hypotheses. The existing theorem
was printed before implementation; its full output is preserved in the inventory.

The damping theorem keeps the flow and joint C³ metric-entry hypotheses of
`Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_le_cubic`.
Scalar positivity is unnecessary for this step, so the result holds on every
such slice, including all positive-scalar slices. The cubic term is retained
literally; no additional cubic or pinching estimate is claimed.

## Proof

The repository uses a metric-orthogonal basis with positive diagonal weights
`d i`, rather than a normalized orthonormal basis. The proof works directly in
that basis. With `D a = dR(e_a)` and `C a i j = (∇_{e_a} Ric)(e_i,e_j)`, it derives

```text
Σ_i C a i i / d i = D a
Σ_a C a a j / d a = D j / 2
C a i j = C a j i.
```

The first trace comes from
`Poincare.ClosedSmoothRiemannianMetric.extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace`.
The second follows from
`Poincare.eventually_closedContractedBianchiOneFormAt_canonical` at the point,
transporting the divergence trace through the existing basis-invariance theorem.
Symmetry is supplied by
`Poincare.covTensor2DerivAt_ricciVariationField_symm`.

Set

```text
B a i j = (3/10) δij d i D a
        + (1/20) δai d a D j
        + (1/20) δaj d a D i.
```

Finite weighted sums verify both traces of `B`. They also give
`⟨C,B⟩ = (7/20) Σ_a (D a)²/d a`. Applying the same pairing result to `B`
gives its squared norm with the same coefficient. Expanding the nonnegative
weighted sum of `(C-B)²` proves

```text
|∇R|² ≤ (20/7)|∇Ric|².
```

The landed normalized traceless-energy identity and
`Poincare.HamiltonScalarGradientEstimate.factorTwentySevenths_damping` then give

```text
(∂t − Δ)U ≤ −(2/21)|∇Ric|² + T_cubic − (4/3)rU.
```

## Actual verification

Focused compilation of each committed item exited 0. Final focused command:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonScalarGradientEstimate.lean
```

Actual final output: empty, exit 0, preserved in `23-damped.out.gz`.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.HamiltonScalarGradientEstimate
```

Actual output tail, exit 0:

```text
✔ [3871/3871] Built Poincare.Global.HamiltonScalarGradientEstimate (4.4s)
Build completed successfully (3871 jobs).
```

Earlier lines replay warnings from imported modules. The changed module's
focused compilation is silent.

```sh
LEAN_NUM_THREADS=1 lake env lean harness/reports/hamilton-bianchi-gradient-bound_evidence/Audit.lean
```

This calls `#print axioms` and requires exact dependency-set equality for every
emitted module declaration, including internal proofs. Actual output includes:

```text
'Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_damped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES_PASS declarations=16
```

Exit 0. All 16 emitted declarations have exactly that three-element set:
9 existing declarations, 5 new named theorems, and 2 generated internal proofs.
The first proof commit independently passed the same check with 15 declarations.

```sh
LEAN_NUM_THREADS=1 lake env lean harness/reports/hamilton-bianchi-gradient-bound_evidence/Targets.lean
```

Exit 0. Both literal target assignments compile; the actual fully qualified
signatures are printed in `26-final-targets.out.gz`.

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonScalarGradientEstimate.lean
```

Empty output, exit 1, meaning no matches. `git diff --check` exits 0 with empty output.

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/hamilton-bianchi-gradient-bound Poincare.Global.HamiltonScalarGradientEstimate
```

Actual final output tail, exit 0:

```text
Build completed successfully (3871 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=14 nonstandard=[]
=== GATE: PASS ===
```

The standard gate scans the 14 named declarations. The stricter audit above
also checks the two internal proofs, giving 16.

## Evidence and next action

Evidence is in `harness/reports/hamilton-bianchi-gradient-bound_evidence/`.
It contains the original theorem inventory, all failed and successful compiler
outputs, exact dependency and target probes, and `final-proof.diff.gz` against the
recorded base. Logs and the proof diff are retained byte-for-byte as gzip files to avoid
compiler-output whitespace affecting the diff gate; use `gzip -dc` to read them.

Early proof failures involved denominator cancellation and finite-sum rewriting.
The first exact audits also caught generic simplifier-generated declarations
with smaller dependency sets. Explicit denominator dischargers and direct sum
rewrites removed those helpers. No artificial dependency was inserted.

No blocking identity remains for this task. No root build or project-level
completion claim is made. The next reviewer action is:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonScalarGradientEstimate.lean
```

Then independently check the diff and exact dependency audit from the recorded
base. The Hamilton quotient mixed-gradient/Hessian estimate remains a separate
open task.
