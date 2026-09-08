# Uniform buffered pair agreement: proved

Date: 2026-09-08. Branch: `worker/uniform-buffered-pair-agreement`.
Base: `f1279a9cce2ad397a322165bb6ade9379dffeac2`.
Verified proof head: `3c7692e25728c92db013aaf9313795b585bfb173`.

Both frozen targets are proved in `Poincare.CartanSuppliedUniformPatchSwitch`:

```lean
theorem uniformBufferedPairAgreement_of_constantCurvature
    (hcurv : HasConstantSectionalCurvature3 g 1) (B : QuantitativeCover g) :
    CartanSuppliedUniformPatchSwitch.UniformBufferedPairAgreement B

theorem exists_switchControl : HasConstantSectionalCurvature3 g 1 →
    ∀ B : QuantitativeCover g, Nonempty (SwitchControl B)
```

The signature probe copies these types into `example` declarations and applies
the new theorems. It also probes the expanded, original pair-agreement definition,
with radius before both anchors and every alignment. No existing definition was
changed or copied into a replacement definition.

The only new Lean file is
`Poincare/Global/CartanSuppliedBufferedPairAgreement.lean`, importing
`CartanSuppliedUniformPatchSwitch`. No existing Lean file or root import changed.
This report is the handoff under the narrower worker scope; `HANDOFF.md` was not
edited. The initial worktree was clean at the base above. `git worktree list
--porcelain` confirmed the isolated worker branch. No merge or acceptance is claimed.

## Checked mathematics

1. `patchFrame_chartTransition` proves that the derivative between two fixed
   hosts is exactly the change between their stored velocity frames. The proof
   differentiates the chart composition identity on the actual overlap.
2. `exists_uniform_chartTransition_bound` bounds that derivative on an arbitrary
   compact overlap, before selecting an anchor.
3. `exists_uniform_transported_flow_radius` uses the compact overlap's positive
   distance from the complement of the second patch's anchors and the retained
   full-time displacement estimate. One velocity radius keeps every trajectory
   in the double cutoff-one region. The chart transition transports the
   normalized geodesic equation on all of `[0,1]`, including the within-derivative
   at each endpoint.
4. `exists_uniform_endpoint_chartTransition` combines this transport with a
   uniform domain for the second endpoint and the transition operator bound.
   Grönwall uniqueness identifies the two normalized trajectories. Both actual
   endpoint source memberships accompany the endpoint equality. The existing
   `geodesic_eqOn_unitInterval` is specialized to the round sphere; this proof
   applies its underlying `ODE_solution_unique_of_mem_Icc_right` argument to
   the arbitrary source metric as well.
5. `exists_uniform_normal_chartTransition` inverts the endpoint equality on the
   actual domains. Its radius precedes the compact-overlap anchor and the
   evaluated point. Its conclusion is
   `D.normal x z = chartTransitionDeriv a b (extChartAt I a x) (C.normal x z)`
   together with both normal source memberships. Swapping the universally
   quantified patches gives the orientation requested in step 1.
6. `linear_chartTransition_of_normal_chartTransition` proves the alignment law
   in the correct target coordinates. The two `linear` outputs are generally
   in different target host frames. Their equation includes the target chart
   derivative; direct coordinate equality is not the definition's law.
7. `uniformBufferedPairAgreement` applies the normal theorem to the source
   buffer intersection and the endpoint theorem to the target buffer
   intersection. A compact uniform alignment bound and small-normal radius
   place every target vector in the sphere endpoint comparison ball, for all
   alignments. The resulting pair radius precedes both moving anchors and `L`.
8. The frozen curvature-facing theorem follows from that stronger comparison.
   Once a quantitative cover supplies the retained cutoff-one patches, this
   comparison needs no additional curvature premise. The frozen curvature
   parameter is retained, producing one unused-variable warning.
9. `exists_switchControl` applies the existing
   `exists_switchControl_of_uniformBufferedPairAgreement`. That consumer takes
   a finite positive lower bound of the label-pair radii and intersects it with
   `B.step`; `buffered_common_source` supplies the required common-source ball.

There is no remaining resisting proposition for this task. The result does not
assert global path independence, sphere recognition, or the Poincaré conjecture.
Root import integration and acceptance belong to the orchestrator.

## Commands and actual output

```sh
LEAN_NUM_THREADS=1 lake env lean --version
```

Exit 0:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

Every theorem was directly compiled before its commit using:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedBufferedPairAgreement.lean
```

The successful logs `01-frame-retry.log`, `02-bound.log`, `03-flow-retry.log`,
`03-flow-endpoints.log`, `04-endpoint-retry2.log`, `05-normal-retry.log`,
`06-linear-retry.log`, and `07-agreement-retry.log` all have exit 0 and empty
output. The final two successful logs, `08-frozen.log` and `09-switch.log`,
have exit 0 and this sole output:

```text
Poincare/Global/CartanSuppliedBufferedPairAgreement.lean:350:7: warning: unused variable `hcurv`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedBufferedPairAgreement
```

Exit 0. Final module output, after replayed dependency warnings:

```text
⚠ [3620/3620] Built Poincare.Global.CartanSuppliedBufferedPairAgreement (3.4s)
warning: Poincare/Global/CartanSuppliedBufferedPairAgreement.lean:350:7: unused variable `hcurv`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3620 jobs).
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedBufferedPairAgreement.lean
git diff --check
git diff f1279a9cce2ad397a322165bb6ade9379dffeac2 --check
```

The token scan returned exit 1 with no matches. Both diff checks returned exit 0
with no output.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-buffered-pair-agreement-evidence/signatures.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-buffered-pair-agreement-evidence/axioms.lean
```

Both exited 0. Signature output was empty. Actual axiom output:

```text
'Poincare.CartanSuppliedBufferedPairAgreement.patchFrame_chartTransition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.exists_uniform_chartTransition_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.exists_uniform_transported_flow_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.exists_uniform_endpoint_chartTransition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.exists_uniform_normal_chartTransition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.linear_chartTransition_of_normal_chartTransition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedBufferedPairAgreement.uniformBufferedPairAgreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.uniformBufferedPairAgreement_of_constantCurvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.exists_switchControl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All nine theorem closures are exactly `[propext, Classical.choice, Quot.sound]`.
No full repository build or root integration audit was launched.

## Compiler retries and evidence

All failed compiler output is preserved under
`/tmp/uniform-buffered-pair-agreement-evidence`:

- `01-frame.log`: the rewritten overlap goal needed the explicit projection
  `hxD.1` rather than `rwa`.
- `03-flow.log`: the locally named transition needed `(n := 3)`.
- `04-endpoint.log`: initial-flow rewriting needed explicit local-state
  equalities; the interior-initial-time uniqueness theorem did not apply at
  time zero; and endpoint extraction needed actual inverse-chart laws.
  The transported-flow lemma was strengthened and verified to retain
  within-derivatives at both endpoints, then the proof used the right-sided
  uniqueness theorem.
- `04-endpoint-retry.log`: the last equality required `endpoint_apply` to
  identify the stored partial homeomorphism with its retained flow endpoint.
- `05-normal.log`: unrestricted rewriting changed the normal vector on the
  right as well; applying `congrArg` to the normal before composing its inverse
  law fixed the dependent expression.
- `07-agreement.log`: the rewrite needed `QuantitativeCover.interp` unfolded.

`06-linear.log` was successful but warned about unused ambient section
instances; the final proof explicitly omits those instances. The final
curvature parameter warning is retained because that parameter is part of
the frozen target. No warning suppression was added.

Probe sources, successful logs, the complete build log, intermediate proof
snippets, and `proof.diff` are in the same evidence directory. The final Lean
diff is also durable in the base-to-proof-head commit range.

## Verified commits

```text
c6c4c081 Prove the transition law for supplied patch velocity frames
43e22dfa Bound chart transition derivatives uniformly on compact overlaps
6e5421a8 Transport fixed-host geodesics uniformly across compact overlaps
1754a1a0 Retain the transported geodesic equation at both interval endpoints
32b98e7a Identify retained endpoints uniformly across fixed chart hosts
c49892b9 Prove uniform chart transition naturality of retained normals
122c9dd6 Make supplied alignment maps commute with both chart transitions
49020893 Prove buffered interpretation agreement uniformly over anchors and alignments
acbfb92a Expose the frozen constant curvature buffered agreement target
3c7692e2 Construct the frozen uniform supplied patch switch control
```

The transported-flow theorem was strengthened in its own additional verified
commit. Each other new theorem has its own verified commit.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedBufferedPairAgreement.lean
```

Then rerun the focused build and the two signature probes above from the
recorded base plus this branch's proof commits. The original task-12
`CartanSuppliedUniformPatchSwitch.exists_switchControl` is now available after
importing the new module. Continue with the dependent supplied-patch schedule
task only after independent acceptance and integration.
