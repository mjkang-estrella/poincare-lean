# Geometric metric transport worker result

Date: 2026-09-07, America/Los_Angeles.
Branch: `worker/metric-transport-2`.
Base: `80fcfacea10aa364aa7bd9d3e7670b136a4f57fb`.
Verified proof head: `51df193e69f0d6e409e0e12ed953a9d8edef891d`.
Status: worker result awaiting independent orchestrator review.

## Outcome

The frozen geometric transport target is proved. Stop condition (a) applies
to the required metric construction and its inner-product formula.
`Poincare.RiemannianMetricInstanceTransportGeometric.transport` constructs the
actual `ClosedSmoothRiemannianMetric` with the second `ChartedSpace` instance.
`transport_inner` proves its inner product is the pullback by `J` in both
arguments. The proof needs no `T2Space` assumption, so it applies in the stated
setting and slightly more generally.

Only one new Lean file was added:
`Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean`.
No existing Lean file or root import was changed. No task, ledger, acceptance
status, or model service was modified. `HANDOFF.md` records this worker result.

The optional distance theorem is not proved. Its exact remaining statement is
`InducedDistanceAgreement`. No separately bundled `LinearIsometryEquiv` for
the two metric-dependent fiber norm instances is supplied. The proved
`transport_inner` gives the inner-product preservation equation for `J`.
No conditional `target_of_resisting` wrapper is needed: the required transport
is unconditional under atlas compatibility, not a partial construction with
smoothness left as an input.

## Verified mathematical chain

1. `commonCharts` enlarges the original atlas to its smooth maximal atlas while
   retaining its preferred charts. Its smoothness reuses
   `ControlledChartInstance.isManifold_and_maximalAtlas_eq`.
2. `D` is the common tangent core's transition derivative. `D_comp` and
   `D_self` give its cocycle and identity laws. `D_eq_fderiv` identifies it
   with the ordinary derivative in the boundaryless model.
3. `J` is a continuous linear equivalence from new preferred coordinates to
   old preferred coordinates. Its inverse is the reverse transition.
   `J_apply` proves exactly
   `J x v = fderiv ℝ (inst.chartAt x ∘ (inst'.chartAt x).symm) (inst'.chartAt x x) v`.
4. `J_inverse_trivialization` and `J_trivialization` prove the cocycle bridges
   on the overlap of the old and new anchor-chart sources.
   `tangentCoordinates_transport` states the forward bridge using the actual
   tangent-bundle trivializations for the explicitly selected instances.
5. `coefficients_transportedInner` proves that the new hom-bundle coefficients
   at anchor `a` are the old coefficients pulled back by
   `D (newChart a) (oldChart a) x`. This includes the moving preferred charts
   through `J x`; no raw-fiber identification is used as a geometric comparison.
6. `contMDiffAt_D` proves smoothness of that fixed-anchor derivative on the
   overlap. `contMDiffAt_pull` proves smoothness of bilinear pullback.
   `modelContMDiffAt_iff` uses
   `contMDiffWithinAt_iff_source_of_mem_maximalAtlas` to transfer vector-valued
   smoothness between the two source instances.
7. `transportedInner_contMDiff` uses the coefficient identity near each anchor
   and `Bundle.contMDiffAt_section` to prove the actual new hom-bundle section
   smooth. `transport` transfers symmetry and positivity through `J`; its
   unit ball is bounded because it is contained in the inverse-`J` image of
   the old unit ball. `transport_inner` is the required formula.

The explicit instance arguments and local `letI` bindings matter. Lean's
ordinary pretty-printer hides them in `#check`; the source and the checked
return type distinguish `inst` and `inst'` throughout.

## Commits

- `d56d211d`: common-core cocycle, invertible `J`, derivative formula and bridges.
- `0559e20f`: bilinear pullback and hom-bundle coefficient identity.
- `611b9b50`: smooth fixed-chart derivatives and bilinear pullbacks.
- `43a93968`: source-atlas smoothness equivalence and smooth transported section.
- `82a700ba`: metric construction and `transport_inner`.
- `51df193e`: actual tangent-trivialization bridge and optional distance statement.

## Actual acceptance commands and output

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean
```

Exit 0, empty stdout/stderr. Final direct-elaboration output is preserved in
`/tmp/metric-transport-2-15.log`.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.RiemannianMetricInstanceTransportGeometric
```

Exit 0, preserved in `/tmp/metric-transport-2-build.log`:

```text
✔ [2704/2704] Built Poincare.Global.RiemannianMetricInstanceTransportGeometric (5.7s)
Build completed successfully (2704 jobs).
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean
```

Exit 1, empty output: no forbidden tokens matched.

```sh
git diff --check
```

Exit 0, empty output.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/metric-transport-2-axioms.lean
```

Exit 0. The probe imports the new module and runs `#print axioms` on all
28 new definitions, instances, and theorems. It also runs `#check` on
`J_apply`, `tangentCoordinates_transport`, `coefficients_transportedInner`,
`transportedInner_contMDiff`, `transport`, `transport_inner`, and
`InducedDistanceAgreement`. Full output is preserved in
`/tmp/metric-transport-2-axioms.log`. Actual axiom output:

```text
'Poincare.RiemannianMetricInstanceTransportGeometric.commonCharts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.commonCharts_isManifold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.D' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.D_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.D_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.oldChart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.pull' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.coefficients_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.D_eq_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.contMDiffAt_D' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.contMDiffAt_pull' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.sectionContMDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.sectionContMDiff_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.tangentCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.newChart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.J' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.J_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.J_inverse_trivialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.J_trivialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.transportedInner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.coefficients_transportedInner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.modelContMDiffAt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.transportedInner_contMDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.transport_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.tangentCoordinates_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.RiemannianMetricInstanceTransportGeometric.InducedDistanceAgreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All 15 new theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`, as are all 13 definitions/instances.
No root integration audit or full-project build was run by this worker.

## Failed compiler evidence

Intermediate compiler outputs are preserved without overwriting at
`/tmp/metric-transport-2-01.log` through `/tmp/metric-transport-2-15.log`.
Failed elaborations were 01, 02, 03, 05, 06, 08, 09, 11, and 13. Successful
stages were 04, 07, 10, 12, 14, and 15. These failures were repaired before
committing their stage.

The main Lean issues were explicit instance selection, converting the core's
within derivative to the ordinary derivative, the `∞ + 1 = ∞` manifold
instance, and the distinction between pointwise rewriting and rewriting an
entire function. One inferred `clm_precomp` codomain also timed out at 200,000
heartbeats; specifying `F₃ := ℝ` resolved it without increasing the limit.
The final file has no timeout override.

For example, attempt 13 rejected constructing a new-instance metric while
the old instance was active. Actual compiler output:

```text
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:266:9: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this
inferred
  inst'
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:272:2: error: No goals to be solved
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:283:4: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this
inferred
  inst'
```

The corrected construction proves the algebraic fields under `inst`, then
installs `inst'` and its verified smoothness instance before constructing the
record. `transport_inner` also selects each instance explicitly when reading
its corresponding metric's `inner` field.

The complete proof diff against the recorded base is preserved in
`/tmp/metric-transport-2-final.diff` and by the six proof commits above.

## Optional remaining distance statement

The exact Lean `def` is `InducedDistanceAgreement`, with additional
`[T2Space M] [CompactSpace M] [ConnectedSpace M]`, as required by `toMetricSpace`.
It asserts, for every `x y : M`, equality of distances from
`(transport inst' h g).toMetricSpace` and `g.toMetricSpace`, using explicit
`@dist` arguments for each metric.

This needs a curve-level proof: transport derivatives through `J`, equate
Riemannian lengths, then compare the infima defining induced distance.
The current tensor smoothness proof does not supply those curve and length
identities. No distance equality is claimed.

Exact first action for independent review after replaying the commits against
the recorded base:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.RiemannianMetricInstanceTransportGeometric
```

The next mathematical action is to prove the derivative transport identity
for smooth curves from the same coordinate cocycle, then use it to attack
`InducedDistanceAgreement`.
