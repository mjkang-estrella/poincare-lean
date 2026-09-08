# Supplied finite patch cover worker result

Date: 2026-09-08. Branch: `worker/supplied-finite-patch-cover`.
Recorded base: `145387ca8971544af2d21fcd862eaaf5304168ef`.
Verified proof head: `275ebda305fd0cdc7b7d6033d555e03c86273eab`.

Both frozen existence targets are proved in the single new Lean file
`Poincare/Global/CartanSuppliedFinitePatchCover.lean`, with the definitions
and signatures from task 11 of `parametrization-plan-3.md`.
This is a worker result awaiting independent orchestrator review.

## Mathematical result

`exists_patchCover` chooses a patch at every point with its host's
`cutoffOneLocus` as the zone. An open anchor ball of radius `r` contains
a compact closed buffer of radius `r / 2`. The compact closed core has
radius `r / 4`, and lies in the buffer interior. Open balls of radius
`r / 4` cover the manifold. Compactness gives a finite subcover, reindexed
by `Fin count`; the metric Lebesgue lemma gives the stored positive
`lebesgue` and the full `ball_cover` clause. Evaluating those balls at
their centers gives `covers`.

`exists_positive_lower_bound` takes iterated minima over a finite index
set. It also handles an empty family by starting with radius 1.

`exists_quantitativeCover` applies `exists_patchCover` to the source metric
and to `roundSphereMetric3` with the existing sphere chart instance.
For every source/target buffer pair it applies the landed
`FixedChartLocalSuccessorEquality.exists_radii`, then takes independent
positive lower bounds for the step and evaluation radii. Restricting the
step bound preserves H1; restricting both bounds preserves H2's full-ball
source inclusion and equality for every datum.

For each core pair, `exists_uniform_domain_radius_into_open` is applied
with the buffer interiors as its two requested open neighborhoods.
A finite lower bound gives `retention`, including retention of both the
source successor anchor and the supplied-map target. All three radii
precede the chain state, alignment, successor point and datum quantifiers.
No path or chain is used to select any radius.

The cover is a finite refinement: several patches may share a host chart.
No one-patch-per-chart coverage assertion is made. This construction needs
no finite-atlas premise. Global development, patch switching and recognition
are later tasks and are not proved here.

## Commits

Each theorem was compiled before its commit.

- `486dee502ff052a99f7a3ed35d965868ce8e343a`: `exists_patchCover`, together
  with the prescribed structures and definitions.
- `e5b600f219941e60d137e4011c2f432da81c127f`: `exists_positive_lower_bound`.
- `275ebda305fd0cdc7b7d6033d555e03c86273eab`: `exists_quantitativeCover`.

No existing Lean file, root import, audit file or source definition changed.
The task's explicit file scope takes precedence over the general
`HANDOFF.md` update instruction; this report is the handoff.

## Verification and actual output

Final direct elaboration:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedFinitePatchCover.lean
```

Exit 0, no output. Recorded in
`/tmp/supplied-finite-patch-cover-evidence/lean-final-02.log`.

Final focused build:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedFinitePatchCover
```

Exit 0. Final lines:

```text
✔ [3618/3618] Built Poincare.Global.CartanSuppliedFinitePatchCover (3.4s)
Build completed successfully (3618 jobs).
```

The complete output, including replayed warnings from dependencies, is
`/tmp/supplied-finite-patch-cover-evidence/build-final.log`.
The new module emitted no warnings.

Prohibited-token gate:

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedFinitePatchCover.lean
```

Exit 1, no matches and no output.

Whitespace gates:

```sh
git diff --check
git diff 145387ca8971544af2d21fcd862eaaf5304168ef --check
```

Both exit 0, no output.

Exact-signature and closure probe:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-finite-patch-cover-evidence/targets.lean
```

The probe imports the new module, enables `autoImplicit false`, uses the
specification's ambient variables, and checks these literal signatures:

```lean
example : ∀ g : ClosedSmoothRiemannianMetric 3 M, Nonempty (PatchCover g) :=
  exists_patchCover
example : HasConstantSectionalCurvature3 g 1 → Nonempty (QuantitativeCover g) :=
  exists_quantitativeCover
#print axioms exists_patchCover
#print axioms exists_positive_lower_bound
#print axioms exists_quantitativeCover
#check @exists_patchCover
#check @exists_quantitativeCover
```

Exit 0. The closure output is:

```text
'Poincare.CartanSuppliedFinitePatchCover.exists_patchCover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedFinitePatchCover.exists_positive_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedFinitePatchCover.exists_quantitativeCover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The expanded target types retain precisely the ambient manifold, T2,
compactness and connectedness instances and the displayed curvature premise.
The full source and output are in `targets.lean` and `targets-final.log`
under the evidence directory. These are all three new theorem declarations.
Root integration audits were not run by this worker.

## Compiler retries and evidence

The first source check reported:

```text
Poincare/Global/CartanSuppliedFinitePatchCover.lean:94:62: error: failed to prove positivity/nonnegativity/nonzeroness
```

The local ball-center membership proof needed the explicit expression
`div_pos (hr x) (by norm_num)` instead of automatic positivity. The failed
compiler output is preserved in `lean-01.log`. Its shell invocation ended
with `cat`, so that invocation's exit 0 was the output-printing command's
status, not a successful Lean check. The corrected direct check exited 0
with no output in `lean-02.log`.

The helper and quantitative proofs passed their first module checks with
no output in `lean-03.log` and `lean-04.log`. A later token scan found the
ordinary word `admit` in a documentation comment at line 151. The comment
was changed to `have`; the final scan has no matches. The final source was
recompiled, rebuilt and probed after the comment correction.

All local evidence is under
`/tmp/supplied-finite-patch-cover-evidence/`. The proof diff against the
recorded base is `final-proof.diff` there. The Git commits are the durable
proof artifacts; this report records the failed output and final gate
results even if temporary logs are later removed.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedFinitePatchCover.lean
```

Then inspect the diff against the recorded base and rerun the signature
probe before accepting this task or freezing the prerequisite for task 12.
