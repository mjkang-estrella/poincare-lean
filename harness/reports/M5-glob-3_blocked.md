# M5-glob-3 blocked report

## Delivered files

- `Poincare/Global/CartanChain.lean`
- `harness/reports/M5-glob-3_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`CartanChain.lean` adds placeholder-free progress for the path-chaining stage:

- `exists_monotone_unitInterval_subdivision_dist_lt`
- `exists_uniform_normal_subdivision`
- `ChainState`
- `ChainState.germ`
- `ChainState.map`
- `ChainState.next`
- `ChainState.RigidStepCompatible`
- `ChainState.next_restr_eqOnSource_of_rigidStepCompatible`
- `ChainState.next_map_eq_of_rigidStepCompatible`
- `initialState`
- `chainState`
- `chainGerm`
- `ChainRigidCompatible`
- `chain_step_restr_eqOnSource`
- `pathChainState`
- `endpoint_target_eq_insert`
- `endpoint_germ_eq_insert_of_alignment`

The subdivision theorem represents a finite subdivision as a monotone sequence
`t : ℕ → I` that is eventually equal to `1`; this is the same finite-data shape
provided by Mathlib's compact unit-interval cover lemma.  Consecutive image
points are proved to have distance `< r`.  The uniform-normal theorem applies
`UniformNormalRadius.lean` to get a common normal-coordinate image for each
consecutive pair.

The chain layer iterates re-anchored Cartan germs over an arbitrary node
sequence.  Its rigid-10 staging hypothesis is the exact `EqOn` common-source
shape consumed by `CartanContinuation.twoStep_*`, not a vacuous certificate.
The single-insertion theorem proves that inserting one intermediate point
preserves the endpoint target value under this `EqOn` compatibility, and
preserves the endpoint germ when the remaining endpoint tangent-alignment
determinacy input is supplied as `HEq`.

## Blocking boundary

The full requested subdivision-independence theorem is not yet provable
non-vacuously from the current interfaces.

1. `UniformNormalRadius.lean` gives close consecutive points in a common
   `normalCoordinateImage`, but there is no theorem connecting that set to the
   source of the active `CartanMap.openPartialHomeomorph`.  The two-step
   Cartan lemmas require common-source membership for the Cartan germs.

2. `CartanContinuation.lean` has germ determinacy only when the endpoint
   tangent-alignment data are identified by `HEq`.  The chain construction can
   prove the endpoint target values agree after inserting one point, but the
   re-anchored endpoint alignments are chosen from `tangentAlignment_nonempty`;
   there is currently no rigid theorem proving those choices determine the same
   endpoint germ.

The next non-vacuous step is to prove the rigid-10 output in the stronger form
needed here: close/source-overlap compatibility for the Cartan sources, plus
transport/determinacy of the endpoint tangent alignment after re-anchoring.
After those are available, `endpoint_germ_eq_insert_of_alignment` is the local
insertion step for the common-refinement induction.  Homotopy invariance remains
the later stage after subdivision independence.

## Verification

Command run:

```bash
lake build Poincare.Global.CartanChain
```

Actual result:

```text
✔ [2989/2989] Built Poincare.Global.CartanChain (3.6s)
Build completed successfully (2989 jobs).
```
