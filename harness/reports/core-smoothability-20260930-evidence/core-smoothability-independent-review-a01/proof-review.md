# Independent exact core S proof review

Reviewer: `exact_target_migration`. Candidate author: root orchestrator.
Base: `c8423a94bc63198b6f5cc59f2b9b1407b1f70ade`.
Worktree: `/Users/mjkang/.codex/worktrees/core-smoothability-upstream/poincare`.
Candidate: `Poincare/Global/VerifiedSmoothability.lean`, untracked and unchanged throughout review.
Candidate SHA256: `3e392581041df9dc56c3c9e5247a4bdbfc49b8a42a1b8eb8cb3cc021556bba99`.

## Mathematical result

The candidate is an unconditional proof of the actual existing core S obligation:

```lean
Poincare.existsSmoothabilitySmoothManifoldStatement :
  Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u}
```

Its only proof steps are introducing the original manifold and instance arguments, then applying `DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three (M := M)`. This producer needs the supplied topology, Hausdorffness, compactness and topological Euclidean3 atlas. It constructs a replacement Euclidean3 charted-space structure C and IsManifold smooth infinity for that C on the SAME carrier and SAME supplied topology. The extra original SimplyConnectedSpace hypothesis is retained and unused because the upstream producer is stronger. No smooth atlas/proof, sphere/homeomorphism, sphere recognition, Hamilton convergence, flow, metric or additional assumption is supplied.

The fresh frozen probe checks the literal universal type and rigid universe arity1, verifies the complete transitive dependency graph has no unsafe/partial declaration, and allows only propext, Classical.choice and Quot.sound. Its final `example : Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u} := Poincare.existsSmoothabilitySmoothManifoldStatement` also passes. Thus this proves the existing constant's proposition, not a target clone or a conditional wrapper requiring the desired witness. Regularity is explicit ENat.top coerced into WithTop ENat, smooth C-infinity rather than analytic omega.

This is credited reuse of the independently checked DifferentialGeometry Moise proof. It is meaningful closure of S in the reviewed module. Acceptance, committing and root integration remain the orchestrator's decisions; the module is not yet wired into Poincare.lean. It makes no claim that the independent Hamilton H construction or the final retained-root completion gate has succeeded.

## Definition, canonical target and root preservation

The existence-shaped definition and its rfl companion were moved byte-for-byte from the pre-move TopologicalCompletionBridge. The moved block SHA256 is `e0bc3ff25246e26ba5d63cc78eb7a46735351816877dbc323d4909848f34c864`. The old bridge is otherwise byte-identical after deleting that exact block and adding the required import. Public names and quantifiers remain the same. The canonical Statement.lean is unchanged from the pre-move commit; ThreeSphere and PoincareConjectureStatement source blocks are also byte-identical to the historical frozen a3b03ff checkpoint.

All1039 original a3b03ff root imports remain in their original order. The move adds the narrow SmoothabilityExistenceStatement root import without removing historical modules. VerifiedSmoothability's root import is still pending integration and was not added by this reviewer. Every sealed definition-context SHA256 was checked before and after fresh gates.

## Dependency and artifact provenance

Actual local Git HEADs and Lake pins are DifferentialGeometry `7a48598d35109aa99d1cc678e2724c213cdf4ff3`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and Lean4.33.1. Both dependency source trees report clean Git status.

The local producer .lean, .olean and .trace match SHA256 of BOTH the original independently checked release checkout and its archived evidence. Producer source SHA256 is `cdd66d048afed7ab54ac76641c99a1751743a472d170f374f5cdd9ea388b3482`; producer artifact SHA256 is `8db36fc9c1ae262254907ee230eac39c9896b3940b4732286fe7152f48fdc787`; trace SHA256 is `320e827d6439f380a4e324110c72fdbb57075a148392fc70d5676a8937fd0985`. The producer's earlier independent receipt has exit0, correct release identity and matching preserved stdout/stderr hashes. Its transcript confirms the exact topology-preserving replacement-atlas producer and standard axiom/safety check.

Root's already-completed local artifact command exited0 and produced candidate olean SHA256 `45af72be1835c54379fb1c1cd9349822c14f17c75f661061cb41dd22c3bd1fe0`, which remained stable across this independent review. No build was duplicated or artifact overwritten by the reviewer.

## Fresh independent gates

- `env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/VerifiedSmoothability.lean`: exit0,3.539192s.
- `env LEAN_NUM_THREADS=1 lake env lean harness/v2/state/upstream-verification-20260930/core-smoothability-proof-a01/FrozenSmoothabilityProbe.lean`: exit0,12.491396s; FROZEN_CONTRACT_OK and AXIOM_CONTRACT_OK for the actual theorem, plus the old-statement application example.
- Exact forbidden-token scan: exit1, no matches.
- `git diff --check`: exit0. Since the file is untracked, a supplemental `git diff --no-index --check -- /dev/null ...` checked it too: exit1 for differences, no whitespace diagnostics. Its full new-file diff is preserved.

All command receipts bind the same candidate source hash. Source, sealed Task, context hashes, definition-move block, root import sequences, artifact/source provenance and full fresh transcripts/exits/timings are preserved append-only here.

No source edit, helper agent, duplicate build, service operation, commit, merge or acceptance was performed. Root's first action is to review these independent results and choose acceptance/integration with the pending root import, then run its retained-root and exact completion gates.
