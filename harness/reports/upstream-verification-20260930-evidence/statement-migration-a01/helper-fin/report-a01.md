# Statement 4.33 endpoint migration helper, 2026-09-30

Base source commit: a3b03ff7263b9d610de0a86d00a3a0f4b7f30794. Source line references below are to that commit, not the concurrently edited migration file.

No repository files were edited. Every written file is in this ignored helper evidence directory. No full build was run.

## Verified shared cause and smallest repair

Pinned toolchain file `/Users/mjkang/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Elab/Tactic/Simpa.lean`, lines 94-95, applies `withReducible` to ordinary `simpa ... using`'s final `isDefEq` comparison. Lines 136-149 expose `simpa ... using! term`, which performs the same simplification but closes at default/semireducible transparency. `simpa! ... using term` is different: the early bang only enables simp auto-unfolding and does not remove the final reducible comparison.

For the reported definitionally equal endpoint/path/set mismatches, use the existing `simpa` proof unchanged except for `using` becoming `using!`. Probes 027-030 all exit 0 in the specified pinned compiler environment.

Confirmed families:

- Fin.last hclose endpoints, original 6876, 7044 and the 20 later occurrences recorded in `later-fin-hclose-source-index.txt`.
- Fin.castSucc membership represented by a Fin constructor, original 7199, 7969, 8066.
- Set preimage versus equivalent set-builder in IsOpen, original 8291, 8292.
- Exact original subtype path-map theorem at 6193.
- Casted versus uncasted concat paths inside Homotopy/Homotopic, original 7453 and 7826, plus repeated analogs.
- rBack mapped-overlap membership, original 6416, 6419.
- Double endpoint cast cancellation, original 8372.

The same probes also show ordinary `exact` suffices where no actual simplification is needed. The exact original theorem at 6193 compiles with `exact hU.map ⟨Subtype.val, continuous_subtype_val⟩`, probe 023. Analogous hclose, castSucc membership, IsOpen and late h0/hSub examples pass with ordinary exact, probes 025-026.

A global `set_option backward.isDefEq.respectTransparency false` does not repair ordinary simpa's final reducible comparison, as verified in probes 002 and 009. This option and `using!` address distinct parts of elaboration.

## Range rewrite failures need explicit arguments

Original 7468 should use:

```lean
rw [Path.trans_range (((p.trans P).trans O).trans R) T]
exact Or.inr hz
```

This passes in probe 016 with the same prefixPts, oppPts, returnPts and afterPts definitions as the failing theorem. Bare `rw [Path.trans_range]` fails in probe 012 because matcher transparency cannot reconcile the locally defined endpoint types. Merely unfolding the point/path lets does not repair that matching, probes 013-014.

For original 7029's analogous membership conversion, instantiate `Path.trans_range p (Path.concat uPts uSegs)` explicitly when rewriting. Unlike the final simpa comparison errors, an unmatched range lemma will not be repaired merely by `using!`.

## Explicit fallback proofs

If avoiding `using!`, the following are verified:

- hclose simp: add `Fin.last` to the existing point-family simp list.
- castSucc simp: include all of `Fin.castSucc, Fin.castAdd, Fin.castLE`, plus the existing A definition where present. Each alone is insufficient because castSucc unfolds to castAdd and then castLE. Probe 008.
- rBack: `change (overlapPath (unitInterval.symm t) : Y) ∈ U` and the corresponding V goal, then exact the subtype's `.2.1` or `.2.2`. Probe 021.
- Double cast: `change Path.Homotopic γ (Path.refl basepoint) at hCastBack; exact hCastBack`. Generic p/q analog passes probe 021.
- Homotopy source transport: prove the casted concat equals its uncasted path with `Path.ext; rfl`, and apply `HcollapseRaw.cast hSourceEq rfl`. Probe 020. Plain `exact HcollapseRaw` also passes probe 022.
- Map fallback: prove `pU.map continuous_subtype_val = p` and q analog with `Path.ext; rfl`, then simp only these equalities. Probe 005.

## Evidence limits

These are focused kernel-checked tactic probes and actual source inspections. The parent must compile the entire edited Statement file and perform its frozen signature/definition review before acceptance. This helper makes no completion claim.

All probe sources and failed/successful logs are retained. The result JSON files record actual Lean subprocess exit codes. Placeholder scan found no sorry/admit/axiom/native_decide in helper Lean files. `git diff --check` passed in the migration worktree at the end of helper execution.
