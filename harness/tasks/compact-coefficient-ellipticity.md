# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/compact-coefficient-ellipticity`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new hypotheses beyond the displayed ones; commit each verified lemma on the branch; report actual command output to `harness/reports/compact-coefficient-ellipticity_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every Mathlib name you use by grep in `.lake/packages/mathlib`. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken the target silently.

Context: read `HANDOFF.md` top section and `harness/reports/ricci-flow-existence-interface-survey_done.md` section 3 (Task 1) and Appendix D first. This is the class-A ellipticity-constant lemma for the finite-atlas parabolic route; it provides a uniform coercivity constant and nothing more.

# Task compact-coefficient-ellipticity

Module: `Poincare/Global/CompactCoefficientEllipticity.lean`. Namespace: `Poincare.CompactCoefficientEllipticity`. Imports: `Poincare.Global.RiemannianContext`, `Mathlib.Topology.Order.Compact`, `Mathlib.Analysis.InnerProductSpace.PiL2` (add what you need).

Objective: from a continuous family of pointwise positive bilinear forms on a compact parameter space, produce one positive quadratic lower bound with the constant quantified before the point and vector.

Displayed target (prove exactly this; `ClosedSmoothModel 3` is `EuclideanSpace ℝ (Fin 3)` in the repository, check `Poincare/Global/RiemannianContext.lean`):

```lean
namespace Poincare.CompactCoefficientEllipticity

abbrev E := ClosedSmoothModel 3
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

theorem exists_uniform_coercivity {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : K → Bilin) (hA : Continuous A) (hpos : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x v, c * ‖v‖ ^ 2 ≤ A x v v

end Poincare.CompactCoefficientEllipticity
```

Proof route: the unit sphere of `E` is compact (finite dimension); `K × sphere` is compact; `(x, v) ↦ A x v v` is continuous (continuity of `A` composed with the continuous bilinear evaluation); if `K` is empty take `c = 1`; otherwise the minimum over the compact nonempty product is attained and strictly positive by `hpos`; for a general nonzero `v` scale to the sphere and use bilinearity (`A x (t • v) (t • v) = t^2 * A x v v`); the zero vector gives `0 ≤ 0`. Useful Mathlib facts to look for: `IsCompact.exists_isMinOn` / `IsCompact.exists_forall_le`, `isCompact_sphere`, `Metric.sphere`, `ContinuousLinearMap.continuous`, `norm_smul`, `ContinuousLinearMap.map_smul`.

Also add the parametrized variant with the constant depending only on the family: `theorem exists_uniform_coercivity_on (s : Set K) (hs : IsCompact s) ...` is optional; do not spend time on it if the main theorem is done.

Exact stop condition: the displayed theorem compiles with exactly the displayed hypotheses and conclusion and passes the gate.
