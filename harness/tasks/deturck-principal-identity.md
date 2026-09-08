# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/deturck-principal-identity`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/deturck-principal-identity_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name you use by grep in the repo or `.lake/packages/mathlib`. If blocked, display the exact resisting expression and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section, `harness/reports/deturck-principal-second-jet_blocked.md` (the whole report: compiled lemmas, the exact residual expression, the exposed second-jet form of the Christoffel derivative, the landed form of the DeTurck field `W`), and the landed `Poincare/Global/DeTurckPrincipalSecondJet.lean` (namespace `Poincare.DeTurckPrincipalSecondJet`: `Bilin`, `Jet1`, `basis3`, `inverseEntries`, `spatialPrincipal`, `fieldDerivative_eq_contractionDerivative`, `evolution_eq_coordinate_expression`, `ricciSecondJet`, `lieSecondJet`, `secondJet_cancellation`, `chartMetric_secondJet_cancellation`, `christoffelDerivative_eq_chartMetricSecondJet`). Reuse them; do not re-prove them.

# Task deturck-principal-identity

Module: `Poincare/Global/DeTurckPrincipalIdentity.lean`. Namespace: `Poincare.DeTurckPrincipalIdentity`. Imports: `Poincare.Global.DeTurckPrincipalSecondJet` (add what you need).

Objective: finish the principal-part identity. With `bg`, `anchor`, `z`, `hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target`, `hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1` fixed, prove

```lean
theorem principalIdentity (bg : ClosedSmoothRiemannianMetric 3 M)
    (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) :
    ∃ lower : Bilin → Jet1 → Bilin,
      ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
        deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z v w =
          spatialPrincipal (CovariantDerivative.chartMetric g.inner anchor) z v w +
          lower (CovariantDerivative.chartMetric g.inner anchor z)
            (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) v w
```

in the manifold context of the landed module (`E := ClosedSmoothModel 3`). `lower` is chosen once, before `g`; it may depend on `bg`, `anchor`, `z` and on the jets of `bg` at `z`.

Route, in order:
1. Derivative of the DeTurck field. From the landed form `W y = ∑ i, Γ_g y (raised_i y) (b i) - Γ_bg y (raised_i y) (b i)` with `raised_i y = (blendedMetric y).inverse (coord i)`, prove `fderiv ℝ W z a` as an explicit expression in `G z`, `fderiv ℝ G z`, `fderiv ℝ (fderiv ℝ G) z`, and the jets of `bg` at `z` (use `hcut` so the blended metric equals `G` eventually near `z`, as in `christoffelDerivative_eq_chartMetricSecondJet`; the derivative of the inverse is `-G⁻¹ (∂G) G⁻¹`; the derivative of `Γ_g` is the landed `C a u v` form; `Γ_bg` and its derivative are constants of `lower`).
2. Second-order bookkeeping. Show that the second-derivative terms of `fderiv ℝ G z (W z) v w + G z (fderiv ℝ W z v) w + G z v (fderiv ℝ W z w)` equal `lieSecondJet (inverseEntries (G z)) (fderiv ℝ (fderiv ℝ G) z) v w` (or whatever exact normalization `lieSecondJet` uses; read its definition) plus terms depending only on `(G z, fderiv ℝ G z)` and `bg`'s jets; and similarly that the curvature sum's second-derivative terms equal `ricciSecondJet ...` plus first-jet terms. State these as two lemmas whose right-hand sides are explicit functions of `(G z, fderiv ℝ G z)`.
3. Assemble with `evolution_eq_coordinate_expression` and `chartMetric_secondJet_cancellation`, and define `lower` as the explicit sum of the first-jet remainders (a function of `(G z, fderiv ℝ G z)` and the fixed `bg` data). Conclude `principalIdentity`.

Exact stop condition: `principalIdentity` compiles with exactly the displayed hypotheses; or a blocked report displays the exact uncancelled term after steps 1 and 2 with the compiled lemmas committed. Do not choose `lower` depending on `g`.
