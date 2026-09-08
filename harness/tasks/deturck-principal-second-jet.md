# Worker contract (Lean task, exploratory)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/deturck-principal-second-jet`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/deturck-principal-second-jet_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name you use by grep in the repo or `.lake/packages/mathlib`. This task is exploratory (class C in the survey): a blocked report that displays the exact uncancelled second-jet expression, with the strongest compiled partial identities (for example the second-order part alone, or the identity for a constant background), is an acceptable outcome. Never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/ricci-flow-existence-interface-survey_done.md` (section 3 Task 2, section 4, and Appendix D, which contains the exact definitions `E`, `Bilin`, `Jet1`, `basis3`, `inverseEntries`, `spatialPrincipal`, `principalIdentityGoal` and the probe context) first. The landed DeTurck chart evolution is `deTurckChartMetricEvolutionBilin` (find it by grep; read its definition module and `Poincare/Global/DeTurckBUCCoefficientIdentification.lean`, `Poincare/Global/DeTurckGaugedFlowClosure.lean`).

# Task deturck-principal-second-jet

Module: `Poincare/Global/DeTurckPrincipalSecondJet.lean`. Namespace: `Poincare.DeTurckPrincipalSecondJet`. Imports: `Poincare.Global.DeTurckBUCCoefficientIdentification`, `Poincare.Global.DeTurckGaugedFlowClosure`, `Mathlib.Analysis.InnerProductSpace.PiL2` (add what you need).

Objective: prove that at a genuine cutoff-one chart point the actual DeTurck chart rate is the inverse-metric contraction of the metric's second spatial derivative plus a function of only the metric's value and first spatial derivative, with that lower-order function chosen before the input metric.

Target (from Appendix D of the survey; reproduce its auxiliary definitions `Bilin`, `Jet1`, `basis3`, `inverseEntries`, `spatialPrincipal` verbatim in the module, then prove):

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

with the context of Appendix D (`E := ClosedSmoothModel 3`, manifold variables as displayed there). Note the quantifier order: `lower` is chosen once, before `g`; it may depend on `bg`, `anchor`, and `z`.

Suggested route: unfold `deTurckChartMetricEvolutionBilin` at the constant family to the chart expression of `-2 Ric(g) + L_{W} g` with `W` the DeTurck field against `bg`; in the cutoff-one region the chart metric is the genuine coordinate metric; express the Ricci tensor through the landed coordinate curvature formulas (Christoffel symbols from first derivatives, their derivatives from second derivatives); collect all second-derivative terms; show the DeTurck correction cancels the mixed second-derivative terms so that only `-(g^{ab} ∂_a ∂_b g_{vw})` (up to the sign/normalization used by `spatialPrincipal`) remains at second order; define `lower` as the explicit remaining polynomial in `(g, ∂g)` with `bg`'s jets at `z` as constants. If the landed curvature formulas are stated only along flows or with cutoff factors, prove the constant-family specialization first as separate lemmas.

Exact stop condition: the displayed theorem compiles with exactly the displayed hypotheses, or a blocked report displays the exact residual second-jet expression that does not cancel, with compiled partial lemmas committed.
