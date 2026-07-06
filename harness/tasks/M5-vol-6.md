Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-6: GOAL 10 — the normalized Ricci flow statement + volume positivity

Context: `harness/reports/M5-vol-5_done.md` (READ FIRST) sketches the normalized-flow RHS: `normalizedRicciFlowRHSAt (g) (x) (u w) := -2 * g.ricciAt x u w + (2 / n) * meanScalar g * g.inner x u w` (`totalScalar`/`meanScalar` in `Poincare/Global/ScalarIntegral.lean`; `volumeMeasure` finite). It also isolates: volume POSITIVITY on nonempty closed `M` (`volumeMeasure g Set.univ ≠ 0`) as the next lemma (route: Hausdorff measure of a set containing a bi-Lipschitz image of a Euclidean ball is positive — the inverse comparison direction of `Poincare/Global/VolumeFinitenessComparison.lean`'s machinery; Mathlib has Hausdorff-measure lower bounds under (anti)Lipschitz maps — assess honestly).

Deliverables, in a NEW file `Poincare/Global/NormalizedFlow.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. `normalizedRicciFlowRHSAt` definition per the sketch + symmetry lemma.
2. `IsClosedNormalizedRicciFlowSolutionAt (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀) (x)` — mirroring `IsClosedRicciFlowSolutionAt`'s test-field style (`Global/RicciFlow.lean:40,72`) with the normalized RHS; plus the honest relation lemma to the unnormalized equation (they differ by the mean-scalar multiple of `g` — state the exact pointwise difference identity, provable from the two definitions).
3. VOLUME POSITIVITY: `volumeMeasure g Set.univ ≠ 0` for nonempty closed `M` — the isolated lemma; if the anti-Lipschitz lower-bound route genuinely blocks in the pinned Mathlib, strict-partial with the ONE missing statement isolated.
4. EINSTEIN STATIC CHECK: a constant Einstein family satisfies the normalized equation clause at Einstein metrics IF the algebra closes cheaply (for Einstein `lam`: `-2·lam·g + (2/n)·(n·lam)·g = 0`, so the CONSTANT family solves the normalized flow — the sanity witness the unnormalized flow lacked!); this is the payoff showing the normalized equation is the right fixed-point formulation.
5. Report `harness/reports/M5-vol-6_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.NormalizedFlow` and report the actual result. Commit your work.
