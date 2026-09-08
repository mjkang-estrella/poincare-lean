# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/moving-position-jacobi-comparison`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartMovingPositionJacobi.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/moving-position-jacobi-comparison_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem).

# Task: the moving-initial-position Jacobi pairing comparison (curvature 1)

Read first: `harness/reports/uniform-nonzero-metric-pullback_blocked.md` (sections "One exact resisting
definition" and "Why the geometric step remains open", which name the lower-level route), then
`Poincare/Global/FixedChartUniformJacobiComparison.lean` (`MovingInitialPositionJacobiComparison`,
`exists_patch_fundamentalSolution`, `coordinateEndpoint_fderiv_of_fundamentalSolution`,
`normalizedJacobiField_initialData`, `target_of_movingInitialPositionJacobiComparison`, and the two
conditional consequences), then the lower-level lemmas the report identifies as applicable with arbitrary
initial position: `GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_orthogonal_chartMetric`,
`coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_zone`,
`JacobiNormSystem.chart_linearized_state_feeds_speed_norm_system_at` (find their files with grep, read their
exact hypotheses: speed preservation along the perturbed flow, chart-metric differentiability along the family,
target/cutoff-one membership, orthogonality), and the per-anchor high-level proof
`RigidityComplete.cartanMap_isLocalIsometry_of_selector_aop_bound` for the overall shape of the argument
(decomposition of `a` into radial and transverse parts, constancy of the radial pairing, the `sin`/`cos`
solution of the transverse scalar Jacobi ODE for curvature 1, and the final pairing identity).

Target (frozen): prove

```lean
theorem movingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) :
    FixedChartUniformJacobiComparison.MovingInitialPositionJacobiComparison g
```

with the definition used verbatim from the landed module and in its instance context, and then restate and
prove in your file the three consequences the landed module already reduces to it:
`uniformNonzeroMetricPullback` (via `target_of_movingInitialPositionJacobiComparison`),
`uniformDifferentialPullback_of_constantCurvature`, and `exists_radius` (the frozen task-8 target).

Route, in order (commit each): (1) along the source patch geodesic `t ↦ C.α qs t` with moving initial position,
prove speed preservation and the cutoff-one/target membership needed by the lower-level lemmas (the patch
retains position control in `U ⊆ cutoffOneLocus x₀`); (2) split each initial vector `a` into its radial
component along the initial velocity and its transverse part with respect to the chart metric at the moving
initial position, and prove the radial Jacobi field is `t ↦ t • (radial part)` transported, while the transverse
Jacobi field satisfies the curvature-1 scalar norm system from
`chart_linearized_state_feeds_speed_norm_system_at` (state the exact norm-system statement you prove); (3) the
same on the sphere patch; (4) the pairing identity at time `T`: both sides equal
`⟨a_rad, a'_rad⟩ + (sin(|v|)/|v|)² ⟨a_⊥, a'_⊥⟩`-type expressions in terms of the anchor metric of `a, a'` and `v`
(derive the exact form from the scalar system rather than assuming it), and the alignment `l` preserves every
anchor pairing (`FixedChartLocalSuccessorExistence.linear_metric`), so the two sides agree; (5) assemble.
If step (2) or (4) resists, deliver the earlier steps and the exact resisting `def` with `target_of_<resisting>`;
keep the statement pointwise (no radius existential).
