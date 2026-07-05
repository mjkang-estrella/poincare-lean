# M5-sphere-4 done: space-form interface and conditional sphere theorem

## Completed

- Added `Poincare/Global/SphereTheorem.lean` and imported it from `Poincare.lean`.
- Added the narrow space-form recognition interface
  `PositiveConstantCurvatureSpaceForm3`.
  It is theorem-shaped: for a closed connected simply connected smooth
  3-manifold, any `ClosedSmoothRiemannianMetric` with
  `HasConstantSectionalCurvature3 g k` and `0 < k` yields the exact
  `PoincareConjecture` target
  `Nonempty (M ~= Metric.sphere (0 : EuclideanSpace R (Fin 4)) 1)`.
- Added the round-sphere target shape check
  `positiveConstantCurvatureSpaceForm3_roundSphere_target_nonempty`.
- Proved `sphere_of_pinched_limit`.
  It uses the existing theorem
  `hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected`
  to obtain constant curvature `k = R0 / 6`, proves `0 < k` from positive
  scalar curvature at one point, and applies `PositiveConstantCurvatureSpaceForm3`.
- Added the upstream convergence-output interface
  `HamiltonConvergencePinchedLimit3`, packaging the concrete limit metric data
  needed downstream: scalar differentiability, vanishing traceless Ricci, and
  positive scalar curvature somewhere.
- Added the statement-chain theorem
  `poincareConjecture_conclusion_of_hamiltonConvergencePinchedLimit3`.
  This is the per-manifold `PoincareConjecture` conclusion under the two
  named interfaces.
- Added the universal assembly theorem
  `poincareConjecture_of_hamiltonConvergencePinchedLimit3`, which derives the
  repository's `PoincareConjecture` statement if both interfaces are available
  for every manifold in the statement context.

## Honest interface inventory

1. `HamiltonConvergencePinchedLimit3`

   This is the upstream analytic/Ricci-flow boundary.  It does not construct a
   flow, prove compactness, or prove Hamilton convergence.  It states the
   concrete limit-metric payload needed by the endgame.

2. `PositiveConstantCurvatureSpaceForm3`

   This is the hard differential-geometric recognition boundary.  It is the
   Killing-Hopf positive space-form classification specialized to the
   repository's closed simply connected 3-manifold context.  It is consumed as
   an explicit hypothesis, never installed globally.

Everything else in this task is proved composition using existing project
theorems plus these explicit hypotheses.

## Commits

- `bc373c56` - `Add positive curvature space form interface`
- `e1697d00` - `Prove conditional pinched limit sphere theorem`
- `35664e5a` - `Compose pinched limit path to Poincare statement`

## Verification

Commands run:

```text
lake build Poincare.Global.ScalarVariation
lake build Poincare.Global.SphereTheorem
git diff --check
lake build Poincare
```

Results:

- `lake build Poincare.Global.ScalarVariation` completed successfully.
- `lake build Poincare.Global.SphereTheorem` completed successfully after each
  Lean change.
- `git diff --check` completed cleanly before the Lean commits.
- `lake build Poincare` completed successfully:
  `Build completed successfully (3150 jobs).`

The full build emitted existing linter/deprecation warnings and the known
nonfatal `LibrarySuggestions` panic while replaying `Poincare.Surgery`; Lake
continued and returned exit status 0.
