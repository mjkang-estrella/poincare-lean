# M5-model-9 done

## Delivered

- Added `Poincare/Global/ConstantCurvatureEinstein.lean`.
- Proved
  `isEinsteinAt_of_hasConstantSectionalCurvature3
    (g : ClosedSmoothRiemannianMetric 3 M) {κ : ℝ}
    (h : HasConstantSectionalCurvature3 g κ) (x : M) :
    g.IsEinsteinAt (2 * κ) x`.
- Added the round-sphere corollary
  `roundSphereMetric3_isEinsteinAt_two :
    ∀ x : RoundSphere3, roundSphereMetric3.IsEinsteinAt 2 x`.
- Added
  `positiveEinsteinMetric3_roundSphere :
    PositiveEinsteinMetric3 RoundSphere3`.

## Contraction route

The proof unfolds `g.IsEinsteinAt` and rewrites `g.ricciAt x u w` using the
existing raised-basis trace lemma
`ricciAt_eq_curvature_inner_contraction`.  Applying
`HasConstantSectionalCurvature3` termwise turns the Ricci trace into the trace
of the metric Kulkarni-Nomizu tensor.  The existing lemma
`metricKulkarniNomizuAt_finBasis_trace_eq` supplies the repository's actual
slot/sign convention:

`tr_g KN(g,g)(., u, w, .) = -4 * g.inner x u w`.

Thus the curvature convention gives `-(κ / 2) * (-4) = 2 * κ`.

For the positive witness, `RoundSphere3` is definitionally the same type as
the statement-layer `ThreeSphere`.  `Poincare.Statement` already provides
`threeSphere_instSimplyConnectedSpace`; this module supplies a local
`ConnectedSpace RoundSphere3` instance from `threeSphere_connectedSpace`.

## Verification

Command:

```text
lake build Poincare.Global.ConstantCurvatureEinstein
```

Actual result:

```text
Build completed successfully (3128 jobs).
```

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the new Lean file.
