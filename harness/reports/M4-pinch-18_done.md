# M4-pinch-18 done: honest quotient evolution with explicit reaction remainder

## Pre-proof coefficient pins

The corrected quotient target keeps the reaction contribution explicit.  Write

```text
R = scalar, N = |Ric|^2, Q = N / R^2,
N_react = |Ric|^2 reaction trace + Ricci-flow metric-motion trace,
R_react = 2N,
(R^2)_react = 2R R_react = 4RN.
```

The named reaction remainder is normalized by

```text
(2 / R^4) P_reaction
  = N_react / R^2 - N (R^2)_react / R^4
  = N_react / R^2 - 2N R_react / R^3,
P_reaction = (R^2 N_react - N (R^2)_react) / 2.
```

Space form `(lambda, lambda, lambda)`:

```text
R = 3 lambda, N = 3 lambda^2,
N_react = 12 lambda^3, (R^2)_react = 36 lambda^3,
P_reaction = 0,
quotient reaction = 0.
```

Non-Einstein `(1,1,2)`:

```text
R = 4, N = 6,
N_react = -8 + 40 = 32, (R^2)_react = 96,
P_reaction = (16 * 32 - 6 * 96) / 2 = -32,
quotient reaction = 2 * (-32) / 4^4 = -1/4.
```

Non-Einstein `(1,2,3)`:

```text
R = 6, N = 14,
N_react = -24 + 144 = 120, (R^2)_react = 336,
P_reaction = (36 * 120 - 14 * 336) / 2 = -192,
quotient reaction = 2 * (-192) / 6^4 = -8/27.
```

These pins are formalized in `Poincare.Global.RicciNorm` as
`diagonalPinchingReactionRemainder3_spaceForm`,
`diagonalPinchingReactionQuotient3_one_one_two`, and
`diagonalPinchingReactionQuotient3_one_two_three`.

## Correction

The old `SatisfiesHamiltonPinchingEvolutionInequality3At` target is retained
only as correction history.  Its traceless-Ricci damping term is stronger than
the reaction supplied by the proven parabolic forms on `(1,1,2)`.

The corrected target is `SatisfiesPinchingQuotientEvolutionAt`: it separates
the completed gradient square from the reaction remainder.  The sign of the
reaction remainder under 3D Ricci nonnegativity is deliberately left for step 5.

## Step-5 outlook

The next proof obligation is the 3D reaction-sign lemma:

```text
Ric >= 0  ==>  pinchingReactionRemainderAt <= 0
```

with the corrected normalization above.  That should be proved as a separate
algebraic lemma, not bundled into the quotient-calculus assembly.
