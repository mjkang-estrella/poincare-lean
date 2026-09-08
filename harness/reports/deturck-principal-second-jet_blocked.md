# deturck-principal-second-jet: blocked with verified partial identities

Date: 2026-09-08. Base: `502203724120a03fa3884df5fa24a242bf56fb0a`.
Branch: `worker/deturck-principal-second-jet`. Proof head: `0313b8e0`.

`principalIdentity` is not proved or declared. The original quantifier order
and hypotheses remain the target. The worker result contains one new Lean
module, `Poincare/Global/DeTurckPrincipalSecondJet.lean`, and this report.
Existing Lean files, `Poincare.lean`, frozen contracts, and `HANDOFF.md` were
not edited. The task's explicit file restriction controls the handoff scope.

## Compiled progress

Every lemma was checked and committed separately. All names below are in
`Poincare.DeTurckPrincipalSecondJet`.

| Commit | Lemma | Result |
| --- | --- | --- |
| `3c421944` | `fieldDerivative_eq_contractionDerivative` | At a genuine cutoff-one point, the ordinary derivative of the actual coordinate field equals the derivative of the landed inverse-metric Christoffel contraction. The pointwise bridge is upgraded to an eventual equality before differentiating. |
| `c0227b0d` | `evolution_eq_coordinate_expression` | Expands the actual constant-family rate into the coordinate Ricci trace, advection, and two derivative slots. It uses no flow equation or extra field regularity premise. |
| `72c70a1f` | `secondJet_cancellation` | Cancels the explicitly defined formal Ricci and Lie second-order expressions for a symmetric inverse matrix and a second jet symmetric in its derivative and metric slots. |
| `f2059097` | `chartMetric_secondJet_cancellation` | Applies that algebra to the genuine chart metric. All symmetry conditions follow from the metric and its landed C2 chart regularity. The result is exactly the positive `spatialPrincipal` from Appendix D. |
| `0313b8e0` | `christoffelDerivative_eq_chartMetricSecondJet` | Expresses the derivative of the actual Christoffel field in the genuine chart metric's jets. Eventual equality removes the cutoff-blended metric from the landed derivative formula. |

The six requested auxiliary declarations were reproduced from Appendix D.
`ricciSecondJet` and `lieSecondJet` are explicit finite algebraic expressions.
They do not define geometric rates and contain no analytic premises.
Their identification with the second-order parts of the actual geometric
rate is still missing. Thus their cancellation, including its specialization
to the actual metric's second derivative, does not prove `principalIdentity`.

## Exact resisting expression

In the original manifold context, fix `bg`, `anchor`, `z`, `hz`, and `hcut`.
The unresolved factorization is the following expression. All symbols other
than the local lets already exist in the checked module or its imports.
`anchorChartDeTurckContractionFlow` is in namespace
`Poincare.DeTurckCoordinateJointRegularity`.

```lean
∃ lower : Bilin → Jet1 → Bilin,
  ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
    let G := CovariantDerivative.chartMetric g.inner anchor
    let Γ := GeodesicTransport.chartChristoffelField g anchor
    let W := anchorChartDeTurckContractionFlow (fun _ => g) bg anchor 0
    let b := Module.finBasis ℝ E;
    -2 * (∑ i, b.coord i
      ((fderiv ℝ Γ z (b i)) v w - (fderiv ℝ Γ z v) (b i) w +
        Γ z (b i) (Γ z v w) - Γ z v (Γ z (b i) w))) +
    fderiv ℝ G z (W z) v w +
    G z (fderiv ℝ W z v) w + G z v (fderiv ℝ W z w) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      inverseEntries (G z) i j *
        fderiv ℝ (fderiv ℝ G) z (basis3 i) (basis3 j) v w) =
    lower (G z) (fderiv ℝ G z) v w
```

`evolution_eq_coordinate_expression` identifies the expression preceding
the subtracted contraction with the actual rate. No choice of `lower`
for this residual was constructed. In particular, a remainder chosen
separately for each `g` would not meet the contract.

The second derivatives in the curvature portion can now be exposed further.
Use the following notation at the fixed point:

```lean
G := CovariantDerivative.chartMetric g.inner anchor
DaG := fun y => fderiv ℝ G y a
K F u v := LinearMap.toContinuousLinearMap
  (CovariantDerivative.christoffelFunctional F z u v)
C a u v :=
  (-((G z).inverse.comp (((fderiv ℝ G z) a).comp (G z).inverse)))
    (K G v u) +
  (G z).inverse (K (fun y => fderiv ℝ G y a) v u)
```

The fifth compiled lemma proves, for every `a u v`,

```lean
fderiv ℝ (GeodesicTransport.chartChristoffelField g anchor) z a u v = C a u v
```

Thus the exact residual above also has curvature sum

```lean
-2 * (∑ i, b.coord i
  (C (b i) v w - C v (b i) w +
    Γ z (b i) (Γ z v w) - Γ z v (Γ z (b i) w)))
```

The uncancelled second-jet expression inside `C a u v`, displayed without
abbreviating its scalar functional, is

```lean
(G z).inverse (LinearMap.toContinuousLinearMap
  (CovariantDerivative.christoffelFunctional
    (fun y => fderiv ℝ G y a) z v u))
```

The covector sent to `(G z).inverse` evaluates on `q` to exactly

```lean
(1 / 2 : ℝ) *
  (fderiv ℝ (fun y => fderiv ℝ G y a) z v u q +
   fderiv ℝ (fun y => fderiv ℝ G y a) z u v q -
   fderiv ℝ (fun y => fderiv ℝ G y a) z q v u)
```

This follows by unfolding `christoffelFunctional`; it is not a new analytic
assumption. It must be combined with the still unexpanded second-order terms
in `G z (fderiv ℝ W z v) w + G z v (fderiv ℝ W z w)`.

The exact field being differentiated is already landed:

```lean
W y = ∑ i,
  let raised := (anchorBlendedMetricFlow (fun _ => g) anchor 0 y).inverse
    (LinearMap.toContinuousLinearMap (b.coord i))
  GeodesicTransport.chartChristoffelField g anchor y raised (b i) -
    GeodesicTransport.chartChristoffelField bg anchor y raised (b i)
```

In particular, differentiating `raised` contributes inverse-metric derivative
terms. Neither those terms nor the background Christoffel derivative can be
dropped. The background jets may be constants of the eventual `lower` because
`bg`, `anchor`, and `z` precede its existential quantifier.

## What cancels, and what remains open

The compiled algebra proves

```lean
-2 * ricciSecondJet A H v w + lieSecondJet A H v w =
  ∑ i : Fin 3, ∑ j : Fin 3, A i j * H (basis3 i) (basis3 j) v w
```

The proof first leaves the following antisymmetric summand and then kills
its finite sum by exchanging `i` and `j` using `A i j = A j i`:

```lean
(1 / 2 : ℝ) * A i j *
  (H v (basis3 i) (basis3 j) w - H v (basis3 j) (basis3 i) w -
   H w (basis3 i) (basis3 j) v + H w (basis3 j) (basis3 i) v)
```

For the actual metric, `chartMetric_secondJet_cancellation` supplies this
identity with `A = inverseEntries (G z)` and
`H a b p q = fderiv ℝ (fderiv ℝ G) z a b p q`, assuming only `hz`.
There is no sign obstruction in this checked algebra.

The remaining proof must:

1. Differentiate the displayed contraction `W`, including the inverse-metric
   derivative and both Christoffel fields, then lower its two Lie slots.
2. Convert the coordinate trace written in `Module.finBasis` and the inverse
   continuous linear map into the `basis3` matrix contraction in the target.
3. Identify the actual second-order terms with `ricciSecondJet` and
   `lieSecondJet`, and construct the remaining bilinear expression as a
   function of `(G z, fderiv ℝ G z)` chosen before `g`.

No claim is made that the target is false or that the actual second-order
terms fail mathematically to cancel. The obstruction is the missing verified
coordinate identification and uniform first-jet factorization.

## Attempts and diagnostics

The coordinate route succeeded through the five lemmas above. The initial
rate proof failed at `rfl` because the Lie terms were associated differently
and the trace used `LinearMap.toContinuousLinearMap (b.coord i)`. Unfolding
the landed curvature definitions, simplifying that coercion, and normalizing
addition resolved it.

A real failed compiler output from the second-jet specialization was:

```text
Poincare/Global/DeTurckPrincipalSecondJet.lean:175:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedAddCommGroup (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
```

The specialization now compiles with local `maxSynthPendingDepth 100` and
local heartbeat limits. Other preserved failures include a leading-minus
parse ambiguity after a `let`, a matrix symmetry annotation inferred as a
function, and definitional `G` abbreviations remaining after simplification.
All are resolved in the committed source. These diagnostics are not being
presented as mathematical counterexamples or as a failure of the full target.

Full available scratch evidence is in
`/tmp/deturck-principal-second-jet-evidence/`: failed compiler logs,
per-stage probes, `FinalProbe.lean`, `final-gate.log`, and
`final-source.patch`. The final probe is the complete module source followed
by `#print axioms` for each of its 13 declarations. It does not import a stale
compiled copy of the new module. The final command transcript below is also
preserved here so the gate evidence survives scratch cleanup.

## Actual final gate output

The empty token scan exits 1, the expected ripgrep result for no matches.
All 13 declaration footprints were checked to be exactly
`[propext, Classical.choice, Quot.sound]`, including the auxiliary definitions.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckPrincipalSecondJet.lean
(no output)
exit_code=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DeTurckPrincipalSecondJet.lean
(no output)
exit_code=1

$ LEAN_NUM_THREADS=1 lake env lean /tmp/deturck-principal-second-jet-evidence/FinalProbe.lean
'Poincare.DeTurckPrincipalSecondJet.E' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.Bilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.Jet1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.basis3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.inverseEntries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.spatialPrincipal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.fieldDerivative_eq_contractionDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.evolution_eq_coordinate_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.ricciSecondJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.lieSecondJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.secondJet_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.chartMetric_secondJet_cancellation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalSecondJet.christoffelDerivative_eq_chartMetricSecondJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit_code=0

$ git diff --check
(no output)
exit_code=0

```

The complete source diff from the recorded base also passed
`git diff 502203724120a03fa3884df5fa24a242bf56fb0a --check` with no output,
exit 0. No root build or integration audit was run; this is a worker partial
result for independent orchestrator review, not an accepted task or merge.

## Next first action

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckPrincipalSecondJet.lean
```

Then target the derivative of `anchorChartDeTurckContractionFlow` used in
`fieldDerivative_eq_contractionDerivative`, with the raised covector kept
explicit. The Christoffel derivative bridge needed by that calculation is
now `christoffelDerivative_eq_chartMetricSecondJet` in the same module.
