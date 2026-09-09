# deturck-principal-identity: done

Verified 2026-09-09 UTC, 2026-09-08 America/Los_Angeles.
Base: `90c3f14e6658e2b463723d03601e6665e5bcacea`.
Branch: `worker/deturck-principal-identity`.
Verified proof head: `c19faddb7ae22d9d676c2190be747cc0e5f022c2`.

`Poincare.DeTurckPrincipalIdentity.principalIdentity` is proved with exactly
the frozen hypotheses and quantifier order. The new module is
`Poincare/Global/DeTurckPrincipalIdentity.lean` and imports only
`Poincare.Global.DeTurckPrincipalSecondJet`.

The final probe copied the complete current source, then checked an
`example` whose statement was extracted verbatim from the read-only task
file, with `principalIdentity bg anchor z hz hcut` as its proof. Thus this
check did not import a stale compiled copy of the new module.

## Uniform remainder

The existential witness is chosen before the varying metric:

```lean
let B := GeodesicTransport.chartChristoffelField bg anchor
lowerTerm (B z) (fderiv ℝ B z) : Bilin → Jet1 → Bilin
```

`lowerTerm_apply` gives its explicit value:

```lean
lowerTerm B DB G J v w =
  -2 * ricciFirst G J v w + lieFirst G J B DB v w
```

Every definition in this formula is finite algebra on `G`, `J`, and the
fixed background connection value and derivative. `fieldFirst` retains the
inverse-metric derivative, the evolving connection applied to the derivative
of the raised covector, the background connection derivative, and the
background connection applied to that raised-covector derivative.
`lieFirst` also retains the metric-advection term. The witness contains no
choice of a metric realizing the jets and no extra analytic premise.

## Proof route

1. `christoffel_eq_connection` and `christoffelDerivative_eq_jets` identify
   the actual Christoffel value and derivative with explicit metric jets.
   The derivative proof uses the landed
   `christoffelDerivative_eq_chartMetricSecondJet` and metric C2 regularity.
2. `fieldDerivative_eq_raised_derivative` differentiates the actual finite
   contraction with the inverse-raising derivative included.
   `fieldDerivative_eq_jets` then separates `fieldSecond` and `fieldFirst`.
3. `inverseEntries_eq_coordinates` identifies the matrix inverse with
   inverse-operator coefficients. `contraction_eq_matrix` uses trace
   invariance to replace `Module.finBasis` by `basis3`.
4. `lieSecondCoordinate_eq_lieSecondJet` and
   `ricciSecondCoordinate_eq_ricciSecondJet` identify the geometric
   second-order terms with the landed formal expressions.
5. The requested two complete decompositions are
   `lie_eq_secondJet_add_first` and `ricci_eq_secondJet_add_first`.
   Their remainders are the explicit `lieFirst` and `ricciFirst` functions.
6. `connectionOperator`, `fieldFirstOperator`, and `ricciFirstBilin` prove
   the needed linearity and bilinearity and construct `lowerTerm`.
   `principalIdentity` assembles the two decompositions with the landed
   `evolution_eq_coordinate_expression` and
   `chartMetric_secondJet_cancellation`.

No uncancelled term remains for this task. This proves the requested local
principal-part identity; it does not construct a Ricci flow or prove the
Poincare conjecture.

## Verification

All 39 source declarations were individually checked with `#print axioms`.
An additional namespace scan checked all 49 non-internal declarations,
including generated declarations, for equality with the three permitted
axioms, rather than merely excluding additional axioms. Every check passed.
The empty `rg` result has exit code 1, as expected.

Actual final command output follows. The probe also checks the frozen target
and the complete namespace footprint.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckPrincipalIdentity.lean
(no output)
exit_code=0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/DeTurckPrincipalIdentity.lean
(no output)
exit_code=1

$ LEAN_NUM_THREADS=1 lake env lean /tmp/deturck-principal-identity-evidence/FinalProbe.lean
'Poincare.DeTurckPrincipalIdentity.koszul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.connection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.koszul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldSecond' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lieSecondCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lieFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciSecondCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciFirst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.inverseEntries_eq_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.inverse_pairing_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.contraction_eq_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.continuousBilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lieTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lieTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lieSecondCoordinate_eq_lieSecondJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciSecondCoordinate_eq_ricciSecondJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.connectionOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.connectionOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldFirstOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldFirstOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciFirstBilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricciFirstBilin_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lowerTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lowerTerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.christoffel_eq_connection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.christoffelDerivative_eq_jets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldDerivative_eq_raised_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.fieldDerivative_eq_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.field_eq_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lie_eq_secondCoordinate_add_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricci_eq_secondCoordinate_add_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.chartMetric_secondJet_metric_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.chartMetric_isInvertible_of_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.lie_eq_secondJet_add_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.ricci_eq_secondJet_add_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DeTurckPrincipalIdentity.principalIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_FOOTPRINT_SCAN declarations=49 failures=[]
exit_code=0

$ git diff --check
(no output)
exit_code=0

$ git diff 90c3f14e6658e2b463723d03601e6665e5bcacea --check
(no output)
exit_code=0
```

The transcript parser additionally returned:

```text
NAMED_FOOTPRINT_CHECK declarations=39 exact=PASS
```

There was no root build or integration audit. Acceptance and merging remain
the orchestrator's responsibility. Existing Lean files, `Poincare.lean`,
frozen contracts, the task file, and `HANDOFF.md` were not changed. The task's
explicit file restriction takes precedence over the general handoff edit
instruction; this report is the dated handoff.

## Commits and evidence

Each verified lemma was committed before proceeding to the next lemma.
The final cleanup only removes unused hypotheses and simplifier arguments.

```text
a584f90f Define Koszul and connection expressions from metric first jets
3d2a0833 Identify the genuine chart Christoffel field with its first-jet expression
890ef0fe Split the Christoffel derivative into explicit first and second metric jets
fb75e319 Differentiate the DeTurck contraction including raised-covector motion
89c9803f Express the full DeTurck field derivative in metric jets and background data
16ed647b Identify the DeTurck field value as a uniform first-jet expression
0577fc0c Separate the geometric Lie expression into second and first metric jets
c5036da3 Separate the geometric Ricci trace into second and first metric jets
594604bc Identify inverse metric matrix entries with raised coordinate coefficients
f5543b11 Prove symmetry of the inverse-metric covector pairing
d5aafc9f Convert finite-basis metric contractions into the fixed inverse-matrix sums
63378596 Bundle the formal second-jet expressions in their contracted bilinear slots
72d34ba9 Identify the actual Lie second-jet contraction with the landed formal expression
9ba01a3b Identify the actual Ricci second-jet trace with the landed formal expression
5a1b2264 Bundle the explicit first-jet connection as a continuous bilinear operator
2a9c3366 Bundle the DeTurck field first-jet derivative remainder as a linear operator
db7675b7 Prove and bundle bilinearity of the explicit Ricci first-jet remainder
386ca7f9 Construct the uniform bilinear lower-order term from first jets
8deb869b Expose metric-slot symmetry of the genuine chart second jet
11804824 Supply chart-metric invertibility on the cutoff-one region
68c98669 Complete the Lie second-jet and uniform first-jet decomposition
9fb1acd5 Complete the Ricci second-jet and uniform first-jet decomposition
49ccb51d Prove the frozen DeTurck principal-part identity with a uniform first-jet remainder
c19faddb Remove unused hypotheses and simplifier arguments from the new module
```

Scratch evidence is preserved at
`/tmp/deturck-principal-identity-evidence/`: numbered compiler logs include
failed attempts, `FinalProbe.lean` contains the exact-target and complete
footprint checks, `run_final_gate.py` records actual subprocess exit codes,
`declaration-names.txt` lists source declarations, `final-gate.log` is the
transcript above, and `final-source.patch` is the complete source diff from
the base. The report preserves the successful output independently of
scratch-file lifetime.

The failed attempts were elaboration issues: a leading minus after a `let`
needed an explicit separator; function subtraction needed `Pi.sub_apply`
before rewriting its derivative; the Euclidean orthonormal basis needed
`.toBasis` for its coordinate linear maps; unrestricted inverse-pairing
rewrites rewrote the same term twice; and the final assembly had a redundant
`dsimp`. These are resolved in the verified source. No failed target or
additional hypothesis remains in the committed file.

## Exact next action

Independently rerun the task gate on this branch before integration:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DeTurckPrincipalIdentity.lean
```

Then review the diff against `90c3f14e6658e2b463723d03601e6665e5bcacea` and rerun the
frozen-target and full declaration-footprint probes. No merge was performed.
