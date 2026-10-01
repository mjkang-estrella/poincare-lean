# Levi-Civita uniqueness migration shapes, attempt a01

Inspected aligned `88f9d463817418be93153be8a137570854b9dad4` and original production `55e4859b54acb9044d7966a12df7a12afa8b52fd`. `Poincare/LeviCivitaUniqueness.lean` is byte-identical at those commits. The recorded second-layer log reports six scalar-derivative applications rejecting a scalar function where the current API expects a ModelWithCorners. Remaining MetricCompatibleAt function-application and missing-theorem errors follow ill-typed declarations; further genuine proof-body failures have not been established.

Latest aligned HANDOFF records accepted actual smoothability S while the retained root, strict successor contract, original Hamilton inputs/convergence and final endpoint acceptance remain pending. This preparation enables retained-root integration. It adds no original core closure.

## Exact API adaptation

Original Mathlib `extDerivFun` is a scalar-valued abbreviation with implicit model I. Its definition is

```lean
fun x => (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
  (mfderiv I 𝓘(ℝ, ℝ) f x)
```

Current Mathlib `mvfderiv` has explicit I and permits arbitrary normed-vector-space codomain. At codomain R its defining expression is the same; current `extDerivFun` is a deprecated alias of `mvfderiv`.

Recorded standalone probes in `levi-civita-433-api-a01` pass with exit 0 in each exact toolchain. Original probe checks `extDerivFun (I := I) f x =` the displayed formula by `rfl`. Current probe checks `extDerivFun I f = mvfderiv I f` and `mvfderiv I f x =` the same formula by `rfl`. The probes retain arbitrary E/H/M universes, all original normed instances, arbitrary manifold model I and original tangent fibers. No differentiability premise is used in these operator equalities. Every source, argv, cwd, commit, stdout/stderr and exit record is preserved. No source edit or build was performed.

The proposed current adaptation is exactly `extDerivFun (fun y => ...)` to `mvfderiv I (fun y => ...)`. A transitional spelling `extDerivFun (I := I) (fun y => ...)` also supplies the missing parameter, but keeps the deprecated name. Do not replace these expressions by ordinary fderiv: the manifold model is arbitrary.

## Definition and declaration guard

Permit exactly six call-site adaptations: MetricCompatibleAt RHS at line 39; the two derivative terms in leviCivita_unique_at_values' compatibility hypotheses at lines 133 and 138; the three scalar derivative terms in koszul_formula's conclusion at lines 221-223. The last five are theorem-signature syntax changes, not proof-body changes, so the reviewed contract must explicitly authorize and verify that normalization.

Preserve MetricCompatibleAt's entire quantified product-rule assertion after this one proven operator normalization: same g, cov, point x, implicit sections Y/Z, two MDiffAt premises, arbitrary tangent direction v and both original metric terms in their original order. Preserve TorsionFreeAt in full byte-for-byte; it needs no derivative rename. Preserve symmetry and nondegeneracy at x, all smoothness assumptions, all norms/topologies and existing connection arguments. Do not add positivity, a bundled Riemannian metric, completeness, finite-dimensionality, stronger regularity or global compatibility.

Freeze all ten original public declarations, exact unapplied types and universe orders, with the shared fully specified derivative expression used to validate the old/current API normalization:

- CovariantDerivative.MetricCompatibleAt
- CovariantDerivative.TorsionFreeAt
- CovariantDerivative.leviCivita_unique_at
- CovariantDerivative.leviCivita_unique_at_values
- CovariantDerivative.koszul_formula
- CovariantDerivative.metricCompatibleAt_eq
- CovariantDerivative.torsionFreeAt_eq
- CovariantDerivative.leviCivita_unique_at_eq
- CovariantDerivative.leviCivita_unique_at_values_eq
- CovariantDerivative.koszul_formula_eq

A normalized-source byte guard should allow the six exact operator substitutions and nothing else initially. If fresh Lean then identifies proof errors, restrict any successor proof repairs to the three uniqueness/Koszul theorem bodies, keeping their quantified statements fixed after reviewed API normalization. Preserve imports, namespaces, local instance/data declarations, TorsionFreeAt, all companion bodies and every other byte. No mathematical data-valued connection is constructed or modified in this module.

## Next scoped gate

After freezing and independently reviewing this exact normalization, first run `LEAN_NUM_THREADS=1 lake env lean Poincare/LeviCivitaUniqueness.lean` in an isolated scoped worker. Record actual remaining diagnostics before expanding proof-body scope. Follow a successful candidate with `LEAN_NUM_THREADS=1 lake build Poincare.LeviCivitaUniqueness`, the ten-declaration rigid-universe/fully elaborated literal and permitted-axiom/unsafe/partial probe, reviewed definition-normalization/body byte guard, placeholder scan and `git diff --check`. The current aliased operator equality is already checked; definition meanings must also be checked, not inferred merely from the two declarations having type Prop. No full build or final proof acceptance is claimed by this report.
