# Independent blind read-back

Verdict: **approved** for semantic preservation of the supplied frozen declarations. This review does not certify elaboration, compilation, proofs, audits, or project completion.

Reviewer: `/root/chart_api_route/chart_blind_review`  
Method: `blind-readback`  
Snapshot identifier: `355b2fbf84d03afe1e431caf7a0873d9a80bed40aa56f33f2f2536c19fbefd45`

Read only `blind-snapshot-a01.json`, `definitions-for-review.txt`, and `original-kernel-types-a01.json`. No task objective, proposed report, other chat, or unrelated source was read. No Lean or shell/child process was invoked and no source was edited.

## Notation

- **D_I**: For g : M → κ, D_I g z := (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf κ κ) g z). It is a continuous κ-linear map TangentSpace I z → κ.
- **chart**: e := extChartAt I x, or extChartAt I x₀ for a fixed chart; e is a partial equivalence M ⇌ E and e.symm is its inverse-chart function.
- **real_chart**: e := extChartAt I′ x : N ⇌ E′; a := e x; F := f ∘ e.symm; Uhat := VectorField.mpullback (modelWithCornersSelf ℝ E′) I′ e.symm U.
- **T_U**: The tangent-bundle section y ↦ Bundle.TotalSpace.mk′ E′ y (U y), with target model I′.prod (modelWithCornersSelf ℝ E′).

## Declaration read-back

### mlieBracket_apply_chart

Universes in declaration order: `u_1, u_2, u_3, u_4`.

mlieBracket I X Y x equals the vector-space lieBracketWithin κ, within range I, of the two mpullbackWithin fields under e.symm, evaluated at e x.

Conditions:

- κ : Type u_1 is any nontrivially normed field; E : Type u_2 is a normed additive commutative group with a NormedSpace κ E instance.
- H : Type u_3 and M : Type u_4 are topological spaces; M has ChartedSpace H M.
- I : ModelWithCorners κ E H is the supplied domain model; tangent vectors and fields use TangentSpace I y, whose underlying type is E.
- IsManifold I 1 M.
- X and Y are arbitrary tangent fields; x is any point of M.

No differentiability of X or Y, boundarylessness, completeness, or finite dimensionality is assumed. This is an identity for the defined total bracket operators; range I is retained.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### mpullbackWithin_extChartAt_symm_self

Universes in declaration order: `u_1, u_2, u_3, u_4`.

The mpullbackWithin of X under e.symm within range I, at e x, is exactly X x.

Conditions:

- κ : Type u_1 is any nontrivially normed field; E : Type u_2 is a normed additive commutative group with a NormedSpace κ E instance.
- H : Type u_3 and M : Type u_4 are topological spaces; M has ChartedSpace H M.
- I : ModelWithCorners κ E H is the supplied domain model; tangent vectors and fields use TangentSpace I y, whose underlying type is E.
- IsManifold I 1 M.
- X is an arbitrary tangent field; x is any point of M.

At the center of the chart, not at arbitrary chart points. No differentiability of X, boundarylessness, completeness, or finite dimensionality is assumed.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_chart

Universes in declaration order: `u_1, u_2, u_3, u_4`.

D_I f x v = fderiv κ (f ∘ e.symm) (e x) v.

Conditions:

- κ : Type u_1 is any nontrivially normed field; E : Type u_2 is a normed additive commutative group with a NormedSpace κ E instance.
- H : Type u_3 and M : Type u_4 are topological spaces; M has ChartedSpace H M.
- I : ModelWithCorners κ E H is the supplied domain model; tangent vectors and fields use TangentSpace I y, whose underlying type is E.
- I.Boundaryless.
- f : M → κ; x : M; MDifferentiableAt I (modelWithCornersSelf κ κ) f x; v : TangentSpace I x.

IsManifold I 1 M is absent from this declaration, as in the original kernel type and the source omit directive. The arbitrary nontrivially normed field is retained; no completeness or finite-dimensional assumption is introduced.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_fixed_chart

Universes in declaration order: `u_1, u_2, u_3, u_4`.

Writing e := extChartAt I x₀, D_I f y v = fderiv κ (f ∘ e.symm) (e y) ((mfderiv I (modelWithCornersSelf κ E) e y) v).

Conditions:

- κ : Type u_1 is any nontrivially normed field; E : Type u_2 is a normed additive commutative group with a NormedSpace κ E instance.
- H : Type u_3 and M : Type u_4 are topological spaces; M has ChartedSpace H M.
- I : ModelWithCorners κ E H is the supplied domain model; tangent vectors and fields use TangentSpace I y, whose underlying type is E.
- IsManifold I 1 M and I.Boundaryless.
- f : M → κ; x₀,y : M; y belongs to (extChartAt I x₀).source.
- MDifferentiableAt I (modelWithCornersSelf κ κ) f y; v : TangentSpace I y.

The chart is fixed at x₀, so its derivative pushes v forward. No claim is made outside its source. No C², global regularity, completeness, or finite dimensionality is assumed.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### isLocallyConstant_of_extDerivFun_eq_zero

Universes in declaration order: `u_5, u_6, u_7`.

f is IsLocallyConstant: around every point its value is locally fixed.

Conditions:

- E : Type u_5 is a normed additive commutative group and a normed real vector space.
- H : Type u_6 and M : Type u_7 are topological spaces; M has ChartedSpace H M; I : ModelWithCorners ℝ E H.
- IsManifold I 1 M and I.Boundaryless.
- f : M → ℝ is manifold-differentiable at every x, using the target self model ℝ.
- For every x : M and every w : TangentSpace I x, D_I f x w = 0.

This is real-valued and global only in its hypotheses over all points. It does not assert global constancy without a connectedness hypothesis; no connectedness, completeness, or finite-dimensional assumption is present.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_mlieBracket_chart

Universes in declaration order: `u_5, u_6, u_7`.

D_I′ f x (mlieBracket I′ X Y x) = fderiv ℝ (z ↦ fderiv ℝ F z (Yhat z)) a (X x) − fderiv ℝ (z ↦ fderiv ℝ F z (Xhat z)) a (Y x).

Conditions:

- E′ : Type u_5 is a normed additive commutative group, a normed real vector space, and CompleteSpace E′.
- H′ : Type u_6 and N : Type u_7 are topological spaces; N has ChartedSpace H′ N; I′ : ModelWithCorners ℝ E′ H′.
- IsManifold I′ 2 N and I′.Boundaryless; all fields are dependent sections y ↦ TangentSpace I′ y.
- f : N → ℝ; X,Y are tangent fields; x : N.
- ContMDiffAt I′ (modelWithCornersSelf ℝ ℝ) 2 f x.
- MDifferentiableAt I′ (I′.prod (modelWithCornersSelf ℝ E′)) T_X x and the same condition for T_Y.

Pointwise bracket-derivation identity in the chart centered at x. The sign is X(Yf) − Y(Xf). C² regularity is for f at x; first-order manifold differentiability is for both tangent-bundle sections at x. No global field regularity or existence is asserted.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### mpullback_extChartAt_symm_apply

Universes in declaration order: `u_5, u_6, u_7`.

For e := extChartAt I′ x, Uhat (e y) = (mfderiv I′ (modelWithCornersSelf ℝ E′) e y) (U y).

Conditions:

- E′ : Type u_5 is a normed additive commutative group, a normed real vector space, and CompleteSpace E′.
- H′ : Type u_6 and N : Type u_7 are topological spaces; N has ChartedSpace H′ N; I′ : ModelWithCorners ℝ E′ H′.
- IsManifold I′ 2 N and I′.Boundaryless; all fields are dependent sections y ↦ TangentSpace I′ y.
- x,y : N; y belongs to (extChartAt I′ x).source; U is any tangent field.

The original C², real, boundaryless, complete-model assumptions are retained, even though the formula concerns one chart and an arbitrary U. No differentiability of U is required; membership in the chart source is required.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_section_eventually_chart

Universes in declaration order: `u_5, u_6, u_7`.

For each U, eventually for y in the neighborhood filter nhds x, D_I′ f y (U y) = fderiv ℝ F (e y) (Uhat (e y)).

Conditions:

- E′ : Type u_5 is a normed additive commutative group, a normed real vector space, and CompleteSpace E′.
- H′ : Type u_6 and N : Type u_7 are topological spaces; N has ChartedSpace H′ N; I′ : ModelWithCorners ℝ E′ H′.
- IsManifold I′ 2 N and I′.Boundaryless; all fields are dependent sections y ↦ TangentSpace I′ y.
- f : N → ℝ; x : N; ContMDiffAt I′ (modelWithCornersSelf ℝ ℝ) 2 f x.
- For every tangent field U, with no regularity assumption on U.

The formal order is ∀ U, eventually y; it is a local eventual equality, not an equality over all N or over all chart-source points under these hypotheses. No differentiability of U is imposed.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_extDerivFun_chart

Universes in declaration order: `u_5, u_6, u_7`.

D_I′ (y ↦ D_I′ f y (U y)) x v = fderiv ℝ (z ↦ fderiv ℝ F z (Uhat z)) a v.

Conditions:

- E′ : Type u_5 is a normed additive commutative group, a normed real vector space, and CompleteSpace E′.
- H′ : Type u_6 and N : Type u_7 are topological spaces; N has ChartedSpace H′ N; I′ : ModelWithCorners ℝ E′ H′.
- IsManifold I′ 2 N and I′.Boundaryless; all fields are dependent sections y ↦ TangentSpace I′ y.
- f : N → ℝ; U is a tangent field; x : N; v : TangentSpace I′ x.
- ContMDiffAt I′ (modelWithCornersSelf ℝ ℝ) 2 f x.
- MDifferentiableAt I′ (I′.prod (modelWithCornersSelf ℝ E′)) T_U x.

An iterated scalar directional derivative at x along a varying differentiable tangent section. The outer operator is the same supplied-model D_I′ applied to the new scalar function. No globally differentiable or globally defined solution is asserted.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_mlieBracket

Universes in declaration order: `u_5, u_6, u_7`.

D_I′ f x (mlieBracket I′ X Y x) = D_I′ (y ↦ D_I′ f y (Y y)) x (X x) − D_I′ (y ↦ D_I′ f y (X y)) x (Y x).

Conditions:

- E′ : Type u_5 is a normed additive commutative group, a normed real vector space, and CompleteSpace E′.
- H′ : Type u_6 and N : Type u_7 are topological spaces; N has ChartedSpace H′ N; I′ : ModelWithCorners ℝ E′ H′.
- IsManifold I′ 2 N and I′.Boundaryless; all fields are dependent sections y ↦ TangentSpace I′ y.
- f : N → ℝ; X,Y are tangent fields; x : N.
- ContMDiffAt I′ (modelWithCornersSelf ℝ ℝ) 2 f x.
- MDifferentiableAt I′ (I′.prod (modelWithCornersSelf ℝ E′)) T_X x and the same condition for T_Y.

Invariant pointwise commutator identity df([X,Y]) = X(Yf) − Y(Xf). All five scalar-operator occurrences use the same supplied model I′ and target self model ℝ. No global topology or Poincare claim is present.

Same quantified parameters, manifold/model/scalar/tangent/regularity hypotheses, chart membership or eventual quantifier, and mathematical conclusion as the supplied original printed/kernel type, after expanding the original scalar abbreviation where present.

No omitted original assumption or semantic weakening detected.

### mlieBracket_apply_chart_eq

Universes in declaration order: `u_5, u_6, u_7, u_8`.

The fully unapplied theorem proof @mlieBracket_apply_chart equals itself at the displayed universes: Eq.{0} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### mpullbackWithin_extChartAt_symm_self_eq

Universes in declaration order: `u_5, u_6, u_7, u_8`.

The fully unapplied theorem proof @mpullbackWithin_extChartAt_symm_self equals itself at the displayed universes: Eq.{0} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_chart_eq

Universes in declaration order: `u_5, u_6, u_7, u_8`.

The fully unapplied theorem proof @extDerivFun_apply_chart equals itself at the displayed universes: Eq.{0} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_fixed_chart_eq

Universes in declaration order: `u_5, u_6, u_7, u_8`.

The fully unapplied theorem proof @extDerivFun_apply_fixed_chart equals itself at the displayed universes: Eq.{0} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### isLocallyConstant_of_extDerivFun_eq_zero_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @isLocallyConstant_of_extDerivFun_eq_zero equals itself at the displayed universes: Eq.{0} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_mlieBracket_chart_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @extDerivFun_apply_mlieBracket_chart equals itself at the displayed universes: Eq.{0} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### mpullback_extChartAt_symm_apply_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @mpullback_extChartAt_symm_apply equals itself at the displayed universes: Eq.{0} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_section_eventually_chart_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @extDerivFun_section_eventually_chart equals itself at the displayed universes: Eq.{0} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_extDerivFun_chart_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @extDerivFun_extDerivFun_chart equals itself at the displayed universes: Eq.{0} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

### extDerivFun_apply_mlieBracket_eq

Universes in declaration order: `u_5, u_6, u_7`.

The fully unapplied theorem proof @extDerivFun_apply_mlieBracket equals itself at the displayed universes: Eq.{0} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7}

No additional manifold, function, vector-field, or regularity hypotheses are separately bound by this companion. They occur inside the proposition/type of the referenced primary theorem proof.

Reflexive equality of a proof object (Eq.{0}); neither a new instance of the primary calculus claim nor equality of old and new implementations, and no existence or completion claim.

The supplied original companion type is textually identical, including the universe list and both proof constants.

No omitted original assumption or semantic weakening detected.

## Findings

### Scalar normalization and supplied model

Seven primary declarations use D_I or D_I′. The original extDerivFun abbreviation is exactly (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf κ κ) g z). The supplied current mvfderiv definition has the same expression for a vector-valued target F; specializing F to κ and explicitly supplying I yields the frozen scalar formula. Its current extDerivFun alias points to mvfderiv. In the real family, every occurrence, including inner and outer iterated derivatives, uses I′. This is operator expansion and explicit model selection, with no substituted derivative, changed scalar, weakened regularity, or boundary assumption removed.

### Actual declaration universe order

All 20 universe arrays match their supplied originals exactly. The first four primary declarations are [u_1,u_2,u_3,u_4] with roles κ,E,H,M. The remaining six primary declarations are [u_5,u_6,u_7] with roles E/H/M or E′/H′/N over scalar ℝ in universe 0. The first four companions are [u_5,u_6,u_7,u_8], applied in that order to primary theorem arguments κ,E,H,M; the other six companions are [u_5,u_6,u_7]. These are declaration-level lists, not the argument order of every constant in a type. In particular TangentSpace.{u_2,u_1,u_3,u_4} orders E,κ,H,M; extChartAt.{u_1,u_2,u_4,u_3} orders κ,E,M,H; VectorField.mlieBracket.{u_1,u_3,u_2,u_4} orders κ,H,E,M. The real specializations retain those permutations. Tangent-section regularity retains the displayed max u_5 u_6 and max u_5 u_7 target universes.

### Source h2 and current inverse-chart identity

The source h2 in mpullbackWithin_extChartAt_symm_self asserts mfderivWithin (modelWithCornersSelf κ E) I e.symm (range I) (e x) = ContinuousLinearMap.id κ E, under the generic κ C¹ chart context. The supplied current lemma mfderivWithin_range_extChartAt_symm states the same local, within-range derivative identity, with its underscore resolving to E. The inverse_apply lemma is its consequence. This stays at the chart center and within range I; replacing it by an unrestricted derivative identity for manifolds with boundary, or by invertibility everywhere, would be a reinterpretation. No such change is present in the frozen types.

### Tangent identification

The supplied TangentSpace definition is E, with the manifold/model/point arguments carried in the type and derived instances. NormedSpace.fromTangentSpace explicitly identifies the target tangent space of the self model with its normed vector space by identity functions. Thus applying the chart-centered formulas directly to v, X x, or Y x is justified by this chosen tangent representation; the fixed-chart formula correctly includes the chart derivative at a noncenter point.

### Missing assumptions and limits

No assumption present in the supplied original theorem surfaces was omitted in the frozen read-back. The extDerivFun_apply_chart declaration intentionally has no IsManifold hypothesis. Initial bracket/pullback identities do not require differentiability of arbitrary fields. The eventual scalar section formula does not require U to be differentiable. The other higher-order real identities require C² f at x and differentiability at x of the relevant tangent-bundle sections; the ambient real C², boundaryless, CompleteSpace assumptions remain. No theorem assumes finite dimensionality, dimension three, compactness, connectedness, simple connectedness, orientation, or a specific sphere.

### Proof equality companions

The ten existing _eq declarations are proof-self-equalities only, all with Eq.{0}. They cannot establish preservation between two different versions of an operator, furnish new geometric content, or establish the underlying theorem by themselves.

### No independent global existence or completion

The types provide chart identifications, scalar derivative formulas, a local-constancy implication under everywhere-zero derivative hypotheses, and local bracket-derivation identities. They do not independently construct manifolds, vector fields, global geometric structures, homeomorphisms, or Poincare.poincare_conjecture. Importing Poincare.ChartIdentification is not completion evidence.

### Review boundary

Approval is confined to the mathematical content of the frozen declarations and their match to the supplied source/kernel evidence. No Lean process, build, audit, source edit, theorem probe, or independent elaboration check was performed.

## Evidence boundary

The snapshot identifier above is the identifier embedded in the frozen input. The JSON file byte SHA-256 is `118c4e36be3d218c733445db708c6d47c76c62c628e8e6741f8a4e8156b4a157`. The definitions-context byte SHA-256 is `c4f1567e0fa1838920a498595d11edee80e4d754bd5ef52c2b93437f25af2ef4`.

This is a read-only mathematical review of the supplied evidence. Compilation and acceptance remain outside this verdict.
