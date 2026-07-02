# Mathlib gap survey for the manifold-level Perelman program

Pinned Mathlib surveyed: `.lake/packages/mathlib/` at
`7175569c842f9164564bd76ff8b207e7b4705522`, matching the root
`lake-manifest.json`.

Method: direct `rg`/file reads against the pinned tree only. Status meanings:
`EXISTS` means the named layer has real reusable declarations in Mathlib;
`PARTIAL` means useful foundations exist but key Perelman-facing pieces are
missing; `ABSENT` means no manifold-level implementation was found, apart from
nearby Euclidean or statement-only material.

## Summary

| Area | Status | Short reason |
| --- | --- | --- |
| Smooth manifolds | EXISTS | Charted spaces, `IsManifold`, smooth maps, tangent spaces, and smooth partitions of unity are present. |
| Vector bundles | PARTIAL | Smooth vector bundles, tangent bundle, smooth-section lemmas, and bundle metrics exist; cotangent/tensor bundle hierarchy is missing. |
| Riemannian metrics | PARTIAL | Smooth Riemannian bundle metrics and Riemannian distance exist; Levi-Civita, geodesics, and curvature are absent. |
| Connections | PARTIAL | Koszul covariant derivatives and torsion exist; no Levi-Civita construction, curvature, or parallel transport. |
| Integration on manifolds | ABSENT | No volume forms, manifold Stokes theorem, or manifold divergence theorem found. |
| Algebraic topology | PARTIAL | Fundamental group, simply connected spaces, covering maps, homology foundations exist; sphere homology/classification is absent. |
| PDE | PARTIAL | Sobolev/distribution/Laplacian and ODE pieces exist; elliptic/parabolic/geometric-flow theory is absent. |
| The sphere | PARTIAL | Smooth sphere instances exist; simply-connectedness and classification facts are absent. |
| Gromov-Hausdorff / metric geometry | PARTIAL | Compact GH space is substantial; pointed/noncompact/measured blow-up-limit machinery is absent. |
| Prior art | ABSENT | No Ricci-flow, mean-curvature-flow, or geometric-analysis development found; only statement stubs. |

## 1. Smooth Manifolds - EXISTS

Found modules and declarations:

- `Mathlib/Geometry/Manifold/ChartedSpace.lean`: `ChartedSpace`.
- `Mathlib/Geometry/Manifold/IsManifold/Basic.lean`: `IsManifold`, `TangentSpace`,
  `TangentBundle`.
- `Mathlib/Geometry/Manifold/ContMDiff/Defs.lean`: `ContMDiff`,
  `ContMDiffAt`, `ContMDiffWithinAt`, `ContMDiffOn`.
- `Mathlib/Geometry/Manifold/ContMDiffMap.lean`: bundled smooth maps
  `ContMDiffMap`.
- `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`: `SmoothPartitionOfUnity`,
  `SmoothBumpCovering`, `SmoothPartitionOfUnity.exists_isSubordinate`,
  `SmoothPartitionOfUnity.contMDiff_finsum_smul`.
- `Mathlib/Geometry/Manifold/BumpFunction.lean`: `SmoothBumpFunction`.
- `Mathlib/Geometry/Manifold/SmoothApprox.lean`: smooth approximation imports
  and uses the partition-of-unity layer.

Assessment: The smooth-manifold substrate is real and usable. The partition of
unity API is strongest under finite-dimensional real, sigma-compact Hausdorff
hypotheses, which is acceptable for many compact-manifold bridge statements but
must be carried explicitly.

## 2. Vector Bundles - PARTIAL

Found modules and declarations:

- `Mathlib/Topology/VectorBundle/Basic.lean`: topological vector-bundle
  foundations.
- `Mathlib/Geometry/Manifold/VectorBundle/Basic.lean`:
  `ContMDiffVectorBundle`, `Bundle.TotalSpace.isManifold`,
  `ContMDiffVectorPrebundle.contMDiffVectorBundle`.
- `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean`:
  `tangentBundleCore`, `TangentSpace.fiberBundle`,
  `TangentSpace.vectorBundle`, `TangentBundle.contMDiffVectorBundle`.
- `Mathlib/Geometry/Manifold/VectorBundle/SmoothSection.lean`:
  `ContMDiff.add_section`, `ContMDiff.neg_section`,
  `ContMDiff.sub_section`, `ContMDiff.smul_section`,
  `ContMDiff.sum_section`, `ContMDiff.finsum_section_of_locallyFinite`.
- `Mathlib/Topology/VectorBundle/Riemannian.lean`:
  `IsContinuousRiemannianBundle`, `RiemannianMetric`,
  `RiemannianBundle`, `ContinuousRiemannianMetric`.
- `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`:
  `IsContMDiffRiemannianBundle`, `ContMDiff.inner_bundle`,
  `ContMDiffRiemannianMetric`.
- `Mathlib/Geometry/Manifold/VectorBundle/Tensoriality.lean`:
  `TensorialAt`, `TensorialAt.mkHom`, `TensorialAt.mkHom₂`.
- `Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`: `extDerivFun`,
  described there as the exterior derivative of a scalar function as a
  cotangent-bundle section.

Searches found no declarations named `CotangentBundle`, `TensorBundle`, or
`TensorField` in the manifold/vector-bundle tree.

Assessment: Tangent bundles and smooth vector bundles are in good shape, and
bundle metrics exist. For Perelman-level work, the missing layer is a systematic
cotangent/tensor bundle and tensor-field hierarchy; current one-form-like
objects are represented as dependent families such as
`TangentSpace I x ->L[... ] ...` rather than bundled tensor fields.

## 3. Riemannian Metrics On Manifolds - PARTIAL

Found modules and declarations:

- `Mathlib/Topology/VectorBundle/Riemannian.lean`: `RiemannianMetric`,
  `RiemannianBundle`, `ContinuousRiemannianMetric`.
- `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`:
  `ContMDiffRiemannianMetric`, `IsContMDiffRiemannianBundle`,
  `ContMDiff.inner_bundle`.
- `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`:
  `pathELength`, `riemannianEDist`,
  `pathELength_eq_lintegral_mfderiv_Icc`,
  `riemannianEDist_le_pathELength`, `riemannianEDist_self`,
  `riemannianEDist_comm`, `riemannianEDist_triangle`.
- `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`:
  `IsRiemannianManifold`, `riemannianMetricVectorSpace`,
  `PseudoEMetricSpace.ofRiemannianMetric`,
  `EMetricSpace.ofRiemannianMetric`.

Searches under `Mathlib/Geometry/Manifold` found no usable declarations for
`Levi`, `Civita`, `Christoffel`, `geodesic`, `Curvature`, `Ricci`, sectional
curvature, or scalar curvature.

Assessment: Mathlib has a smooth Riemannian metric abstraction and distance via
path length. The differential-geometric engine needed by Ricci flow--Levi-Civita
connection, geodesics, curvature tensors, Ricci/scalar curvature, and their
identities--is absent.

## 4. Connections / Covariant Derivatives - PARTIAL

Found modules and declarations:

- `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`:
  `IsCovariantDerivativeOn`, `ContMDiffCovariantDerivativeOn`,
  `CovariantDerivative`, `ContMDiffCovariantDerivative`,
  `IsCovariantDerivativeOn.add_one_form`,
  `IsCovariantDerivativeOn.difference`,
  `CovariantDerivative.addOneForm`, `CovariantDerivative.difference`.
- `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Torsion.lean`:
  `IsCovariantDerivativeOn.torsion`, `CovariantDerivative.torsion`,
  `CovariantDerivative.torsion_eq_zero_iff`.

Assessment: There is a serious starting point for Koszul connections on vector
bundles, including torsion for tangent-bundle connections. Missing pieces for
our use are existence of smooth connections by partition of unity, the
Levi-Civita connection from a metric, curvature of a connection, Bianchi-style
identities, and parallel transport.

## 5. Integration On Manifolds - ABSENT

Found nearby modules and declarations:

- `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`: `extDeriv`,
  `extDerivWithin`, and second-exterior-derivative-zero theorems for normed
  spaces. Its TODO explicitly says the manifold version is not defined yet.
- `Mathlib/Analysis/Calculus/DifferentialForm/VectorField.lean`: vector-field
  evaluation of differential forms on normed spaces.
- `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`:
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` for boxes in
  Euclidean spaces.
- `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`:
  `BoxIntegral.hasIntegral_GP_pderiv` and related rectangular-box statements.
- `Mathlib/Geometry/Euclidean/Volume/Measure.lean`:
  `MeasureTheory.Measure.euclideanHausdorffMeasure` and notation `μHE[...]`.
- `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`:
  Poincare lemma material for 1-forms on convex subsets of normed spaces, such
  as `exists_forall_hasFDerivAt_of_fderiv_symmetric`.
- `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`: a TODO mentions using the
  partition-of-unity layer to define integrals of differential forms over
  manifolds.

Assessment: I found no manifold volume forms, no integration of differential
forms over manifolds, no Stokes theorem on manifolds, and no divergence theorem
on Riemannian manifolds. The available material is Euclidean/normed-space
infrastructure, not a manifold integration layer.

## 6. Algebraic Topology - PARTIAL

Found modules and declarations:

- `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`:
  `FundamentalGroup`, `FundamentalGroup.map`,
  `fundamentalGroupMulEquivOfPath`,
  `fundamentalGroupMulEquivOfPathConnected`.
- `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`:
  `SimplyConnectedSpace`, `IsSimplyConnected`,
  `simply_connected_iff_unique_homotopic`,
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`.
- `Mathlib/Topology/Covering/Basic.lean`: `IsEvenlyCovered`,
  `IsCoveringMapOn`, `IsCoveringMap`.
- `Mathlib/Topology/Homotopy/Lifting.lean`:
  `IsCoveringMap.exists_path_lifts`, `IsCoveringMap.liftPath`,
  `IsCoveringMap.liftHomotopy`,
  `IsCoveringMap.existsUnique_continuousMap_lifts`.
- `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`:
  `singularHomology`.
- `Mathlib/AlgebraicTopology/SingularHomology/HomologyZero.lean`:
  `singularHomology₀Iso`, `singularHomology₀ε`,
  `singularHomology₀Iso_sigma_desc_id`.
- `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`:
  `SimplicialSet.chainComplex`, `SimplicialSet.homology`,
  `SimplicialSet.homologyMap`, `SimplicialSet.homologyFunctor`.
- `Mathlib/Topology/Homotopy/HomotopyGroup.lean`: `HomotopyGroup`,
  `HomotopyGroup.Pi`, `HomotopyGroup.pi1EquivFundamentalGroup`.
- `Mathlib/Topology/CWComplex/Classical/Basic.lean`: `CWComplex`.
- `Mathlib/Geometry/Manifold/PoincareConjecture.lean`: statement stubs
  `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere`,
  `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`,
  `SimplyConnectedSpace.nonempty_diffeomorph_sphere_three`.

Searches for `Betti`, sphere homology, and sphere homeomorphism-classification
machinery did not find a usable classification layer.

Assessment: Basic homotopy, fundamental group, covering-space, and homology
foundations exist. The topological input Perelman needs--homology of spheres,
3-manifold classification/Poincare-level conclusions, and sphere
homeomorphism/diffeomorphism classification--is not proved in Mathlib; the
Poincare file is statement-only via `proof_wanted`.

## 7. PDE - PARTIAL

Found modules and declarations:

- `Mathlib/Analysis/Distribution/Sobolev.lean`:
  `TemperedDistribution.besselPotential`,
  `TemperedDistribution.MemSobolev`, `MemSobolev.laplacian`,
  `MemSobolev.fourierMultiplierCLM_of_bounded`.
- `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`:
  `MeasureTheory.eLpNorm_le_eLpNorm_fderiv` and related
  Gagliardo-Nirenberg-Sobolev inequalities.
- `Mathlib/Analysis/Distribution/DerivNotation.lean`: `Laplacian`.
- `Mathlib/Analysis/InnerProductSpace/Laplacian.lean`:
  `instLaplacian` for functions on finite-dimensional real inner-product
  spaces.
- `Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean` and
  `Mathlib/Analysis/Distribution/TemperedDistribution.lean`: distributional
  derivative/Laplacian material.
- `Mathlib/Analysis/ODE/PicardLindelof.lean`: `IsPicardLindelof`,
  `ODE.picard`, and local existence theorems for Banach-space ODEs.
- `Mathlib/Dynamics/Flow.lean`: topological/dynamical `Flow`.

Searches did not find short-time existence for geometric flows, heat-equation
semigroup theory, Hille-Yosida-style generator theory, elliptic regularity, or
parabolic Schauder/Sobolev theory.

Assessment: There is meaningful analytic infrastructure for distributions,
Sobolev spaces, Euclidean Laplacians, and ODEs. It is not close to the
quasilinear parabolic PDE theory needed for Ricci-flow short-time existence or
the estimates used in Perelman's program.

## 8. The Sphere - PARTIAL

Found modules and declarations:

- `Mathlib/Geometry/Manifold/Instances/Sphere.lean`: stereographic charts
  `stereographic`, `stereographic'`; sphere instances
  `EuclideanSpace.instChartedSpaceSphere`,
  `EuclideanSpace.instIsManifoldSphere`; smoothness lemmas
  `contMDiff_coe_sphere`, `ContMDiff.codRestrict_sphere`,
  `contMDiff_neg_sphere`; tangent-map lemmas
  `range_mfderiv_coe_sphere`, `mfderiv_coe_sphere_injective`; circle manifold
  and Lie group instances.
- `Mathlib/Topology/Compactification/OnePoint/Sphere.lean`:
  `onePointHyperplaneHomeoUnitSphere`,
  `onePointEquivSphereOfFinrankEq`.
- `Mathlib/Topology/Category/TopCat/Sphere.lean`: `TopCat.sphere`,
  `TopCat.disk`, `TopCat.diskBoundary`, `TopCat.ball`.
- `Mathlib/Topology/Homeomorph/Defs.lean`: `Homeomorph` and notation
  `X ≃ₜ Y`.
- `Mathlib/Geometry/Manifold/Diffeomorph.lean`: `Diffeomorph` and manifold
  diffeomorphism notation.

Searches found no `SimplyConnectedSpace` instance/theorem for `Metric.sphere`
and no sphere homology/classification facts.

Assessment: The smooth structure on Euclidean metric spheres is present and
usable. What is missing is the algebraic-topology bridge: simple
connectedness of higher spheres, homology of spheres, and any
homeomorphism-classification machinery that could turn homotopy/topological
hypotheses into `Nonempty (M ≃ₜ sphere ...)`.

## 9. Gromov-Hausdorff / Metric Geometry - PARTIAL

Found modules and declarations:

- `Mathlib/Topology/MetricSpace/HausdorffDistance.lean`:
  `Metric.infEDist`, `hausdorffEDist`, `hausdorffDist`,
  `hausdorffEDist_triangle`, `hausdorffDist_triangle`,
  `hausdorffEDist_zero_iff_closure_eq_closure`,
  `hausdorffDist_zero_iff_closure_eq_closure`,
  `hausdorffDist_image`.
- `Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean`:
  namespace `GromovHausdorff`; `candidates`, `HD`,
  `candidatesBOfCandidates`, `candidatesBDist`,
  `premetricOptimalGHDist`, `OptimalGHCoupling`,
  `optimalGHInjl`, `optimalGHInjr`,
  `isometry_optimalGHInjl`, `isometry_optimalGHInjr`,
  `compactSpace_optimalGHCoupling`,
  `hausdorffDist_optimal_le_HD`.
- `Mathlib/Topology/MetricSpace/GromovHausdorff.lean`:
  `GromovHausdorff.GHSpace`, `GromovHausdorff.toGHSpace`,
  `GromovHausdorff.GHSpace.Rep`, `GromovHausdorff.ghDist`,
  `GromovHausdorff.ghDist_le_hausdorffDist`,
  `GromovHausdorff.hausdorffDist_optimal`,
  `GromovHausdorff.ghDist_eq_hausdorffDist`,
  `MetricSpace GHSpace`, `SecondCountableTopology GHSpace`,
  `GromovHausdorff.ghDist_le_of_approx_subsets`,
  `GromovHausdorff.totallyBounded`, `CompleteSpace GHSpace`.
- `Mathlib/Topology/MetricSpace/HausdorffDimension.lean`: Hausdorff-dimension
  theory and Lipschitz/smooth-image bounds.

Assessment: Compact Gromov-Hausdorff distance is much stronger than expected:
the GH space is metric, second-countable, complete, and has a total-boundedness
criterion. Perelman blow-up limits still need major bridges: pointed/noncompact
GH or Cheeger-Gromov convergence, measured GH, curvature/injectivity-radius
hypotheses, and links from Riemannian manifolds to compact metric-space
representatives.

## 10. Prior Art For Ricci Flow / MCF / Geometric Analysis - ABSENT

Searches used case-insensitive greps for `ricci-flow`, `Ricci flow`,
`mean-curvature-flow`, `mean curvature flow`, `curvature flow`,
`geometric-analysis`, `geometric analysis`, and `Perelman`.

Found modules and declarations:

- `Mathlib/Geometry/Manifold/PoincareConjecture.lean`: statement-only
  `proof_wanted` declarations for the generalized Poincare conjecture,
  3-dimensional topological Poincare, 3-dimensional smooth Poincare, exotic
  7-sphere, and exotic `R^4`.
- `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`: Poincare lemma
  for 1-forms on convex subsets of normed spaces, unrelated to Ricci flow.
- `Mathlib/Analysis/Complex/UpperHalfPlane/Metric.lean` and
  `Mathlib/Analysis/Complex/UnitDisc/Basic.lean`: Poincare metric/disc
  terminology, unrelated to the 3-manifold program.

Assessment: There is no Ricci-flow, mean-curvature-flow, or geometric-analysis
development to reuse. The closest Perelman-named file is a statement-only
Poincare-conjecture stub, so any M1 manifold-level Perelman program must build
the geometry and analysis stack itself.

## Cheapest High-Value Bridge Tasks

1. **Standard Riemannian context wrapper.** Create a local import/context module
   that packages `IsManifold`, `RiemannianBundle`,
   `IsContMDiffRiemannianBundle`, `IsRiemannianManifold`, `TangentSpace`,
   and `TangentBundle` for compact smooth Riemannian manifolds. This is mostly
   namespace and instance plumbing. Estimated effort: 2-4 days.
2. **Sphere-3 bridge facts.** Package `Metric.sphere (0 :
   EuclideanSpace ℝ (Fin 4)) 1` as the canonical smooth 3-sphere with its
   charted-space, manifold, compact, nonempty, coercion-smoothness, and
   basic diffeomorphism/homeomorphism conveniences. Estimated effort: 3-5 days.
3. **One-form/cotangent facade.** Define project-local aliases and lemmas for
   one-forms as `forall x, TangentSpace I x ->L[...] K`, using `extDerivFun`
   and `Tensoriality` where possible. This avoids waiting for a full tensor
   bundle hierarchy while allowing honest statements of gradients and
   differential one-forms. Estimated effort: 1-2 weeks.
4. **Riemannian distance/path-length bridge.** Build a local API around
   `pathELength`, `riemannianEDist`, and `EMetricSpace.ofRiemannianMetric`:
   topology compatibility, compact balls where available, and sphere/manifold
   specialization lemmas. Estimated effort: about 1 week.
5. **Covariant-derivative existence and affine operations.** Fill the nearby
   partition-of-unity gap noted in the covariant-derivative file: locally
   finite sums/affine combinations of connections and existence of smooth
   connections on finite-dimensional paracompact-style manifolds. Estimated
   effort: 2-4 weeks.

## Biggest Walls

1. **Levi-Civita, curvature, and Ricci geometry.** No Levi-Civita connection,
   geodesics, Riemann curvature, Ricci tensor, scalar curvature, sectional
   curvature, or evolution identities were found. A usable core geometry stack
   is likely 3-6 months of focused Mathlib-compatible work before Ricci-flow
   statements become natural.
2. **Parabolic PDE / geometric-flow existence.** Existing Sobolev and ODE
   foundations do not include quasilinear parabolic theory, heat semigroups,
   regularity, or short-time existence for geometric flows. A serious
   short-time-existence bridge is likely 6-12+ months, depending on how much is
   stated axiomatically versus proved.
3. **3-manifold topology and sphere classification.** Fundamental group and
   homology foundations exist, but the Poincare-conjecture file is
   `proof_wanted` and no sphere homology/classification layer was found. A
   proof-bearing path to 3-sphere classification is a multi-year Mathlib-scale
   wall unless treated as an external theorem interface.
