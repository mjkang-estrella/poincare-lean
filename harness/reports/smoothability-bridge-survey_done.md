# Smoothability bridge survey


> Orchestrator note (2026-09-08): this landed copy keeps sections 1-5 and appendices K, P, E, D, N (lines 1-1498 of the worker report). The remaining evidence appendices (exact source searches, every structure of Smoothability.lean, the 5,824-entry source-mapped signature inventory, failed-probe evidence) are retained unmerged on branch `worker/smoothability-bridge-survey` at its head commit, not on main, because of their size.

Date: 2026-09-08. Base: `468b5a67fca45c9b019665ad6c368c28ff6d7afa`.
Branch: `worker/smoothability-bridge-survey`. Worktree: `/private/tmp/poincare-workers/smoothability-bridge-survey`.
Lean: `leanprover/lean4:v4.30.0-rc2`. Manifest and checked Mathlib HEAD both: `7175569c842f9164564bd76ff8b207e7b4705522`.

Result: survey complete; smoothability remains open. The repository has genuine finite-atlas preparation and conditional smooth-atlas assembly. It does not supply the intervening topological smoothing theorem. Its legacy Moise/PL records already assume sphere recognition. Mathlib supplies complexes and smooth-manifold analysis, but no located theorem constructing a PL or smooth structure on an arbitrary topological 3-manifold. There is one small new foundational A task below, with its feasibility proved in scratch Lean. There is no identified unproved A task that resolves the core Moise or PL-smoothing obstruction.

Only this report is a deliverable. No project Lean source, root import, audit, mission, ledger, or `HANDOFF.md` is modified. The task's exactly-one-report restriction takes precedence over the general handoff-edit instruction. No task is marked accepted or merged. All proposed declarations below are proposals, not landed theorems. Scratch files and build caches are not deliverables.

## 1. Repository inventory and exact boundary

### 1.1 Frozen target and the two kinds of atlas quantification

The following are the existing definitions, not new hypotheses added by this survey. Probe K prints the definitions and checks the named reductions.

```lean
-- Poincare/Statement.lean, namespace Poincare
PoincareConjectureStatement.{u} =
  (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ ThreeSphere))

-- Poincare/Global/TopologicalCompletionBridge.lean, namespace Poincare
ExistsSmoothabilitySmoothManifoldStatement.{u} =
  (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
        IsManifold (𝓡 3) ∞ M)
```

The original topology is retained. The output atlas can differ from the input atlas. Compactness supplies sigma-compactness, hence second countability through Mathlib's `ChartedSpace.secondCountable_of_sigmaCompact`. The model is Euclidean space without boundary. No full noncompact, boundary, relative, or uniqueness version of Moise is required for this frozen endpoint.

`Poincare.SmoothabilitySmoothManifoldStatement` in `Poincare/Smoothability.lean:2376` instead concludes `IsManifold (𝓡 3) ∞ M` for the supplied atlas. This stronger ambient-atlas assertion is not what Moise proves. Arbitrary compatible topological charts need not have differentiable transitions. Do not dispatch its unconditional proof as the smoothability mission. The existing implication from this stronger interface to the existential interface is valid conditional assembly, not evidence for the stronger premise.

`Poincare.poincareConjectureStatement_iff_canonical_three_sphere_statement` is defined in `Poincare/Statement.lean:48080`. `Poincare/CanonicalBridges.lean` consumes that equivalence; it does not strengthen it. Probe K checks both it and `Poincare.canonical_three_sphere_statement_iff_canonical_completion_target`.

The exact current reduction, checked in K, is:

```lean
Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence :
  Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u} →
  Poincare.UniversalHamiltonConvergenceStatement.{u} →
  Poincare.PoincareConjectureStatement.{u}
```

Both input statements remain obligations. `harness/v2/missions/hamilton-poincare.json` has these two mathematical inputs and the reserved endpoint as a third obligation node. Its recorded base is older than this survey base. The handoff sentence saying smoothability is not registered is superseded by the same handoff's later paragraph and by the actual mission file. Probe N confirms that the requested endpoint name `Poincare.universal_exists_smoothability` and the reserved `Poincare.poincare_conjecture` are absent from the imported environment. Source searches find mission references but no defining Lean declaration. No completion claim follows from importing the reductions.

### 1.2 Exhaustive source/signature appendix

The inventory appendix is deliberately exhaustive rather than a selected list of attractive theorem names. It contains:

- All 280 explicit named declarations in `Poincare/Smoothability.lean`, in source order, including definition equalities, constructors, package fields, projection theorems, and conditional assembly.
- All explicit declarations in the files whose basename contains `Smoothability`, including the newer geometric reductions.
- A conservative repository-wide superset of declarations whose declaration block mentions smoothability, smoothable structures, Moise, triangulations, PL records, or handle decompositions. This includes consumers in assembly/completion modules and the large historical proof-progress files. Body-only matches are retained rather than silently losing a dependent hypothesis.
- 5,824 public named entries across 74 imported modules, each source-verified by literal `rg` and checked by `#check @fully.qualified.name`. The source-to-name mapping and exact compiler output are included. All implicit parameters appear as binders in these checks, so the hypotheses are not inferred from filenames. There was one unrelated private coordinate-naturality false positive; it is excluded from the public inventory, not counted as missing smoothability work.
- All 45 explicit structures from `Poincare/Smoothability.lean` printed by Lean in probe S. This records generated field/projection types and constructor dependencies that a bare `#check` on the structure would hide. Anonymous typeclass instances and generated recursors are not counted as separate authored declarations.

The generator and its matching expression are included for review. This is a source-level mention inventory, not an assertion that every theorem whose proof transitively imports smoothability is a smoothability theorem. The overinclusive legacy ledger and completion entries are recognizable by their source paths. `theorem`/`lemma` entries are existing checked conditional results; `def`/`structure` entries are definitions and interfaces. A checked proposition-valued definition is not a proof that it is inhabited. Nothing in the count measures progress toward Moise.

### 1.3 What the legacy records actually contain

Most local topology/PL records in the first part of `Poincare/Smoothability.lean` contain a field

```lean
onePointRecognition : Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 3)))
```

and, where indexed by previous records, equalities identifying those records with constructors from the same recognition proof. Probe S gives every field and its actual dependencies. For example:

| Existing record | Source | Additional indices/hypotheses beyond the target manifold instances | Actual information |
| --- | --- | --- | --- |
| `Poincare.HasMoiseLocalTriangulationCharts` | `Poincare/Smoothability.lean:21` | None | One-point recognition; no triangulated chart data. |
| `Poincare.HasMoiseTriangulation` | `Poincare/Smoothability.lean` | None | One-point recognition; no geometric simplicial complex or realization map. |
| `Poincare.HasCompatiblePLStructure` | `Poincare/Smoothability.lean:484` | A `HasMoiseTriangulation` record | One-point recognition, not a PL atlas. |
| `Poincare.HasPLSmoothingExistence` | `Poincare/Smoothability.lean:746` | Triangulation, PL-structure, and compatible-PL-atlas records | Recognition and equalities to recognition-generated records; no independent smoothing construction. |
| `Poincare.SmoothabilityPackage` | `Poincare/Smoothability.lean:3253` | See all universal fields in S | Packages the preceding interfaces and the separately supplied manifold/bridge conclusions. It does not prove them. |

The remaining local-refinement, simplicial-approximation, star, subdivision, regular-neighborhood, link, Hauptvermutung, collar, obstruction-vanishing, microbundle, atlas, uniqueness, and bridge records must be read the same way through their printed fields. They cannot be used as the definitions of geometric triangulation or smoothing in a new mission.

This is not merely a suspicion about the names. Probe E checks
`Poincare.homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace` from `Poincare/TopologyExtraction.lean`. Under only a topology on `M`, its two sides are exactly recognition by the target sphere and recognition by the compactification. Universal production of even the first legacy local-chart record would therefore already solve the topological sphere-recognition problem.

Transport after recognition is real proved work. `Poincare/ProofProgress/SmoothabilityOnePointRecognition.lean` builds an atlas from an actual recognition homeomorphism and proves C∞ smoothness on that transported atlas. Its full declaration inventory appears below. `Poincare/ProofProgress/MoiseSmoothabilityTarget.lean` defines `Poincare.AdmitsSurgeryModelSmoothStructure` and `Poincare.MoiseSmoothabilityStatement`: these select a C¹ atlas. They do not provide an unconditional constructor from the bare topological hypotheses. `Poincare/Global/SmoothabilityExistenceBridge.lean` consequently retains `Poincare.C1ToCInfinityAtlasUpgrade3` as a hypothesis. Lowering C∞ regularity to C¹ is proved; raising it by constructing a new atlas is a different theorem.

### 1.4 Genuine geometric preparation and the surviving hypothesis

For this table, the common fixed-manifold assumptions are `{M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]`. Simple connectivity is generally not required by these local reductions. Exact exceptions and additional dependent binders are in the inventory.

| Module under `Poincare/Global/` | Proved content / retained input |
| --- | --- |
| `SmoothabilityFiniteTopologicalAtlasReduction.lean` | Finite subcover by actual preferred charts; transition identities and source membership. |
| `SmoothabilityFinitePrecompactTopologicalAtlasReduction.lean` | Finite smaller open domains whose closures are compact and contained in chart sources. |
| `SmoothabilityFiniteAtlasNerveReduction.lean` | Finite ordered overlapping pairs and compact transition domains. `exists_finiteAtlasNerveReduction3` constructs this package with no smoothing assumption. This is an overlap graph with transition data, not a triangulation of `M`. |
| `SmoothabilityFiniteLocalAffineTransitionModels.lean` | Finite patch extraction from supplied local affine corrected-transition models. Affineness is assumed. |
| `SmoothabilityLocalSmoothTransitionGerms.lean` | Finite local smooth models and smooth extensions assembled by partitions of unity, assuming local smooth agreement of corrected transitions. |
| `SmoothabilityFiniteSmoothTransitionExtension.lean` and `SmoothabilityFiniteTransitionSmoothingBoundary.lean` | Build an actual smooth atlas from compatible supplied corrected-transition extensions. Neither produces the required coordinate corrections from topological charts. |
| `SmoothabilitySimultaneousLocalConjugacy.lean` | One topological coordinate correction per finite-atlas vertex; every corrected transition agrees locally with a smooth local diffeomorphism on its compact domain. This input implies an actual C∞ atlas. Existence of those simultaneous corrections is open. |
| `SmoothabilityPLCompatibleAffineConjugacy.lean` | Locally affine-equivalence corrected transitions imply the preceding smooth-germ input. This is a sufficient special case, not general PL smoothing. |
| `SmoothabilityAffineGermInvertibilityReduction.lean` | Derives local affine invertibility using the actual open overlap and its topological transition, eliminating a separate invertibility requirement once local affineness has been supplied. |
| `SmoothabilityRawAffineNerveIdentityConjugacy.lean` | Identity corrections suffice for already locally affine raw transitions. |
| `SmoothabilityFiniteTetrahedralStarReduction.lean` | Finite tetrahedral presentations plus `StarwiseTangentCompatible3` give locally affine transition germs. The extra condition says the linear parts on every pair of incident pieces agree. Ordinary PL continuity only equates values on common faces. For example, the piecewise linear homeomorphism of a line with slopes 1 and 2 has unequal slopes at its breakpoint; taking its product with two identity coordinates gives the same problem in dimension 3. The record also is not a global face-to-face triangulation of `M`. |
| `SmoothabilityProofBearingAtlasUpgrade.lean` | `CInfinityLocalTransitionAtlasData3` is equivalent to existence of a selected smooth atlas. Recognition-based inputs also give such data, conditionally. |

The raw locally affine route can impose an affine-atlas type of condition substantially stronger than ordinary smoothability. No claim is made that it follows from Moise. In particular, the tetrahedral derivative-matching field cannot be obtained by simply renaming the usual PL face-compatibility condition. Classify a universal producer for this special affine input as C until its mathematical feasibility is settled; do not dispatch it as an easy B smoothing lemma.

## 2. Pinned Mathlib inventory

These findings are for the checked manifest revision, not current upstream Mathlib. Positive names below were located in source and their relevant signatures checked in K or D. Negative statements mean no matching theorem or geometric definition was located by the recorded searches, not a formal proof that no equivalent mathematical consequence could be derived under some other name.

| Topic | Actual source hits | What is present / absent |
| --- | --- | --- |
| Abstract complexes | `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean` | `PreAbstractSimplicialComplex`, `AbstractSimplicialComplex`: finite nonempty faces with downward closure; the latter includes singletons. Present definitions; no manifold triangulation existence theorem. |
| Geometric complexes | `Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean`; `AffineIndependentUnion.lean` in the same directory | `Geometry.SimplicialComplex`, `.space`, `.convexHull_inter_convexHull`, `.down_closed`. Faces have affine-independent vertices and convex-hull intersection compatibility. Useful actual geometric foundations. No local manifold link/smoothing theorem was found. |
| Subdivision | `Mathlib/AlgebraicTopology/SimplicialSet/Subdivision.lean` | `SSet.sd`, `SSet.ex`, `SSet.sdExAdjunction` are categorical subdivision/adjunction definitions. They are not a relative PL approximation or mesh-control theorem for topological manifold charts. Do not report all subdivision theory absent. |
| CW complexes | `Mathlib/Topology/CWComplex/Classical/{Basic,Subcomplex,Finite,Graph}.lean`; `Mathlib/Topology/CWComplex/Abstract/Basic.lean` | Classical and categorical CW foundations exist. K checks the actual classical name `Topology.CWComplex`, whose argument is a subset of a topological space. An assumed CW structure is not a triangulation theorem. |
| Triangulations of manifolds | Broad `triangulat` search and focused searches in the evidence appendix | No construction found. Triangulated categories and a Catalan-number comment about polygon triangulations are unrelated hits. |
| PL structures/maps/manifolds | Searches for piecewise-linear, PL-structure, PL-manifold and PL-homeomorphism terminology | No relevant geometric theory found. Generic piecewise functions and affine maps do not constitute PL manifold structures. |
| Collar theorems | `Mathlib/Geometry/Manifold/Bordism.lean:22` | A prose mention describing future bordism transitivity. No collar theorem or collar structure found. |
| Schoenflies / local flatness | Searches for `schoenflies` and `locallyFlat` | No hits. Smooth or locally flat/PL hypotheses cannot be dropped in a future sphere-embedding theorem. |
| Handles / isotopy extension | Searches for handle decomposition, handle attachment, isotopy extension | No relevant hits. No genuine handle decomposition was located in the project's Lean tree either. Surgery traces and finite component sets are different objects. |
| Smoothing / microbundles | Searches for smoothability, smoothing theorem and microbundle terminology | No general PL-to-smooth or C¹-to-C∞ atlas-existence theorem found. Local differentiability and smooth partitions are present. |
| Whitney embedding | `Mathlib/Geometry/Manifold/WhitneyEmbedding.lean` | `exists_embedding_euclidean_of_compact` gives a smooth closed embedding into some finite-dimensional Euclidean space and injective differential, with `[IsManifold I ∞ M]` already assumed. `SmoothBumpCovering.exists_immersion_euclidean` likewise starts smooth. Neither creates smoothability; no optimal ambient-dimension bound is claimed. |
| Poincaré statements | `Mathlib/Geometry/Manifold/PoincareConjecture.lean` | The topological/smooth sphere names in the old gap report occur under `proof_wanted`. Probe N gets unknown-constant errors, not proofs. |

Compact convex hulls of finite vertex sets are already available as `Set.Finite.isCompact_convexHull` in `Mathlib/Analysis/Convex/Topology.lean:339`. Finite unions of compact sets are available as `Set.Finite.isCompact_biUnion` in `Mathlib/Topology/Compactness/Compact.lean:459`. These suffice for the small A task in section 5. They do not supply any triangulation homeomorphism.

## 3. Literature routes, lemma boundaries, and effort

A means the specified item can be formalized using landed definitions/theorems without a new deep geometric theorem. B means it needs absent theory. C means the exact reduction or feasibility is unresolved in this survey. Effort estimates are my rough expert-person time estimates, not measurements or delivery promises. They include proof development and API work; dependency estimates overlap and should not be added mechanically.

### 3.1 Shared preparation and the classical Moise/Bing route

Moise's paper is *Affine Structures in 3-Manifolds: V. The Triangulation Theorem and Hauptvermutung*, Annals 56 (1952), 96–114. Bing's paper is *An Alternative Proof that 3-Manifolds Can be Triangulated*, Annals 69 (1959), 37–65. Their publisher pages/PDF routes were consulted, but exposed no full article text to this run. I therefore do not invent their internal lemma numbers or claim a page-by-page reconstruction. Hamilton explicitly identifies both as predecessors. The following classical decomposition is a proposed proof-development outline; exact original-proof matching is C pending primary-text inspection. [Moise publisher record](https://www.jstor.org/stable/1969769), [Bing publisher record](https://www.jstor.org/stable/1970092).

| Lemma-shaped step | Class and evidence | Rough effort |
| --- | --- | --- |
| Obtain finite precompact coordinate neighborhoods and compact overlap domains. | A, already landed by the finite-atlas modules in section 1. No new task. | 0 new proof work. |
| Prove compactness of the support of a given finite geometric complex. | A, scratch proof succeeds in P. This is preparation for a real triangulation interface, not existence of one. | Hours to 1 day for a reviewed module. |
| Define geometric subdivisions, stars, links, PL maps, common refinements, and relative compatibility. | B. Complexes exist; the needed PL manifold API does not. | 2–6 person-months. |
| Replace suitably controlled local surface/2-complex embeddings by polyhedral ones, with relative control on previously treated sets. | B for the geometry; C for the exact Moise-versus-Bing lemma package until their full proofs are read. Needs taming/approximation, local flatness, and relative ambient control. | 6–18 person-months, high uncertainty. |
| Fit chartwise polyhedral decompositions together, keeping earlier overlaps fixed. | B. Independent triangulations or independent smoothing of individual transition maps do not ensure a single coherent atlas. | 3–9 person-months after the preceding API. |
| Fill the resulting complementary regions by compatible tetrahedra and verify link conditions / realization homeomorphism. | B. Needs controlled ball recognition, PL gluing, subdivision and local finiteness results. | 3–9 person-months after those tools. |
| Pass the controlled locally finite construction to a global triangulation; in the compact case reduce to finite data. | B overall; elementary finite-cover bookkeeping is A and largely landed. No locally finite geometric triangulation-to-finite theorem was located. | 1–3 person-months after geometry. |
| Prove uniqueness/Hauptvermutung. | B; not required by the frozen existential smoothability endpoint. | Do not schedule for this mission. |

Bing's original abstract, reproduced with the bibliography, identifies approximation of topologically embedded 2-complexes by polyhedra as the central input. That provides a useful candidate boundary, but this report does not silently strengthen approximation of an embedded set into a relative ambient-isotopy theorem. The exact extra control needed for assembly must be read in the original paper before freezing tasks. [Bing's abstract, bibliography entry 47](https://celebratio.org/Bing_RH/article/49/).

### 3.2 Hamilton 1976, inspected proof

This is A. J. S. Hamilton, not the Ricci-flow Hamilton endpoint in the repository. The paper proves triangulation by three-dimensional handle straightening and chartwise induction. Its short length hides major prerequisites. [Hamilton, pp. 63–70](https://www.maths.ed.ac.uk/~v1ranick/papers/hamiltontri.pdf).

| Paper boundary | Class / missing material | Rough effort |
| --- | --- | --- |
| Lemma 1: PL immersions of suitable open low-dimensional PL manifolds. | B: PL immersion theory. | 3–6 months. |
| Lemma 2: compact PL neighborhoods controlling a simply connected end. | B: end theory and PL neighborhoods. | 3–6 months. |
| Lemma 3: relative PL rigidity for sufficiently large irreducible manifolds. | B: Waldhausen/Scott theory. | 12+ months. |
| Theorem 1: straighten handles in a Euclidean chart, relative to boundary/outside support. | B: preceding lemmas, Alexander/Brown Schoenflies, torus lifting, Dehn and decomposition tools. | 6–12 months after prerequisites. |
| Theorem 2.1: inductively reconcile local PL structures. | B: relative handle straightening and PL gluing; existing finite atlas preparation is A. | 1–3 months after prerequisites. |

The chart-local irreducibility restriction matters. A generic simply connected manifold is not supplied as a ball. Neither universal covering theory nor the existing chart overlap graph gives the needed PL rigidity. My assessment: this route has the clearest published modular outline among the inspected texts, but is not the cheapest route from the current formal library.

### 3.3 Hatcher's notes are consumers of category equivalence

Hatcher's *Notes on Basic 3-Manifold Topology* begins in the C∞ category. Its Alexander theorem and prime decomposition arguments use smooth embeddings, Morse theory and isotopy/ball-attachment arguments. They do not prove that the initial topological manifold is smooth. His separate *Classification of 3-Manifolds — A Brief Overview* explicitly starts by invoking the topological/PL/smooth correspondence. These texts are useful consumers and guides to further topology, not a shortcut around the missing category-conversion proof. [Notes, chapter 1](https://pi.math.cornell.edu/~hatcher/3M/3M.pdf), [overview, first page](https://pi.math.cornell.edu/~hatcher/Papers/3Msurvey.pdf).

An attempted plan through these notes would require B tasks for relative isotopy extension, Morse normal forms, smooth/PL Schoenflies and ball gluing, with months of work for each major layer. It would still need the initial smoothing/triangulation step. Unrestricted topological sphere embeddings cannot replace the smooth/local-flat hypotheses. The notes' theorem statements must be read with their ambient category assumption.

### 3.4 PL 3-manifold to smooth structure is a separate construction

Whitehead's *On C¹-complexes* addresses compatible triangulations of already differentiable manifolds. That direction cannot be reversed merely by naming the theorem. [Whitehead's paper, collected-work publisher summary](https://www.sciencedirect.com/science/chapter/edited-volume/pii/B978008009870850021X).

Hirsch's smoothing-obstruction paper provides a precise alternative decomposition: relative product smoothing, an obstruction to extending a smoothing across a simplex, and compatibility under changes on lower skeleta. It treats manifold smoothing separately from smoothing maps, and connects the obstructions to PL/orthogonal bundle data. These are substantial theorems, not consequences of finite unions or affine-independent vertices. [Hirsch, sections 2–5](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/hirscho.pdf).

| Lemma-shaped step | Class and missing theory | Rough effort |
| --- | --- | --- |
| Turn a geometric triangulation of a 3-manifold into a combinatorial/PL manifold with the required link charts. | B: geometric links, low-dimensional sphere/ball recognition, PL chart changes. The bare proposed triangulation interface does not assert these. | 3–6 person-months. |
| Define partial smoothings near subcomplexes and their relative agreement. | B: regular neighborhoods, PL maps and piecewise differentiable structures. | 2–4 person-months. |
| Extend a smoothing across successive simplex neighborhoods. | B: relative product theorem and extension/obstruction theory, or a direct low-dimensional smoothing proof. | 6–12 person-months. |
| Show the dimension-three obstruction groups/extension problems vanish. | B; C for the cheapest exact low-dimensional proof and indexing choices. Do not assert a particular obstruction-group formula without fixing its definition and checking the source. | 3–9 person-months, possibly overlapping preceding work. |
| Produce actual smooth transition functions and retain simultaneous agreement. | B until the geometric smoothing theorem is proved. Once its output matches the finite local-conjugacy record, the repository's assembly is A and already proved. | Weeks for the adapter after matching data exists. |
| Upgrade a selected C¹ atlas to a selected C∞ atlas, if the chosen route stops at C¹. | B: relative approximation and preservation of invertible coordinate changes. Existing regularity-lowering lemmas do not suffice. A route constructing C∞ directly avoids this separate node. | 3–9 person-months. |
| Prove uniqueness up to diffeomorphism. | B and unnecessary for existence. | Exclude from immediate scope. |

Munkres' work on smoothing maps and imposing structures and Hirsch–Mazur's *Smoothings of Piecewise Linear Manifolds* are the relevant separate smoothing literature. The book's stated approach is homotopy obstruction theory; importing that entire route would require PL microbundles, stable bundle comparisons and obstruction theory not found here. The exact low-dimensional specialization still needs a primary-text lemma audit before a worker contract is frozen. [Hirsch–Mazur publisher description](https://www.jstor.org/stable/j.ctt1bd6m0d), [Munkres, imposing differentiable structures](https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-8/issue-3/Obstructions-to-imposing-differentiable-structures/10.1215/ijm/1256059559.full).

My effort assessment for either complete route is multi-year library development at the present boundary, with substantial uncertainty. No core existence step is evidenced as an A-sized proof job. This is an estimate of missing theory, not a claim that formalizing Moise is mathematically impossible.

## 4. Alternatives preserving the frozen statement

The grounded-topology route is a valid conditional alternative to the global Hamilton/C∞ consumer. Probe K checks:

```lean
Poincare.poincare_statement_of_groundedTopologySources_and_covering :
  Poincare.GroundedTopologyUniversalSourceStatement.{u} →
  Poincare.GroundedTopologyThreeSphereCoveringStatement.{u} →
  Poincare.PoincareConjectureStatement.{u}
```

It is not a route from currently reachable bare hypotheses. A `GroundedTopologyPresentation` selects an atlas and a `GroundedTopologySource`. The source's trace contains `IsManifold ThreeManifoldModelWithCorners 1 M`, on that selected atlas. Probe P proves, in scratch Lean, that universal source existence implies `MoiseSmoothabilityStatement`. This establishes the overlap exactly at C¹, not C∞. The first attempt failed because the ambient atlas remained installed; the corrected proof installs `p.chartedSpace` before projecting the trace field. That actual failure and repair are retained below.

Consequently, this route could avoid a *separate C∞ upgrade* if its own analytic/surgery/source requirements were proved with their frozen C¹ assumptions. It still needs existence of a differentiable atlas, together with the much larger surgery and trace payload. It cannot obtain these from a finite partition of the original point set. Source existence and covering construction are both still unproved mission nodes.

The other possible route is genuinely topological recognition. A covering `ThreeSphere → M`, together with the current compactness, simple connectivity and local path connectivity, is already consumed by `Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected`. The conclusion is a homeomorphism; its symmetry has the required target orientation. Building this covering without a source is the missing geometric content, not an available consequence of generic covering theory. A simply connected space's identity covering is not a covering by `ThreeSphere`.

Likewise, a homeomorphism with the one-point compactification would directly imply the frozen statement by the verified model equivalence in section 1. The legacy Moise local-chart record already asks for precisely that information. Using it as an unconditional input to prove smoothability and then Poincaré would assume the required recognition rather than derive it.

No alternative proof from only currently reachable hypotheses was found. A topological sphere-recognition project could replace the smooth route while retaining exactly the frozen target, but it would be a new Poincaré-level proof program. Homotopy or homology equivalence alone is not the requested homeomorphism, and no such replacement is proposed here.

## 5. Numbered plan and registered-obligation proposals

Shared dispatch contract: base `468b5a67fca45c9b019665ad6c368c28ff6d7afa`; one new module per task, with a fresh base frozen if prerequisites change. All existing Lean files, the six frozen contract files, `Poincare.lean`, audits, missions and ledgers are forbidden to workers. The orchestrator owns registration and acceptance. No task is dispatched by this report. Standard gate means direct Lean, a no-match forbidden-token scan, `git diff --check`, and an independent exact-signature/axiom probe. Root builds/audits belong to integration and were not run for this prose survey.

### 5.1 Task 1: finite geometric-complex support compactness [A]

Module: `Poincare/Topology/FiniteGeometricComplexCompactness.lean` proposed new file.
Namespace: `Poincare.FiniteGeometricComplexCompactness`.
Imports: `Mathlib.Analysis.Convex.SimplicialComplex.Basic`, `Mathlib.Analysis.Convex.Topology`.

Objective: prove compactness of the actual geometric realization of a finite complex. Use the existing union-of-convex-hulls realization, not a new quotient or an assumed compactness field. This is small foundation work for a genuine triangulation interface. It does not reduce the open topological existence theorem.

Proposed theorem signature:

```lean
namespace Poincare.FiniteGeometricComplexCompactness
-- Proposed new name; the exact proposition and a proof were checked in P.
theorem isCompact_space_of_finite_faces
    (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hf : K.faces.Finite) : IsCompact K.space
end Poincare.FiniteGeometricComplexCompactness
```

Proof plan: apply finite compact-union closure to the face set; each face's convex hull is compact by its finite vertex set. Probe P verifies the proof term, with no placeholder. No equivalent support-compactness theorem was found in the pinned simplicial-complex modules. This task should be skipped if a new base already supplies it.

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Topology/FiniteGeometricComplexCompactness.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Topology/FiniteGeometricComplexCompactness.lean
git diff --check
```

Exact stop condition: the displayed theorem compiles using the existing `Geometry.SimplicialComplex.space`, its axiom check has only standard logical dependencies, and no other file is changed. Do not turn this task into triangulation existence, a recognition certificate, or a compactness assumption. Estimate: hours to one day. There are no further justified new A tasks on the core Moise/smoothing path identified by this survey; finite atlas selection and post-smoothing assembly are already landed.

### 5.2 Registration proposal 1: selected finite-nerve smoothing

Proposed module: `Poincare/Global/SelectedFiniteNerveSmoothingStatements.lean`.
Proposed namespace: `Poincare.SelectedFiniteNerveSmoothing`.
Imports: `Poincare.Global.SmoothabilitySimultaneousLocalConjugacy`.
Suggested mission node ID: `selected-finite-nerve-smoothing`.

Objective: pin exactly the simultaneous local theorem which can feed the existing consumer. It is sufficient to produce one suitable finite reduction, rather than solve every reduction of the same manifold. This is smaller in quantifier scope than the existing universal-over-reductions interface. It is not claimed to be mathematically weaker than smoothability, nor is a reverse implication proved.

The following exact proposition was elaborated as `SmoothabilitySurveyProposal.SelectedFiniteNerveSmoothingStatement` in P. Moving it to the proposed namespace would be an explicit later registration change.

```lean
open Poincare.SmoothabilityFiniteAtlasNerveReduction
open Poincare.SmoothabilitySimultaneousLocalConjugacy

def SelectedFiniteNerveSmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ r : FiniteAtlasNerveReduction3 M,
        Nonempty (FiniteNerveSimultaneousLocalConjugacySmoothing3 r)
```

A record contains one open partial homeomorphism correction for each vertex, source containment for the entire compact coordinate image, and local smooth-diffeomorphism agreement on each compact overlap domain. The actual fields and equations are printed in K. They do not assume a smooth atlas or a sphere homeomorphism. Corrections must be simultaneous; a separate smoothing for each edge is insufficient.

P also checks the proposed edge:

```lean
SelectedFiniteNerveSmoothingStatement.{u} →
  Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u}
```

The proof uses the landed per-record local-transition-atlas consumer and the landed equivalence between that data and an existential smooth atlas. Existence of the new node is B; only its conditional assembly edge is already verified in scratch. The node would remain open. Do not label the definition or this adapter as a discharged smoothing obligation.

Gate for a later registration implementation:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/SelectedFiniteNerveSmoothingStatements.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/SelectedFiniteNerveSmoothingStatements.lean
git diff --check
```

Exact stop condition: the proposition has the displayed universe/atlas quantifiers, the conditional edge to the unchanged existing target is checked, and independent statement review confirms the local correction fields. Registration must remain an obligation. Stop if the producer demands locally affine transitions or tangent equality not supplied by the intended literature theorem; do not strengthen the planned provider silently. This registration alone is administrative and should not be advertised as theorem-bearing progress.

### 5.3 Registration proposal 2: an actual finite triangulation interface

Proposed module: `Poincare/Topology/FiniteTriangulationStatements.lean`.
Proposed namespace: `Poincare.FiniteTriangulation`.
Imports: `Poincare.Statement`, `Mathlib.Analysis.Convex.SimplicialComplex.Basic`.
Suggested node ID: `finite-triangulation-existence`.

Objective: separate genuine triangulation existence from PL smoothing using existing geometric definitions. P checks these bodies under the scratch proposal namespace:

```lean
def FiniteTriangulationData3 (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ n : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
    K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 4) ∧ Nonempty (M ≃ₜ K.space)

def FiniteTriangulationExistence3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteTriangulationData3 M
```

The complex can live in any finite-dimensional Euclidean ambient space. Requiring the whole closed 3-manifold to embed as a complex in ℝ³ would be wrong. The face cardinality bound asserts dimension at most 3, not smoothness. The topology on `K.space` is the ambient subtype topology, and the homeomorphism preserves the given topology on `M`. Faces already have affine-independent vertices and proper convex-hull intersections through the Mathlib structure. Finiteness is actual finiteness of the face set.

This is the smallest standalone triangulation-existence interface I would pin now without inventing a PL manifold API. It deliberately does not assert combinatorial links, PL smoothability, a compatible smooth atlas, uniqueness, or sphere recognition. From it to the selected finite-nerve smoothing node, genuine link/PL recognition and the smoothing construction are still B. There is no checked implication from this interface alone to the current smoothability obligation. Do not insert such a checked edge into a mission graph.

Gate for a later statement module:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Topology/FiniteTriangulationStatements.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Topology/FiniteTriangulationStatements.lean
git diff --check
```

Exact stop condition: both proposition bodies elaborate at the displayed universe, independent review accepts the support topology and dimension bound, and the node stays open with no asserted smoothing edge. Stop before registering a consumer if its required link or relative smoothing condition has no precise definition. The next mathematical task would be the missing PL/link interface design and primary-literature audit, not unconditional construction of a legacy Moise record.

### 5.4 Reproduction and handoff

Exact first independent action after reading this report: extract the `smoothability_plan.lean` source in appendix P to `/tmp/smoothability_plan.lean`, then run:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_plan.lean
```

If the geometric-complex import cache is absent, first run the focused build command recorded in the evidence appendix. Successful elaboration verifies the proposed statements and three scratch implications/results; it does not prove either existence proposal. Review the resisting simultaneous-correction type in K before choosing any mathematical worker task.

All evidence below is from this run. No signature or proof conclusion is taken on trust from a historical ledger. Successful inventory checks use existing compiled imports at the recorded checkout; this survey did not rebuild the entire Poincaré project or rerun integration audits. Only three selected consumer axiom closures were inspected, not every legacy declaration's dependency closure.

## Evidence appendix

These appendices are part of sections 1–5. The long inventory is kept in collapsible blocks so the findings and proposed tasks remain readable. There are no omitted hypotheses in the inventory by editorial summarization; the printed Lean types are the authority. Proof terms may be elided by Lean pretty printing.


### Provenance and reading scope


```sh
git status --short --branch
```


```text
## worker/smoothability-bridge-survey
```


Exit `0`.


```sh
git rev-parse HEAD
```


```text
468b5a67fca45c9b019665ad6c368c28ff6d7afa
```


Exit `0`.


```sh
git worktree list --porcelain
```


```text
worktree /Users/mjkang/Develop/poincare
HEAD 468b5a67fca45c9b019665ad6c368c28ff6d7afa
branch refs/heads/main

worktree /private/tmp/poincare-workers/hamilton-front-decomposition
HEAD 468b5a67fca45c9b019665ad6c368c28ff6d7afa
branch refs/heads/worker/hamilton-front-decomposition

worktree /private/tmp/poincare-workers/smoothability-bridge-survey
HEAD 468b5a67fca45c9b019665ad6c368c28ff6d7afa
branch refs/heads/worker/smoothability-bridge-survey

worktree /Users/mjkang/.codex/worktrees/focused-job-gates/poincare
HEAD a87c80a6ff90952ad633b894ef6fc467e60c8ee6
branch refs/heads/codex/focused-job-gates

worktree /Users/mjkang/.codex/worktrees/formalization-until-6/poincare
HEAD 64c9f999c9c699cb52e87ea36fad294d43b774d4
branch refs/heads/codex/formalization-until-6

worktree /Users/mjkang/.codex/worktrees/frozen-statement-contracts/poincare
HEAD b6fd0aa7d6865696f69b1c03c82d507fd4b5f5d7
branch refs/heads/codex/frozen-statement-contracts

worktree /Users/mjkang/.codex/worktrees/grounded-topology-consumer/poincare
HEAD ed7052816a46ee5a2328364b421d411edd3f401f
branch refs/heads/codex/grounded-topology-consumer

worktree /Users/mjkang/.codex/worktrees/harness-throughput/poincare
HEAD 3d8dc9f20a5b943d1fc55019ad968713947ca137
branch refs/heads/codex/harness-throughput

worktree /Users/mjkang/.codex/worktrees/poincare-interrupted-evidence
HEAD 81cde04465ad1a0e6144c0d219e62d4cfd7ed7d3
branch refs/heads/codex/allow-repeated-interrupted-task-block

worktree /Users/mjkang/.codex/worktrees/proof-workflow-improvements/poincare
HEAD 5d408763930e07ab9237c5c889056064bbe398ec
branch refs/heads/codex/proof-workflow-improvements

worktree /Users/mjkang/.codex/worktrees/theorem-dependency-registry/poincare
HEAD 64351986f66e9654ea233d0eab90acd4ae57df4b
branch refs/heads/codex/theorem-dependency-registry
```


Exit `0`.


```sh
git -C .lake/packages/mathlib rev-parse HEAD
```


```text
7175569c842f9164564bd76ff8b207e7b4705522
```


Exit `0`.


The status above was captured before creating the report. Required context inspected: `HANDOFF.md` top section first; `README.md`; `docs/PROJECT_MAP.md`; `AGENTS.md`; `harness/tasks/smoothability-bridge-survey.md`; the task-named Lean files and their direct imports; both mission JSON files; `harness/reports/mathlib_gaps.md` section 6; and `harness/reports/parametrization-plan-3.md`. Large legacy files were traversed by source inventory and their relevant definitions were read/printed, rather than trusting prose descriptions.


### Focused cache preparation

The first K and P attempts failed because the geometric-complex olean was absent. No source was changed to work around this. These were focused Mathlib builds, not full Poincaré builds, and did not overlap each other.


```sh
LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.Convex.SimplicialComplex.Basic Mathlib.Analysis.Convex.Topology Mathlib.Geometry.Manifold.WhitneyEmbedding Mathlib.Topology.CWComplex.Classical.Basic
```


```text
✔ [1260/1263] Built Mathlib.Order.UpperLower.Relative (831ms)
✔ [1262/1288] Built Mathlib.AlgebraicTopology.SimplicialComplex.Basic (1.2s)
✔ [1287/1293] Built Mathlib.Analysis.Convex.SimplicialComplex.Basic (1.2s)
✔ [2693/2694] Built Mathlib.Topology.CWComplex.Classical.Basic (3.1s)
✔ [2694/2694] Built Mathlib.Geometry.Manifold.WhitneyEmbedding (2.7s)
Build completed successfully (2694 jobs).
```


Exit `0`.


```sh
LEAN_NUM_THREADS=1 lake build Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
```


```text
✔ [567/628] Built Mathlib.AlgebraicTopology.SimplexCategory.Defs (1.3s)
✔ [805/810] Built Mathlib.CategoryTheory.Limits.Opposites (3.2s)
✔ [806/820] Built Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks (3.3s)
✔ [814/820] Built Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks (1.5s)
✔ [816/820] Built Mathlib.CategoryTheory.MorphismProperty.Composition (1.1s)
✔ [817/820] Built Mathlib.CategoryTheory.Limits.Constructions.EpiMono (884ms)
✔ [818/822] Built Mathlib.CategoryTheory.MorphismProperty.Concrete (940ms)
✔ [819/825] Built Mathlib.CategoryTheory.ConcreteCategory.EpiMono (892ms)
✔ [821/825] Built Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers (1.6s)
✔ [822/825] Built Mathlib.CategoryTheory.EffectiveEpi.Basic (1.0s)
✔ [823/826] Built Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs (1.2s)
✔ [824/882] Built Mathlib.CategoryTheory.Limits.Shapes.RegularMono (1.6s)
✔ [879/886] Built Mathlib.CategoryTheory.FintypeCat (1.3s)
✔ [882/886] Built Mathlib.Order.Category.FinPartOrd (1.0s)
✔ [884/886] Built Mathlib.Order.Category.LinOrd (1.1s)
✔ [885/1051] Built Mathlib.Order.Category.NonemptyFinLinOrd (1.3s)
✔ [1048/1051] Built Mathlib.AlgebraicTopology.SimplexCategory.Basic (1.0s)
✔ [1049/1051] Built Mathlib.CategoryTheory.Adjunction.Reflective (1.0s)
✔ [1050/1056] Built Mathlib.AlgebraicTopology.SimplexCategory.Rev (1.0s)
✔ [1053/1056] Built Mathlib.CategoryTheory.Limits.Shapes.Equivalence (781ms)
✔ [1054/1057] Built Mathlib.CategoryTheory.Functor.KanExtension.Basic (3.1s)
✔ [1055/1060] Built Mathlib.CategoryTheory.Functor.KanExtension.Pointwise (2.0s)
✔ [1056/1064] Built Mathlib.CategoryTheory.Category.Cat.AsSmall (774ms)
✔ [1057/1066] Built Mathlib.CategoryTheory.Elements (2.5s)
✔ [1058/1066] Built Mathlib.CategoryTheory.Grothendieck (3.0s)
✔ [1059/1066] Built Mathlib.CategoryTheory.Comma.StructuredArrow.Functor (1.5s)
✔ [1060/1066] Built Mathlib.CategoryTheory.Limits.Shapes.Grothendieck (1.7s)
✔ [1061/1067] Built Mathlib.CategoryTheory.Functor.KanExtension.Adjunction (1.8s)
✔ [1062/1073] Built Mathlib.AlgebraicTopology.SimplicialObject.Basic (3.3s)
✔ [1063/1073] Built Mathlib.CategoryTheory.Subfunctor.Basic (1.2s)
✔ [1064/1073] Built Mathlib.AlgebraicTopology.SimplicialSet.Basic (1.3s)
✔ [1065/1073] Built Mathlib.AlgebraicTopology.SimplicialObject.Op (1.0s)
✔ [1066/1074] Built Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono (872ms)
✔ [1067/1076] Built Mathlib.AlgebraicTopology.SimplicialSet.Op (1.0s)
✔ [1068/1076] Built Mathlib.CategoryTheory.Subfunctor.Image (1.3s)
✔ [1069/1076] Built Mathlib.CategoryTheory.Subfunctor.OfSection (885ms)
✔ [1070/1076] Built Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex (1.8s)
✔ [1071/1077] Built Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp (888ms)
✔ [1072/1077] Built Mathlib.AlgebraicTopology.SimplicialSet.Degenerate (1.3s)
✔ [1073/1082] Built Mathlib.AlgebraicTopology.SimplicialSet.Simplices (1.0s)
✔ [1075/1082] Built Mathlib.AlgebraicTopology.SimplicialSet.Dimension (1.2s)
✔ [1076/1082] Built Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices (1.2s)
✔ [1081/1084] Built Mathlib.AlgebraicTopology.SimplicialSet.Finite (1.1s)
✔ [1082/1084] Built Mathlib.CategoryTheory.IsConnected (1.1s)
✔ [1083/1095] Built Mathlib.CategoryTheory.Limits.Types.Products (1.2s)
✔ [1087/1095] Built Mathlib.CategoryTheory.Limits.Final (3.1s)
✔ [1089/1095] Built Mathlib.CategoryTheory.ComposableArrows.Basic (5.3s)
✔ [1090/1098] Built Mathlib.AlgebraicTopology.SimplexCategory.Truncated (1.4s)
✔ [1091/1099] Built Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated (1.3s)
✔ [1093/1101] Built Mathlib.AlgebraicTopology.SimplicialSet.CompStruct (1.4s)
✔ [1095/1101] Built Mathlib.Order.Fin.SuccAboveOrderIso (777ms)
✔ [1096/1102] Built Mathlib.AlgebraicTopology.SimplicialSet.Nerve (1.5s)
✔ [1098/1102] Built Mathlib.Order.Fin.Finset (809ms)
✔ [1099/1102] Built Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate (1.1s)
✔ [1100/1102] Built Mathlib.CategoryTheory.Comma.Presheaf.Basic (2.4s)
✔ [1101/1108] Built Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex (2.7s)
✔ [1104/1110] Built Mathlib.CategoryTheory.Limits.Comma (1.5s)
✔ [1105/1110] Built Mathlib.CategoryTheory.Adjunction.Comma (1.0s)
✔ [1106/1110] Built Mathlib.Order.NonemptyFiniteChains (915ms)
✔ [1107/1110] Built Mathlib.CategoryTheory.Limits.ConeCategory (1.8s)
✔ [1108/1110] Built Mathlib.CategoryTheory.Limits.Over (1.1s)
✔ [1109/1110] Built Mathlib.CategoryTheory.Limits.Presheaf (3.8s)
✔ [1110/1110] Built Mathlib.AlgebraicTopology.SimplicialSet.Subdivision (984ms)
Build completed successfully (1110 jobs).
```


Exit `0`.


### K. Important repository and Mathlib definitions/signatures



Command, run from the survey worktree:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_key.lean
```


Actual Lean exit code: `0`. Source and complete actual output follow.

<details>
<summary>Probe source</summary>


```lean
import Poincare.Global.HamiltonPoincareReduction
import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Poincare.Global.SmoothabilityFiniteTetrahedralStarReduction
import Poincare.ProofProgress.GroundedTopologyAssembly
import Poincare.CanonicalBridges
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.CWComplex.Classical.Basic
set_option autoImplicit false
set_option pp.universes true
set_option format.width 110
open scoped Manifold ContDiff
#print Poincare.ExistsSmoothabilitySmoothManifoldStatement
#print Poincare.SmoothabilitySmoothManifoldStatement
#print Poincare.PoincareConjectureStatement
#check @Poincare.poincareConjectureStatement_iff_canonical_three_sphere_statement
#check @Poincare.canonical_three_sphere_statement_iff_canonical_completion_target
#check @Poincare.poincareConjecture_of_universalHamiltonConvergence
#check @Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence
#print Poincare.HasMoiseLocalTriangulationCharts
#print Poincare.HasMoiseTriangulation
#print Poincare.HasCompatiblePLStructure
#print Poincare.HasPLSmoothingExistence
#print Poincare.AdmitsSurgeryModelSmoothStructure
#print Poincare.MoiseSmoothabilityStatement
#print Poincare.C1ToCInfinityAtlasUpgrade3
#print Poincare.GroundedTopologyUniversalSourceStatement
#print Poincare.GroundedTopologyThreeSphereCoveringStatement
#check @Poincare.ExtinctionSurgeryTraceRealizationSource.smooth
#check @Poincare.poincare_statement_of_groundedTopologySources_and_covering
#check @Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected
#check @Poincare.SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
#check @Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.exists_finitePrecompactTopologicalChartAtAtlas3
#check @Poincare.nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas
#print Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3
#print Poincare.SmoothabilitySimultaneousLocalConjugacy.CorrectedTransitionsLocallySmoothlyConjugateOnCompact3
#print Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3
#print Poincare.SmoothabilityFiniteTetrahedralStarReduction.StarwiseTangentCompatible3
#print PreAbstractSimplicialComplex
#print AbstractSimplicialComplex
#print Geometry.SimplicialComplex
#check @Geometry.SimplicialComplex.space
#check @Geometry.SimplicialComplex.convexHull_inter_convexHull
#check @Geometry.SimplicialComplex.down_closed
#check @Set.Finite.isCompact_convexHull
#check @exists_embedding_euclidean_of_compact
#check @SmoothBumpCovering.exists_immersion_euclidean
#check @ChartedSpace.secondCountable_of_sigmaCompact
#check @Topology.CWComplex
```


</details>

<details>
<summary>Actual compiler output</summary>


```text
def Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M],
  ∃ charted, IsManifold.{0, 0, 0, u} (𝓡 3) ∞ M
def Poincare.SmoothabilitySmoothManifoldStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [T2Space.{u} M]
  [inst_2 : ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u} M]
  [CompactSpace.{u} M], IsManifold.{0, 0, 0, u} (𝓡 3) ∞ M
def Poincare.PoincareConjectureStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M],
  Nonempty.{max 1 (u + 1)} (Homeomorph.{u, 0} M Poincare.ThreeSphere)
Poincare.poincareConjectureStatement_iff_canonical_three_sphere_statement.{u_1} : Iff
  Poincare.PoincareConjectureStatement.{u_1}
  (∀ (M : Type u_1) [inst : TopologicalSpace.{u_1} M] [T2Space.{u_1} M]
    [ChartedSpace.{0, u_1} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u_1} M]
    [CompactSpace.{u_1} M], Nonempty.{u_1 + 1} (Homeomorph.{u_1, 0} M Poincare.ThreeSphere))
Poincare.canonical_three_sphere_statement_iff_canonical_completion_target.{u_1} : Iff
  (∀ (M : Type u_1) [inst : TopologicalSpace.{u_1} M] [T2Space.{u_1} M]
    [ChartedSpace.{0, u_1} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u_1} M]
    [CompactSpace.{u_1} M], Nonempty.{u_1 + 1} (Homeomorph.{u_1, 0} M Poincare.ThreeSphere))
  Poincare.canonicalCompletionTarget.{u_1}
Poincare.poincareConjecture_of_universalHamiltonConvergence.{u_1} : Poincare.UniversalHamiltonConvergenceStatement.{u_1} →
  Poincare.PoincareConjecture.{u_1}
Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence.{u_1} : Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u_1} →
  Poincare.UniversalHamiltonConvergenceStatement.{u_1} → Poincare.PoincareConjectureStatement.{u_1}
structure Poincare.HasMoiseLocalTriangulationCharts.{u} (M : Type u) [TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M] : Prop
number of parameters: 6
fields:
  Poincare.HasMoiseLocalTriangulationCharts.onePointRecognition.{u} : Nonempty.{u + 1}
      (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))
constructor:
  Poincare.HasMoiseLocalTriangulationCharts.mk.{u} {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M]
    [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
    (onePointRecognition : Nonempty.{u + 1} (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))) :
    Poincare.HasMoiseLocalTriangulationCharts.{u} M
structure Poincare.HasMoiseTriangulation.{u} (M : Type u) [TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M] : Prop
number of parameters: 6
fields:
  Poincare.HasMoiseTriangulation.onePointRecognition.{u} : Nonempty.{u + 1}
      (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))
constructor:
  Poincare.HasMoiseTriangulation.mk.{u} {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M]
    [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
    (onePointRecognition : Nonempty.{u + 1} (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))) :
    Poincare.HasMoiseTriangulation.{u} M
structure Poincare.HasCompatiblePLStructure.{u} (M : Type u) [TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
  (_triangulation : Poincare.HasMoiseTriangulation.{u} M) : Prop
number of parameters: 7
fields:
  Poincare.HasCompatiblePLStructure.onePointRecognition.{u} : Nonempty.{u + 1}
      (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))
constructor:
  Poincare.HasCompatiblePLStructure.mk.{u} {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M]
    [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
    {_triangulation : Poincare.HasMoiseTriangulation.{u} M}
    (onePointRecognition : Nonempty.{u + 1} (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))) :
    Poincare.HasCompatiblePLStructure.{u} M _triangulation
structure Poincare.HasPLSmoothingExistence.{u} (M : Type u) [TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
  (triangulation : Poincare.HasMoiseTriangulation.{u} M)
  (plStructure : Poincare.HasCompatiblePLStructure.{u} M triangulation)
  (plAtlas : Poincare.HasCompatiblePLAtlas.{u} M triangulation plStructure) : Prop
number of parameters: 9
fields:
  Poincare.HasPLSmoothingExistence.onePointRecognition.{u} : Nonempty.{u + 1}
      (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))))
  Poincare.HasPLSmoothingExistence.plStructure_eq.{u} : Eq.{0} plStructure ⋯
  Poincare.HasPLSmoothingExistence.plAtlas_eq.{u} : Eq.{0} plAtlas ⋯
constructor:
  Poincare.HasPLSmoothingExistence.mk.{u} {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M]
    [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M]
    {triangulation : Poincare.HasMoiseTriangulation.{u} M}
    {plStructure : Poincare.HasCompatiblePLStructure.{u} M triangulation}
    {plAtlas : Poincare.HasCompatiblePLAtlas.{u} M triangulation plStructure}
    (onePointRecognition : Nonempty.{u + 1} (Homeomorph.{u, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3)))))
    (plStructure_eq : Eq.{0} plStructure ⋯) (plAtlas_eq : Eq.{0} plAtlas ⋯) :
    Poincare.HasPLSmoothingExistence.{u} M triangulation plStructure plAtlas
def Poincare.AdmitsSurgeryModelSmoothStructure.{u} : (M : Type u) → [TopologicalSpace.{u} M] → Prop :=
fun M [TopologicalSpace.{u} M] => ∃ _charted, IsManifold.{0, 0, 0, u} Poincare.ThreeManifoldModelWithCorners 1 M
def Poincare.MoiseSmoothabilityStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [T2Space.{u} M] [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M]
  [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M], Poincare.AdmitsSurgeryModelSmoothStructure.{u} M
def Poincare.C1ToCInfinityAtlasUpgrade3.{u} : (M : Type u) → [TopologicalSpace.{u} M] → Prop :=
fun M [TopologicalSpace.{u} M] =>
  ∀ (c1Atlas : ChartedSpace.{0, u} Poincare.ThreeManifoldModel M),
    IsManifold.{0, 0, 0, u} Poincare.ThreeManifoldModelWithCorners 1 M →
      ∃ smoothAtlas, IsManifold.{0, 0, 0, u} (𝓡 3) ∞ M
def Poincare.GroundedTopologyUniversalSourceStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [inst_1 : T2Space.{u} M]
  [ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [inst_3 : SimplyConnectedSpace.{u} M]
  [inst_4 : CompactSpace.{u} M], Nonempty.{u + 2} (Poincare.GroundedTopologyPresentation.{u} M)
def Poincare.GroundedTopologyThreeSphereCoveringStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [inst_1 : T2Space.{u} M]
  [inst_2 : ChartedSpace.{0, u} Poincare.ThreeManifoldModel M] [inst_3 : SimplyConnectedSpace.{u} M]
  [inst_4 : CompactSpace.{u} M] (_source : Poincare.GroundedTopologySource.{u} M), ∃ p, IsCoveringMap.{0, u} p
@Poincare.ExtinctionSurgeryTraceRealizationSource.smooth.{u_1} : ∀ {M : Type u_1} [inst : TopologicalSpace.{u_1} M]
  [inst_1 : T2Space.{u_1} M] [inst_2 : ChartedSpace.{0, u_1} (EuclideanSpace.{0, 0} Real (Fin 3)) M]
  [inst_3 : SimplyConnectedSpace.{u_1} M] [inst_4 : CompactSpace.{u_1} M]
  {extinction : Poincare.FiniteExtinctionByRicciFlowWithSurgery.{u_1} M}
  {decomposition : Poincare.HasExtinctionTopologyDecomposition.{u_1} M extinction} {traceStage : Type u_1}
  (self : Poincare.ExtinctionSurgeryTraceRealizationSource.{u_1} M extinction decomposition traceStage),
  IsManifold.{0, 0, 0, u_1} Poincare.ThreeManifoldModelWithCorners 1 M
Poincare.poincare_statement_of_groundedTopologySources_and_covering.{u_1} : Poincare.GroundedTopologyUniversalSourceStatement.{u_1} →
  Poincare.GroundedTopologyThreeSphereCoveringStatement.{u_1} → Poincare.PoincareConjectureStatement.{u_1}
@Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected.{u_1,
    u_2} : {E : Type u_1} →
  {X : Type u_2} →
    [inst : TopologicalSpace.{u_1} E] →
      [inst_1 : TopologicalSpace.{u_2} X] →
        {p : E → X} →
          [ConnectedSpace.{u_1} E] →
            [SimplyConnectedSpace.{u_2} X] →
              [LocPathConnectedSpace.{u_2} X] → IsCoveringMap.{u_1, u_2} p → Homeomorph.{u_1, u_2} E X
@Poincare.SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3.{u_1} : ∀ {M : Type u_1}
  [inst : TopologicalSpace.{u_1} M] [inst_1 : T2Space.{u_1} M] [inst_2 : CompactSpace.{u_1} M]
  [inst_3 : ChartedSpace.{0, u_1} (EuclideanSpace.{0, 0} Real (Fin 3)) M],
  Nonempty.{u_1 + 1} (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.{u_1} M)
@Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.exists_finitePrecompactTopologicalChartAtAtlas3.{u_1} : ∀
  {M : Type u_1} [inst : TopologicalSpace.{u_1} M] [inst_1 : T2Space.{u_1} M] [inst_2 : CompactSpace.{u_1} M]
  [inst_3 : ChartedSpace.{0, u_1} (EuclideanSpace.{0, 0} Real (Fin 3)) M],
  Nonempty.{u_1 + 1}
    (Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.{u_1} M)
@Poincare.nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas.{u_1} : ∀ {M : Type u_1}
  [inst : TopologicalSpace.{u_1} M],
  Iff (Nonempty.{u_1 + 1} (Poincare.CInfinityLocalTransitionAtlasData3.{u_1} M))
    (∃ smoothAtlas, IsManifold.{0, 0, 0, u_1} (Poincare.closedSmoothModelWithCorners 3) ∞ M)
structure Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.{u}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
  [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M]
  (reduction : Poincare.SmoothabilitySimultaneousLocalConjugacy.NerveReduction3.{u} M) : Type u
number of parameters: 6
fields:
  Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.correction.{u} : ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
          (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction)) →
      OpenPartialHomeomorph.{0, 0} (EuclideanSpace.{0, 0} Real (Fin 3)) (EuclideanSpace.{0, 0} Real (Fin 3))
  Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.correction_neighborhood.{u} : ∀
      (i :
        ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
            (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction))),
      Subset.{0}
        (Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.compactCoordinateImage.{u}
          (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction) i)
        (PartialEquiv.source.{0, 0}
          (OpenPartialHomeomorph.toPartialEquiv.{0, 0}
            (Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.correction.{u}
              self i)))
  Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.local_conjugacy.{u} : Poincare.SmoothabilitySimultaneousLocalConjugacy.CorrectedTransitionsLocallySmoothlyConjugateOnCompact3.{u}
      (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction)
      (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.transitions.{u} reduction)
      (Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.correction.{u}
        self)
constructor:
  Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.mk.{u} {M : Type u}
    [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
    [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M]
    {reduction : Poincare.SmoothabilitySimultaneousLocalConjugacy.NerveReduction3.{u} M}
    (correction :
      ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
            (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction)) →
        OpenPartialHomeomorph.{0, 0} (EuclideanSpace.{0, 0} Real (Fin 3)) (EuclideanSpace.{0, 0} Real (Fin 3)))
    (correction_neighborhood :
      ∀
        (i :
          ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
              (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction))),
        Subset.{0}
          (Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.compactCoordinateImage.{u}
            (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction) i)
          (PartialEquiv.source.{0, 0} (OpenPartialHomeomorph.toPartialEquiv.{0, 0} (correction i))))
    (local_conjugacy :
      Poincare.SmoothabilitySimultaneousLocalConjugacy.CorrectedTransitionsLocallySmoothlyConjugateOnCompact3.{u}
        (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.atlas.{u} reduction)
        (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3.transitions.{u} reduction)
        correction) :
    Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.{u} reduction
def Poincare.SmoothabilitySimultaneousLocalConjugacy.CorrectedTransitionsLocallySmoothlyConjugateOnCompact3.{u} : {M :
    Type u} →
  [inst : TopologicalSpace.{u} M] →
    [inst_1 : T2Space.{u} M] →
      [inst_2 : CompactSpace.{u} M] →
        [inst_3 : ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] →
          (data : Poincare.SmoothabilitySimultaneousLocalConjugacy.PrecompactAtlas3.{u} M) →
            Poincare.SmoothabilitySimultaneousLocalConjugacy.NerveTransitionPackage3.{u} data →
              (↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
                      data) →
                  OpenPartialHomeomorph.{0, 0} (EuclideanSpace.{0, 0} Real (Fin 3))
                    (EuclideanSpace.{0, 0} Real (Fin 3))) →
                Prop :=
fun {M} [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
    [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] data nerve correction =>
  ∀ (p : ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
    (v : EuclideanSpace.{0, 0} Real (Fin 3)),
    Membership.mem.{0, 0}
        (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u} nerve
          p)
        v →
      ∃ e,
        And
          (Membership.mem.{0, 0}
            (PartialEquiv.source.{0, 0}
              (OpenPartialHomeomorph.toPartialEquiv.{0, 0}
                (Poincare.SmoothabilitySimultaneousLocalConjugacy.SmoothLocalDiffeomorphism3.toOpenPartialHomeomorph
                  e)))
            (↑(correction (↑p).1) v))
          (∀ (w : EuclideanSpace.{0, 0} Real (Fin 3)),
            Membership.mem.{0, 0}
                (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u}
                  nerve p)
                w →
              Membership.mem.{0, 0}
                  (PartialEquiv.source.{0, 0}
                    (OpenPartialHomeomorph.toPartialEquiv.{0, 0}
                      (Poincare.SmoothabilitySimultaneousLocalConjugacy.SmoothLocalDiffeomorphism3.toOpenPartialHomeomorph
                        e)))
                  (↑(correction (↑p).1) w) →
                Eq.{1}
                  (↑(Poincare.SmoothabilitySimultaneousLocalConjugacy.SmoothLocalDiffeomorphism3.toOpenPartialHomeomorph
                        e)
                    (↑(correction (↑p).1) w))
                  (↑(correction (↑p).2)
                    (↑(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionMap.{u}
                          nerve p)
                      w)))
structure Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.{u}
  {M : Type u} [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
  [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M]
  (data : Poincare.SmoothabilityFiniteTetrahedralStarReduction.PrecompactAtlas3.{u} M)
  (nerve : Poincare.SmoothabilityFiniteTetrahedralStarReduction.NerveTransitionPackage3.{u} data) : Type u
number of parameters: 7
fields:
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u} : ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
          data) →
      OpenPartialHomeomorph.{u, 0} M (EuclideanSpace.{0, 0} Real (Fin 3))
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart_neighborhood.{u} : ∀
      (i :
        ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.centers.{u}
            data)),
      Subset.{u}
        (closure.{u}
          (Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.innerDomain.{u}
            data i))
        (PartialEquiv.source.{u, 0}
          (OpenPartialHomeomorph.toPartialEquiv.{u, 0}
            (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u}
              self i)))
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u} : ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u}
          nerve) →
      Nat
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexVertices.{u} : (p :
        ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve)) →
      Fin
          (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u}
            self p) →
        Fin 4 → EuclideanSpace.{0, 0} Real (Fin 3)
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplex_affineIndependent.{u} : ∀
      (p : ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
      (q :
        Fin
          (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u}
            self p)),
      AffineIndependent.{0, 0, 0, 0} Real
        (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexVertices.{u}
          self p q)
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexMap.{u} : (p :
        ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve)) →
      Fin
          (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u}
            self p) →
        ContinuousAffineMap.{0, 0, 0, 0, 0} Real (EuclideanSpace.{0, 0} Real (Fin 3))
          (EuclideanSpace.{0, 0} Real (Fin 3))
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.correctedCompactDomain_subset_simplexCover.{u} : ∀
      (p :
        ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve)),
      Subset.{0}
        (Set.image.{0, 0}
          (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
              (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u}
                self)
              (↑p).1))
          (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u} nerve
            p))
        (⋃ q,
          Poincare.SmoothabilityFiniteTetrahedralStarReduction.tetrahedronCarrier
            (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexVertices.{u}
              self p q))
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexMap_agrees_on_correctedCompactDomain.{u} : ∀
      (p : ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
      (q :
        Fin
          (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u}
            self p))
      (v : EuclideanSpace.{0, 0} Real (Fin 3)),
      Membership.mem.{0, 0}
          (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u} nerve
            p)
          v →
        Membership.mem.{0, 0}
            (Poincare.SmoothabilityFiniteTetrahedralStarReduction.tetrahedronCarrier
              (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexVertices.{u}
                self p q))
            (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                  (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u}
                    self)
                  (↑p).1)
              v) →
          Eq.{1}
            ((Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexMap.{u}
                self p q)
              (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                    (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u}
                      self)
                    (↑p).1)
                v))
            (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                  (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.developedChart.{u}
                    self)
                  (↑p).2)
              (↑(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionMap.{u}
                    nerve p)
                v))
constructor:
  Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.mk.{u} {M : Type u}
    [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
    [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M]
    {data : Poincare.SmoothabilityFiniteTetrahedralStarReduction.PrecompactAtlas3.{u} M}
    {nerve : Poincare.SmoothabilityFiniteTetrahedralStarReduction.NerveTransitionPackage3.{u} data}
    (developedChart :
      ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.Index.{u}
            data) →
        OpenPartialHomeomorph.{u, 0} M (EuclideanSpace.{0, 0} Real (Fin 3)))
    (developedChart_neighborhood :
      ∀
        (i :
          ↥(Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.centers.{u}
              data)),
        Subset.{u}
          (closure.{u}
            (Poincare.SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.innerDomain.{u}
              data i))
          (PartialEquiv.source.{u, 0} (OpenPartialHomeomorph.toPartialEquiv.{u, 0} (developedChart i))))
    (simplexCount :
      ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve) →
        Nat)
    (simplexVertices :
      (p :
          ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u}
              nerve)) →
        Fin (simplexCount p) → Fin 4 → EuclideanSpace.{0, 0} Real (Fin 3))
    (simplex_affineIndependent :
      ∀
        (p :
          ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
        (q : Fin (simplexCount p)), AffineIndependent.{0, 0, 0, 0} Real (simplexVertices p q))
    (simplexMap :
      (p :
          ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u}
              nerve)) →
        Fin (simplexCount p) →
          ContinuousAffineMap.{0, 0, 0, 0, 0} Real (EuclideanSpace.{0, 0} Real (Fin 3))
            (EuclideanSpace.{0, 0} Real (Fin 3)))
    (correctedCompactDomain_subset_simplexCover :
      ∀
        (p :
          ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve)),
        Subset.{0}
          (Set.image.{0, 0}
            (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                developedChart (↑p).1))
            (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u}
              nerve p))
          (⋃ q, Poincare.SmoothabilityFiniteTetrahedralStarReduction.tetrahedronCarrier (simplexVertices p q)))
    (simplexMap_agrees_on_correctedCompactDomain :
      ∀
        (p :
          ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
        (q : Fin (simplexCount p)) (v : EuclideanSpace.{0, 0} Real (Fin 3)),
        Membership.mem.{0, 0}
            (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u}
              nerve p)
            v →
          Membership.mem.{0, 0}
              (Poincare.SmoothabilityFiniteTetrahedralStarReduction.tetrahedronCarrier (simplexVertices p q))
              (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                    developedChart (↑p).1)
                v) →
            Eq.{1}
              ((simplexMap p q)
                (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                      developedChart (↑p).1)
                  v))
              (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.vertexCorrectionOfDevelopedCharts.{u} data
                    developedChart (↑p).2)
                (↑(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionMap.{u}
                      nerve p)
                  v))) :
    Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.{u} data nerve
def Poincare.SmoothabilityFiniteTetrahedralStarReduction.StarwiseTangentCompatible3.{u} : {M : Type u} →
  [inst : TopologicalSpace.{u} M] →
    [inst_1 : T2Space.{u} M] →
      [inst_2 : CompactSpace.{u} M] →
        [inst_3 : ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] →
          {data : Poincare.SmoothabilityFiniteTetrahedralStarReduction.PrecompactAtlas3.{u} M} →
            {nerve : Poincare.SmoothabilityFiniteTetrahedralStarReduction.NerveTransitionPackage3.{u} data} →
              Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.{u} data
                  nerve →
                Prop :=
fun {M} [TopologicalSpace.{u} M] [T2Space.{u} M] [CompactSpace.{u} M]
    [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] {data} {nerve} input =>
  ∀ (p : ↥(Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs.{u} nerve))
    (v : EuclideanSpace.{0, 0} Real (Fin 3)),
    Membership.mem.{0, 0}
        (Poincare.SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.transitionDomain.{u} nerve
          p)
        v →
      ∀
        (q r :
          Fin
            (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCount.{u}
              input p)),
        Membership.mem.{0, 0}
            (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCarrier.{u}
              input p q)
            (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.correction.{u}
                  input (↑p).1)
              v) →
          Membership.mem.{0, 0}
              (Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexCarrier.{u}
                input p r)
              (↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.correction.{u}
                    input (↑p).1)
                v) →
            Eq.{1}
              (AffineMap.linear.{0, 0, 0, 0, 0}
                ↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexMap.{u}
                    input p q))
              (AffineMap.linear.{0, 0, 0, 0, 0}
                ↑(Poincare.SmoothabilityFiniteTetrahedralStarReduction.FiniteTetrahedralPLTransitionPresentation3.simplexMap.{u}
                    input p r))
structure PreAbstractSimplicialComplex.{u_1} (ι : Type u_1) : Type u_1
number of parameters: 1
fields:
  PreAbstractSimplicialComplex.faces.{u_1} : Set.{u_1} (Finset.{u_1} ι)
  PreAbstractSimplicialComplex.isRelLowerSet_faces.{u_1} : IsRelLowerSet.{u_1}
      (PreAbstractSimplicialComplex.faces.{u_1} self) Finset.Nonempty.{u_1}
constructor:
  PreAbstractSimplicialComplex.mk.{u_1} {ι : Type u_1} (faces : Set.{u_1} (Finset.{u_1} ι))
    (isRelLowerSet_faces : IsRelLowerSet.{u_1} faces Finset.Nonempty.{u_1}) : PreAbstractSimplicialComplex.{u_1} ι
structure AbstractSimplicialComplex.{u_1} (ι : Type u_1) : Type u_1
number of parameters: 1
parents:
  AbstractSimplicialComplex.toPreAbstractSimplicialComplex.{u_1} : PreAbstractSimplicialComplex.{u_1} ι
fields:
  PreAbstractSimplicialComplex.faces.{u_1} : Set.{u_1} (Finset.{u_1} ι)
  PreAbstractSimplicialComplex.isRelLowerSet_faces.{u_1} : IsRelLowerSet.{u_1}
      (PreAbstractSimplicialComplex.faces.{u_1} (AbstractSimplicialComplex.toPreAbstractSimplicialComplex.{u_1} self))
      Finset.Nonempty.{u_1}
  AbstractSimplicialComplex.singleton_mem.{u_1} : ∀ (v : ι),
      Membership.mem.{u_1, u_1}
        (PreAbstractSimplicialComplex.faces.{u_1} (AbstractSimplicialComplex.toPreAbstractSimplicialComplex.{u_1} self))
        (singleton.{u_1, u_1} v)
constructor:
  AbstractSimplicialComplex.mk.{u_1} {ι : Type u_1}
    (toPreAbstractSimplicialComplex : PreAbstractSimplicialComplex.{u_1} ι)
    (singleton_mem :
      ∀ (v : ι),
        Membership.mem.{u_1, u_1} (PreAbstractSimplicialComplex.faces.{u_1} toPreAbstractSimplicialComplex)
          (singleton.{u_1, u_1} v)) :
    AbstractSimplicialComplex.{u_1} ι
field notation resolution order:
  AbstractSimplicialComplex.{u_1}, PreAbstractSimplicialComplex.{u_1}
structure Geometry.SimplicialComplex.{u_1, u_2} (𝕜 : Type u_1) (E : Type u_2) [Ring.{u_1} 𝕜] [PartialOrder.{u_1} 𝕜]
  [AddCommGroup.{u_2} E] [Module.{u_1, u_2} 𝕜 E] : Type u_2
number of parameters: 6
parents:
  Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} : PreAbstractSimplicialComplex.{u_2} E
fields:
  PreAbstractSimplicialComplex.faces.{u_1} : Set.{u_2} (Finset.{u_2} E)
  PreAbstractSimplicialComplex.isRelLowerSet_faces.{u_1} : IsRelLowerSet.{u_2}
      (PreAbstractSimplicialComplex.faces.{u_2}
        (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} self))
      Finset.Nonempty.{u_2}
  Geometry.SimplicialComplex.indep.{u_1,
    u_2} : ∀ {s : Finset.{u_2} E},
      Membership.mem.{u_2, u_2}
          (PreAbstractSimplicialComplex.faces.{u_2}
            (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} self))
          s →
        AffineIndependent.{u_1, u_2, u_2, u_2} 𝕜 Subtype.val.{u_2 + 1}
  Geometry.SimplicialComplex.inter_subset_convexHull.{u_1,
    u_2} : ∀ {s t : Finset.{u_2} E},
      Membership.mem.{u_2, u_2}
          (PreAbstractSimplicialComplex.faces.{u_2}
            (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} self))
          s →
        Membership.mem.{u_2, u_2}
            (PreAbstractSimplicialComplex.faces.{u_2}
              (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} self))
            t →
          Subset.{u_2} (Inter.inter.{u_2} ((convexHull.{u_1, u_2} 𝕜) ↑s) ((convexHull.{u_1, u_2} 𝕜) ↑t))
            ((convexHull.{u_1, u_2} 𝕜) (Inter.inter.{u_2} ↑s ↑t))
constructor:
  Geometry.SimplicialComplex.mk.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [Ring.{u_1} 𝕜] [PartialOrder.{u_1} 𝕜]
    [AddCommGroup.{u_2} E] [Module.{u_1, u_2} 𝕜 E]
    (toPreAbstractSimplicialComplex : PreAbstractSimplicialComplex.{u_2} E)
    (indep :
      ∀ {s : Finset.{u_2} E},
        Membership.mem.{u_2, u_2} (PreAbstractSimplicialComplex.faces.{u_2} toPreAbstractSimplicialComplex) s →
          AffineIndependent.{u_1, u_2, u_2, u_2} 𝕜 Subtype.val.{u_2 + 1})
    (inter_subset_convexHull :
      ∀ {s t : Finset.{u_2} E},
        Membership.mem.{u_2, u_2} (PreAbstractSimplicialComplex.faces.{u_2} toPreAbstractSimplicialComplex) s →
          Membership.mem.{u_2, u_2} (PreAbstractSimplicialComplex.faces.{u_2} toPreAbstractSimplicialComplex) t →
            Subset.{u_2} (Inter.inter.{u_2} ((convexHull.{u_1, u_2} 𝕜) ↑s) ((convexHull.{u_1, u_2} 𝕜) ↑t))
              ((convexHull.{u_1, u_2} 𝕜) (Inter.inter.{u_2} ↑s ↑t))) :
    Geometry.SimplicialComplex.{u_1, u_2} 𝕜 E
field notation resolution order:
  Geometry.SimplicialComplex.{u_1, u_2}, PreAbstractSimplicialComplex.{u_1}
@Geometry.SimplicialComplex.space.{u_1,
    u_2} : {𝕜 : Type u_1} →
  {E : Type u_2} →
    [inst : Ring.{u_1} 𝕜] →
      [inst_1 : PartialOrder.{u_1} 𝕜] →
        [inst_2 : AddCommGroup.{u_2} E] →
          [inst_3 : Module.{u_1, u_2} 𝕜 E] → Geometry.SimplicialComplex.{u_1, u_2} 𝕜 E → Set.{u_2} E
@Geometry.SimplicialComplex.convexHull_inter_convexHull.{u_1,
    u_2} : ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Ring.{u_1} 𝕜] [inst_1 : PartialOrder.{u_1} 𝕜]
  [inst_2 : AddCommGroup.{u_2} E] [inst_3 : Module.{u_1, u_2} 𝕜 E] {K : Geometry.SimplicialComplex.{u_1, u_2} 𝕜 E}
  {s t : Finset.{u_2} E},
  Membership.mem.{u_2, u_2}
      (PreAbstractSimplicialComplex.faces.{u_2}
        (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} K))
      s →
    Membership.mem.{u_2, u_2}
        (PreAbstractSimplicialComplex.faces.{u_2}
          (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} K))
        t →
      Eq.{u_2 + 1} (Inter.inter.{u_2} ((convexHull.{u_1, u_2} 𝕜) ↑s) ((convexHull.{u_1, u_2} 𝕜) ↑t))
        ((convexHull.{u_1, u_2} 𝕜) (Inter.inter.{u_2} ↑s ↑t))
@Geometry.SimplicialComplex.down_closed.{u_1,
    u_2} : ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Ring.{u_1} 𝕜] [inst_1 : PartialOrder.{u_1} 𝕜]
  [inst_2 : AddCommGroup.{u_2} E] [inst_3 : Module.{u_1, u_2} 𝕜 E] {K : Geometry.SimplicialComplex.{u_1, u_2} 𝕜 E}
  {s t : Finset.{u_2} E},
  Membership.mem.{u_2, u_2}
      (PreAbstractSimplicialComplex.faces.{u_2}
        (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} K))
      s →
    Subset.{u_2} t s →
      Finset.Nonempty.{u_2} t →
        Membership.mem.{u_2, u_2}
          (PreAbstractSimplicialComplex.faces.{u_2}
            (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{u_1, u_2} K))
          t
@Set.Finite.isCompact_convexHull.{u_1,
    u_2} : ∀ {E : Type u_1} (𝕜 : Type u_2) [inst : Field.{u_2} 𝕜] [inst_1 : LinearOrder.{u_2} 𝕜]
  [IsStrictOrderedRing.{u_2} 𝕜] [inst_3 : TopologicalSpace.{u_2} 𝕜] [OrderClosedTopology.{u_2} 𝕜]
  [CompactIccSpace.{u_2} 𝕜] [ContinuousAdd.{u_2} 𝕜] [inst_7 : AddCommGroup.{u_1} E] [inst_8 : Module.{u_2, u_1} 𝕜 E]
  [inst_9 : TopologicalSpace.{u_1} E] [IsTopologicalAddGroup.{u_1} E] [ContinuousSMul.{u_2, u_1} 𝕜 E] {s : Set.{u_1} E},
  Set.Finite.{u_1} s → IsCompact.{u_1} ((convexHull.{u_2, u_1} 𝕜) s)
@exists_embedding_euclidean_of_compact.{u_1, u_2,
    u_3} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E]
  [FiniteDimensional.{0, u_1} Real E] {H : Type u_2} [inst_3 : TopologicalSpace.{u_2} H]
  {I : ModelWithCorners.{0, u_1, u_2} Real E H} {M : Type u_3} [inst_4 : TopologicalSpace.{u_3} M]
  [inst_5 : ChartedSpace.{u_2, u_3} H M] [IsManifold.{0, u_1, u_2, u_3} I ∞ M] [T2Space.{u_3} M] [CompactSpace.{u_3} M],
  ∃ n e,
    And (ContMDiff.{0, u_1, u_2, u_3, 0, 0, 0} I (𝓡 n) ∞ e)
      (And (Topology.IsClosedEmbedding.{u_3, 0} e) (∀ (x : M), Function.Injective.{u_1 + 1, 1} ⇑(mfderiv% e x)))
@SmoothBumpCovering.exists_immersion_euclidean.{u_1, u_2, u_3,
    u_4} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E]
  [inst_2 : FiniteDimensional.{0, u_1} Real E] {H : Type u_2} [inst_3 : TopologicalSpace.{u_2} H]
  {I : ModelWithCorners.{0, u_1, u_2} Real E H} {M : Type u_3} [inst_4 : TopologicalSpace.{u_3} M]
  [inst_5 : ChartedSpace.{u_2, u_3} H M] [IsManifold.{0, u_1, u_2, u_3} I ∞ M] [T2Space.{u_3} M] {ι : Type u_4}
  [Finite.{u_4 + 1} ι] (f : SmoothBumpCovering.{u_4, u_1, u_2, u_3} ι I M),
  ∃ n e,
    And (ContMDiff.{0, u_1, u_2, u_3, 0, 0, 0} I (𝓡 n) ∞ e)
      (And (Function.Injective.{u_3 + 1, 1} e) (∀ (x : M), Function.Injective.{u_1 + 1, 1} ⇑(mfderiv% e x)))
ChartedSpace.secondCountable_of_sigmaCompact.{u_1,
  u_2} : ∀ (H : Type u_1) (M : Type u_2) [inst : TopologicalSpace.{u_1} H] [inst_1 : TopologicalSpace.{u_2} M]
  [ChartedSpace.{u_1, u_2} H M] [SecondCountableTopology.{u_1} H] [SigmaCompactSpace.{u_2} M],
  SecondCountableTopology.{u_2} M
@Topology.CWComplex.{u_1} : {X : Type u_1} → [TopologicalSpace.{u_1} X] → Set.{u_1} X → Type (u_1 + 1)
```


</details>


### P. Proposed interfaces and scratch feasibility proofs

The three anonymous examples check the selected-nerve-to-existential-smoothability edge, finite support compactness, and grounded-source-to-C¹-smoothability edge. Neither proposed existence statement has a proof. Earlier versions/failures are recorded below. The preceding successful version before adding the compactness example had the same printed output, since successful anonymous examples print nothing.

Command, run from the survey worktree:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_plan.lean
```


Actual Lean exit code: `0`. Source and complete actual output follow.

<details>
<summary>Probe source</summary>


```lean
import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Poincare.ProofProgress.GroundedTopologyAssembly
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false
set_option pp.universes true
set_option format.width 110
open scoped Manifold ContDiff
universe u
namespace SmoothabilitySurveyProposal
-- New proposal, not a landed declaration or proved existence theorem.
def FiniteTriangulationData3 (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ n : ℕ, ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
    K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 4) ∧ Nonempty (M ≃ₜ K.space)
def FiniteTriangulationExistence3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      FiniteTriangulationData3 M
-- Target proposition only; the task below has not been implemented.
def FiniteComplexCompactnessTarget : Prop :=
  ∀ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))),
    K.faces.Finite → IsCompact K.space
open Poincare
open Poincare.SmoothabilityFiniteAtlasNerveReduction
open Poincare.SmoothabilitySimultaneousLocalConjugacy
-- Smaller quantifier scope than solving every finite reduction of a manifold.
def SelectedFiniteNerveSmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ r : FiniteAtlasNerveReduction3 M,
        Nonempty (FiniteNerveSimultaneousLocalConjugacySmoothing3 r)
-- Scratch verification of the proposed edge. No project file is changed.
example (h : SelectedFiniteNerveSmoothingStatement.{u}) :
    ExistsSmoothabilitySmoothManifoldStatement.{u} := by
  intro M _ _ _ _ _
  obtain ⟨r, ⟨s⟩⟩ := h M
  exact nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas.mp
    s.nonempty_cInfinityLocalTransitionAtlasData3
-- Scratch feasibility proof for the only new foundational A task.
example (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hf : K.faces.Finite) : IsCompact K.space := by
  exact hf.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ
-- Exact regularity implied by grounded source existence is C1.
example (h : GroundedTopologyUniversalSourceStatement.{u}) :
    MoiseSmoothabilityStatement.{u} := by
  intro M _ _ _ _ _
  obtain ⟨p⟩ := h M
  letI : ChartedSpace ThreeManifoldModel M := p.chartedSpace
  exact ⟨p.chartedSpace, p.source.trace.smooth⟩
#print FiniteTriangulationData3
#print FiniteTriangulationExistence3
#print FiniteComplexCompactnessTarget
#print SelectedFiniteNerveSmoothingStatement
#check @Geometry.SimplicialComplex.space
#check @Set.Finite.isCompact_convexHull
end SmoothabilitySurveyProposal
```


</details>

<details>
<summary>Actual compiler output</summary>


```text
def SmoothabilitySurveyProposal.FiniteTriangulationData3.{u} : (M : Type u) → [TopologicalSpace.{u} M] → Prop :=
fun M [TopologicalSpace.{u} M] =>
  ∃ n K,
    And
      (Set.Finite.{0}
        (PreAbstractSimplicialComplex.faces.{0} (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{0, 0} K)))
      (And
        (∀ (s : Finset.{0} (EuclideanSpace.{0, 0} Real (Fin n))),
          Membership.mem.{0, 0}
              (PreAbstractSimplicialComplex.faces.{0}
                (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{0, 0} K))
              s →
            LE.le.{0} (Finset.card.{0} s) 4)
        (Nonempty.{max 1 (u + 1)} (Homeomorph.{u, 0} M ↑(Geometry.SimplicialComplex.space.{0, 0} K))))
def SmoothabilitySurveyProposal.FiniteTriangulationExistence3.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [T2Space.{u} M]
  [ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u} M] [CompactSpace.{u} M],
  FiniteTriangulationData3.{u} M
def SmoothabilitySurveyProposal.FiniteComplexCompactnessTarget : Prop :=
∀ (n : Nat) (K : Geometry.SimplicialComplex.{0, 0} Real (EuclideanSpace.{0, 0} Real (Fin n))),
  Set.Finite.{0}
      (PreAbstractSimplicialComplex.faces.{0} (Geometry.SimplicialComplex.toPreAbstractSimplicialComplex.{0, 0} K)) →
    IsCompact.{0} (Geometry.SimplicialComplex.space.{0, 0} K)
def SmoothabilitySurveyProposal.SelectedFiniteNerveSmoothingStatement.{u} : Prop :=
∀ (M : Type u) [inst : TopologicalSpace.{u} M] [inst_1 : T2Space.{u} M]
  [inst_2 : ChartedSpace.{0, u} (EuclideanSpace.{0, 0} Real (Fin 3)) M] [SimplyConnectedSpace.{u} M]
  [inst_4 : CompactSpace.{u} M], ∃ r, Nonempty.{u + 1} (FiniteNerveSimultaneousLocalConjugacySmoothing3.{u} r)
@Geometry.SimplicialComplex.space.{u_1,
    u_2} : {𝕜 : Type u_1} →
  {E : Type u_2} →
    [inst : Ring.{u_1} 𝕜] →
      [inst_1 : PartialOrder.{u_1} 𝕜] →
        [inst_2 : AddCommGroup.{u_2} E] →
          [inst_3 : Module.{u_1, u_2} 𝕜 E] → Geometry.SimplicialComplex.{u_1, u_2} 𝕜 E → Set.{u_2} E
@Set.Finite.isCompact_convexHull.{u_1,
    u_2} : ∀ {E : Type u_1} (𝕜 : Type u_2) [inst : Field.{u_2} 𝕜] [inst_1 : LinearOrder.{u_2} 𝕜]
  [IsStrictOrderedRing.{u_2} 𝕜] [inst_3 : TopologicalSpace.{u_2} 𝕜] [OrderClosedTopology.{u_2} 𝕜]
  [CompactIccSpace.{u_2} 𝕜] [ContinuousAdd.{u_2} 𝕜] [inst_7 : AddCommGroup.{u_1} E] [inst_8 : Module.{u_2, u_1} 𝕜 E]
  [inst_9 : TopologicalSpace.{u_1} E] [IsTopologicalAddGroup.{u_1} E] [ContinuousSMul.{u_2, u_1} 𝕜 E] {s : Set.{u_1} E},
  Set.Finite.{u_1} s → IsCompact.{u_1} ((convexHull.{u_2, u_1} 𝕜) s)
```


</details>


### E. Recognition equivalence and selected axiom closures



Command, run from the survey worktree:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_extra.lean
```


Actual Lean exit code: `0`. Source and complete actual output follow.

<details>
<summary>Probe source</summary>


```lean
import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Poincare.ProofProgress.GroundedTopologyAssembly
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false
set_option pp.universes true
set_option format.width 110
#check @Poincare.homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace
#check @Poincare.onePoint_threeSpace_homeomorph_threeSphere
#check @Set.Finite.isCompact_biUnion
#print axioms Poincare.poincare_statement_of_groundedTopologySources_and_covering
#print axioms Poincare.nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas
#print axioms Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.nonempty_cInfinityLocalTransitionAtlasData3
```


</details>

<details>
<summary>Actual compiler output</summary>


```text
@Poincare.homeomorph_to_threeSphere_iff_homeomorph_to_onePoint_threeSpace.{u_1} : ∀ {M : Type u_1}
  [inst : TopologicalSpace.{u_1} M],
  Iff (Nonempty.{u_1 + 1} (Homeomorph.{u_1, 0} M Poincare.ThreeSphere))
    (Nonempty.{u_1 + 1} (Homeomorph.{u_1, 0} M (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3)))))
Poincare.onePoint_threeSpace_homeomorph_threeSphere : Nonempty.{1}
  (Homeomorph.{0, 0} (OnePoint.{0} (EuclideanSpace.{0, 0} Real (Fin 3))) Poincare.ThreeSphere)
@Set.Finite.isCompact_biUnion.{u_1,
    u_2} : ∀ {X : Type u_1} {ι : Type u_2} [inst : TopologicalSpace.{u_1} X] {s : Set.{u_2} ι} {f : ι → Set.{u_1} X},
  Set.Finite.{u_2} s →
    (∀ (i : ι), Membership.mem.{u_2, u_2} s i → IsCompact.{u_1} (f i)) →
      IsCompact.{u_1} (⋃ i, ⋃ (_ : Membership.mem.{u_2, u_2} s i), f i)
'Poincare.poincare_statement_of_groundedTopologySources_and_covering' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
'Poincare.nonempty_cInfinityLocalTransitionAtlasData3_iff_exists_smoothAtlas' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
'Poincare.SmoothabilitySimultaneousLocalConjugacy.FiniteNerveSimultaneousLocalConjugacySmoothing3.nonempty_cInfinityLocalTransitionAtlasData3' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```


</details>


### D. Actual categorical subdivision signatures



Command, run from the survey worktree:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_subdivision.lean
```


Actual Lean exit code: `0`. Source and complete actual output follow.

<details>
<summary>Probe source</summary>


```lean
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
set_option pp.universes true
#check SSet.sd
#check SSet.ex
#check SSet.sdExAdjunction
```


</details>

<details>
<summary>Actual compiler output</summary>


```text
SSet.sd.{u} : CategoryTheory.Functor.{u, u, u + 1, u + 1} SSet.{u} SSet.{u}
SSet.ex.{u} : CategoryTheory.Functor.{u, u, u + 1, u + 1} SSet.{u} SSet.{u}
SSet.sdExAdjunction.{u} : CategoryTheory.Adjunction.{u, u, u + 1, u + 1} SSet.sd.{u} SSet.ex.{u}
```


</details>


### N. Expected negative endpoint / proof-wanted probes

The two project names are searched as proposed/reserved names, not cited as existing declarations. The three Mathlib names occur in source under `proof_wanted` but are not available constants.

Command, run from the survey worktree:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/smoothability_absent.lean
```


Actual Lean exit code: `1`. Source and complete actual output follow.

<details>
<summary>Probe source</summary>


```lean
import Poincare.Global.HamiltonPoincareReduction
import Mathlib.Geometry.Manifold.PoincareConjecture
#check Poincare.universal_exists_smoothability
#check Poincare.poincare_conjecture
#check SimplyConnectedSpace.nonempty_homeomorph_sphere_three
#check SimplyConnectedSpace.nonempty_diffeomorph_sphere_three
#check ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere
```


</details>

<details>
<summary>Actual compiler output</summary>


```text
/tmp/smoothability_absent.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.universal_exists_smoothability`
/tmp/smoothability_absent.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.poincare_conjecture`
/tmp/smoothability_absent.lean:5:7: error(lean.unknownIdentifier): Unknown constant `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`
/tmp/smoothability_absent.lean:6:7: error(lean.unknownIdentifier): Unknown constant `SimplyConnectedSpace.nonempty_diffeomorph_sphere_three`
/tmp/smoothability_absent.lean:7:7: error(lean.unknownIdentifier): Unknown constant `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere`
```


</details>


