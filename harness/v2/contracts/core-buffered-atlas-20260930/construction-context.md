# Constructed buffered geometry for core Hamilton existence

Core addressed: `UniversalHamiltonConvergenceStatement`, whose real input existence is still open. The accepted `SmoothInitialMetricExistence.exists_initial_metric` supplies an actual initial smooth metric g0. The next eventual target is generic `ClosedRicciFlowNormalization.regularRicciFlowGoal g0`, with ordinary joint C3 at zero preserved.

This batch must construct metric-adapted finite buffered AtlasData, not assume A, P, R, a good initial curvature, sphere recognition or smooth limit realization. Centered shrinking feeds RefinedFiniteAtlasExistence. The refined atlas and metric coefficient neighborhoods feed MetricAdaptedBufferedAtlas. The constructed final buffers feed the actual `BufferedFrozenParabolicSolver.exists_single_chart_parametrix`, which returns local P_i,R_i and positive lifespan/bounds. Select its own positive tolerance at each manifold anchor before applying the buffered theorem. Do not identify two independently chosen tolerance witnesses silently.

The global L/P/R tensor operator construction is still missing. Its exact next analytic consumer is `ParametrixNeumannCorrection.exists_right_inverse` with L.comp P=id-R and normR<1. Preserve the local residual sign (chartValue(Pf)-f), destination-only localization of already weighted fields, and the fixed-anchor cutoff-one condition needed by principalIdentity.

This construction does not imply global continuation, positive Ricci, positive Einstein existence, a uniform mean floor or smooth limits. The separate existence-shaped smoothability core also remains open. Each proof is meaningful only as a constructed input of the named subsequent proof.


## Actual source Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:1-46

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.HausdorffFiniteAtlasChartFrameReduction
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) (closedSmoothModelWithCorners 3) M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) ((EuclideanSpace.basisFun (Fin 3) ℝ) a)) c

def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
```

## Actual source Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:220-254

```lean
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace

namespace Poincare.FiniteAtlasParabolicTensorSpace

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M)
```

## Actual source Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:35-90

```lean

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- A finite family of genuine extended charts whose open sources cover the
compact manifold. -/
structure FiniteExtendedChartCover where
  chartCount : ℕ
  anchor : Fin chartCount → M
  sources_cover :
    (⋃ i : Fin chartCount, (extChartAt I (anchor i)).source) = Set.univ

/-- Compactness extracts a finite subcover from the canonical extended-chart
source cover. -/
theorem exists_finiteExtendedChartCover :
    Nonempty (FiniteExtendedChartCover (n := n) (M := M)) := by
  classical
  obtain ⟨anchors, hanchors⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : M ↦ (extChartAt I x).source)
      (fun x ↦ isOpen_extChartAt_source x)
      (fun x _hx ↦ Set.mem_iUnion.mpr
        ⟨x, mem_extChartAt_source x⟩)
  refine ⟨
    { chartCount := anchors.card
      anchor := fun i ↦ (anchors.equivFin.symm i).1
      sources_cover := ?_ }⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hanchors (Set.mem_univ x))
  let a' : anchors := ⟨a, ha⟩
  refine Set.mem_iUnion.mpr ⟨anchors.equivFin a', ?_⟩
  simpa [a'] using hxa

/-- A fixed noncomputable finite extended-chart cover chosen from
compactness.  All later analytic hypotheses can be stated directly on this
canonical choice. -/
noncomputable def compactFiniteExtendedChartCover :
    FiniteExtendedChartCover (n := n) (M := M) :=
  Classical.choice exists_finiteExtendedChartCover

namespace FiniteExtendedChartCover

```

## Actual source Poincare/Global/FiniteFixedAnchorCutoffOneChartCover.lean:25-131

```lean

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The part of the preferred chart source on which the fixed anchor's
blending cutoff is locally equal to one. -/
def fixedAnchorCutoffOneChartNeighborhood (x : M) : Set M :=
  (extChartAt I x).source ∩
    (extChartAt I x) ⁻¹' {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}

omit [T2Space M] [CompactSpace M] in
/-- The fixed-anchor cutoff-one chart neighborhood is open. -/
theorem isOpen_fixedAnchorCutoffOneChartNeighborhood (x : M) :
    IsOpen (fixedAnchorCutoffOneChartNeighborhood (n := n) x) := by
  exact isOpen_extChartAt_preimage' x isOpen_setOf_eventually_nhds

omit [T2Space M] [CompactSpace M] in
/-- The anchor belongs to its fixed-anchor cutoff-one chart neighborhood. -/
theorem self_mem_fixedAnchorCutoffOneChartNeighborhood (x : M) :
    x ∈ fixedAnchorCutoffOneChartNeighborhood (n := n) x := by
  refine ⟨mem_extChartAt_source x, ?_⟩
  exact GeodesicTransport.cutoff_eventuallyEq_one (n := n) x

/-- A finite family of fixed preferred-chart anchors with precompact open
inner domains. Each inner-domain closure stays where the anchor chart is
valid and the anchor cutoff is locally one. Fixing finitely many anchors
avoids any need for joint continuity in the anchor variable. -/
structure FiniteFixedAnchorCutoffOneChartCover
    (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M] where
  anchors : Finset M
  innerDomain : ↑anchors → Set M
  isOpen_innerDomain : ∀ i, IsOpen (innerDomain i)
  anchor_mem_innerDomain : ∀ i, (i : M) ∈ innerDomain i
  closure_innerDomain_subset_cutoffOneChartNeighborhood :
    ∀ i, closure (innerDomain i) ⊆
      fixedAnchorCutoffOneChartNeighborhood (n := n) (i : M)
  innerDomain_cover : (⋃ i, innerDomain i) = Set.univ

/-- Compact Hausdorff normality shrinks every fixed-anchor cutoff-one
neighborhood, after which compactness extracts a finite subcover. -/
theorem exists_finiteFixedAnchorCutoffOneChartCover :
    Nonempty (FiniteFixedAnchorCutoffOneChartCover n M) := by
  have hshrinking : ∀ x : M, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧
        closure U ⊆ fixedAnchorCutoffOneChartNeighborhood (n := n) x := by
    intro x
    obtain ⟨U, hUopen, hxU, hUclosure⟩ :=
      normal_exists_closure_subset
        (isClosed_singleton : IsClosed ({x} : Set M))
        (isOpen_fixedAnchorCutoffOneChartNeighborhood (n := n) x)
        (Set.singleton_subset_iff.2
          (self_mem_fixedAnchorCutoffOneChartNeighborhood (n := n) x))
    exact ⟨U, hUopen, hxU (Set.mem_singleton x), hUclosure⟩
  choose U hUopen hxU hUclosure using hshrinking
  obtain ⟨anchors, hcover⟩ :=
    isCompact_univ.elim_finite_subcover U hUopen (by
      intro x _hx
      exact Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨{
    anchors := anchors
    innerDomain := fun i ↦ U (i : M)
    isOpen_innerDomain := fun i ↦ hUopen (i : M)
    anchor_mem_innerDomain := fun i ↦ hxU (i : M)
    closure_innerDomain_subset_cutoffOneChartNeighborhood :=
      fun i ↦ hUclosure (i : M)
    innerDomain_cover := ?_
  }⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx := hcover (Set.mem_univ x)
  rcases Set.mem_iUnion.1 hx with ⟨anchor, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hanchor, hxUanchor⟩
  exact Set.mem_iUnion.2 ⟨⟨anchor, hanchor⟩, hxUanchor⟩

namespace FiniteFixedAnchorCutoffOneChartCover

/-- The finite type indexing the selected fixed anchors. -/
abbrev Index (data : FiniteFixedAnchorCutoffOneChartCover n M) :=
  ↑data.anchors

/-- The compact coordinate image of one inner-domain closure. -/
def compactCoordinateSet
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) : Set E :=
  extChartAt I (i : M) '' closure (data.innerDomain i)

/-- Every selected inner-domain closure is compact. -/
theorem isCompact_closure_innerDomain
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    IsCompact (closure (data.innerDomain i)) :=
  isClosed_closure.isCompact

/-- Each compact coordinate set is compact. -/
theorem isCompact_compactCoordinateSet
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    IsCompact (data.compactCoordinateSet i) := by
```

## Actual source Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:83-112

```lean
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
```

## Actual source Poincare/Global/BufferedFrozenParabolicSolver.lean:220-250

```lean
        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
  exact oscillation_extension_entries hα hα1 (isOpen_extChartAt_target p)
    (fun x i j => (inverseChartPullbackGramMatrixField g p x)⁻¹ i j)
    (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p)
    anchor hξ hc hξU hξ01 hε hosc

/-- The genuine inverse entries have arbitrarily small oscillation at each target point. -/
theorem inverse_metric_oscillation_radius
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M) (anchor : (ClosedSmoothModel 3))
    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : (ClosedSmoothModel 3) → ℝ, tsupport ξ ⊆ Metric.ball anchor ρ →
      ∀ x ∈ tsupport ξ, ∀ i j,
        |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
          (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε := by
  apply exists_oscillation_radius _ anchor _ hε
  intro i j
  exact ((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
    anchor hanchor).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hanchor) |>.continuousAt

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Each landed coordinate support has a compact buffer in its actual chart target. -/
theorem exists_atlas_cutoff (A : FiniteAtlasParabolicTensorSpace.AtlasData M)
    (i : Fin A.cover.chartCount) :
    ∃ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧
      tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)).target ∧
      (∀ x ∈ FiniteAtlasParabolicTensorSpace.coordSupport A i,
        ∀ᶠ y in 𝓝 x, ξ y = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) := by
  exact exists_buffered_cutoff (FiniteAtlasParabolicTensorSpace.isCompact_coordSupport A i)
    (isOpen_extChartAt_target (A.cover.anchor i))
```

## Actual source Poincare/Global/BufferedFrozenParabolicSolver.lean:510-540

```lean
noncomputable section
open Set
open scoped ContDiff Topology
namespace Poincare.BufferedFrozenParabolicSolver
open ParabolicHolder ParabolicSolutionGraph

/-- Two compact buffers separate the coefficient extension from the solution cutoff. -/
theorem exists_nested_cutoffs {K U : Set (ClosedSmoothModel 3)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (U₁ : Set (ClosedSmoothModel 3)) (ψ ξ : (ClosedSmoothModel 3) → ℝ),
      IsOpen U₁ ∧ IsCompact (closure U₁) ∧ closure U₁ ⊆ U ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U₁ ∧
      (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ψ y = 1) ∧ (∀ x, ψ x ∈ Icc 0 1) ∧
      ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U ∧
      (∀ x ∈ closure U₁, ξ x = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) ∧
      (∀ x ∈ tsupport ψ, ξ x = 1) := by
  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ψ, hψ, hcψ, hψV, hψK, hψ01⟩ := exists_buffered_cutoff hK hV hKV
  obtain ⟨ξ, hξ, hcξ, hξU, hξV, hξ01⟩ := exists_buffered_cutoff hcV hU hVU
  have hone : ∀ x ∈ closure V, ξ x = 1 := fun x hx => Filter.EventuallyEq.eq_of_nhds (hξV x hx)
  exact ⟨V, ψ, ξ, hV, hcV, hVU, hψ, hcψ, hψV, hψK, hψ01,
    hξ, hcξ, hξU, hone, hξ01, fun x hx => hone x (subset_closure (hψV hx))⟩

/-- The outer extension agrees with the original entries on the inner support. -/
theorem nested_coefficient_agreement {α T : ℝ}
    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
    (ψ ξ : (ClosedSmoothModel 3) → ℝ)
    (hnest : ∀ x ∈ tsupport ψ, ξ x = 1)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) :
```

## Actual source Poincare/Global/BufferedFrozenParabolicSolver.lean:989-1024

```lean

set_option maxHeartbeats 1600000 in
/-- Construct a single-chart parametrix from smooth entries and a positive frozen matrix.
The patch oscillation is only an existence condition. After choosing the nested cutoffs,
the residual has only the two positive commutator time powers, with constants fixed
before time. The maps take values in the original unweighted derivative graph and
Hölder spaces, and the residual is identified with the actual chart operator. -/
theorem exists_single_chart_parametrix {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U)
    (a : (ClosedSmoothModel 3) → Matrix (Fin 3) (Fin 3) ℝ) (anchor : (ClosedSmoothModel 3))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (hpos : (a anchor).PosDef) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : Set (ClosedSmoothModel 3)) (ψ ξ : (ClosedSmoothModel 3) → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      (∀ x, ξ x ∈ Icc 0 1) →
      (∀ x ∈ tsupport ψ, ξ x = 1) → (∀ x ∈ K, ψ x = 1) →
      (∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε₀) →
      ∃ C_ψ C' τ₀ : ℝ, 0 ≤ C_ψ ∧ 0 ≤ C' ∧ 0 < τ₀ ∧
      ∀ T ∈ Ioc 0 τ₀,
        ∃ (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
          (R : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ),
          (∀ f p, p.2 ∉ tsupport ψ → (P f).u p = 0) ∧
          ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ,
            (∀ p, p.2 ∉ K → f p = 0) →
            (∀ p, R f p = chartValue a (P f) p - f p) ∧
            ‖R f‖ ≤ C_ψ * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ ∧
            ‖P f‖ ≤ C' * ‖f‖ := by
  obtain ⟨lam, Λell, hlam, hlamΛ, hlo, hhi⟩ := matrixBilin_ellipticity hpos
  obtain ⟨C_S, ε₀, τ, hCS, hε₀, hτ, hsolver⟩ :=
    exists_chart_operator α hα hα1 lam Λell hlam hlamΛ
  refine ⟨ε₀, hε₀, ?_⟩
  intro K ψ ξ hψ hcψ hξ hcξ hξU hξ01 hnest hone hosc
  obtain ⟨Λb, _, hext⟩ := oscillation_extension_entries hα hα1 hU a ha anchor
    hξ hcξ hξU hξ01 hε₀.le hosc
  obtain ⟨δ, hδ, hδ1, hδτ, hsmall⟩ :=
```

## Actual source Poincare/Global/GeodesicTransport.lean:87-119

```lean
  exact real_inner_comm w v

/-- A chosen cutoff supported in the anchor chart target and equal to `1` near the anchor. -/
def cutoff : E → ℝ :=
  Classical.choose (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)

omit [T2Space M] in
theorem cutoff_contDiff : ContDiff ℝ ∞ (cutoff (n := n) x₀) :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).1

omit [T2Space M] in
theorem cutoff_nonneg : ∀ z : E, 0 ≤ cutoff (n := n) x₀ z :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.1

omit [T2Space M] in
theorem cutoff_le_one : ∀ z : E, cutoff (n := n) x₀ z ≤ 1 :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.1

omit [T2Space M] in
theorem cutoff_tsupport :
    tsupport (cutoff (n := n) x₀) ⊆ (extChartAt I x₀).target :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.2.1

omit [T2Space M] in
theorem cutoff_eventuallyEq_one :
    ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀), cutoff (n := n) x₀ z = 1 :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.2.2.1

```

## Actual source Poincare/Global/DeTurckPrincipalIdentity.lean:668-682

```lean

/-- The chart evolution has inverse-metric second-derivative principal part and a uniform first-jet remainder. -/
theorem principalIdentity (bg : ClosedSmoothRiemannianMetric 3 M)
    (anchor : M) (z : E)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) anchor).target)
    (hcut : ∀ᶠ y in nhds z, GeodesicTransport.cutoff (n := 3) anchor y = 1) :
    ∃ lower : Bilin → Jet1 → Bilin,
      ∀ (g : ClosedSmoothRiemannianMetric 3 M) (v w : E),
        deTurckChartMetricEvolutionBilin (fun _ => g) bg anchor 0 z v w =
          spatialPrincipal (CovariantDerivative.chartMetric g.inner anchor) z v w +
          lower (CovariantDerivative.chartMetric g.inner anchor z)
            (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) v w := by
  let B := GeodesicTransport.chartChristoffelField bg anchor
  refine ⟨lowerTerm (B z) (fderiv ℝ B z), ?_⟩
  intro g v w
```
