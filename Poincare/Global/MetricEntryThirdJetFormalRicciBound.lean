import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.MetricEntryThirdJetAnchorLowerComparison
import Poincare.Global.NormalizedFlowEnergyConcentrationCurvatureDerivative

/-!
# Global covariant-Ricci bounds from compact formal profiles

The finite fixed-anchor cover turns the chartwise formal bound into an
intrinsic bound on the whole compact manifold.  The only residual analytic
premise is invertibility of every reconstructed formal metric on the finite
family of compact coordinate sets.  Smooth realization of profile limits is
not required.
-/

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "E" => ClosedSmoothModel 3
local notation "G" => ClosedSmoothRiemannianMetric 3 M
local notation "P" => MetricEntryThirdJetProfileTarget 3 M

/-- Compact scalar third-jet profile closure and formal invertibility on the
finite fixed-chart cover give a global intrinsic `|∇ Ric|` bound for the
original metric family. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_formal_invertibility
    {J : Type v} (gt : J → G)
    (data : FiniteFixedAnchorCutoffOneChartCover 3 M)
    (hProfileCompact : IsCompact
      (closure (Set.range
        (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt))))
    (hnd : ∀ i : data.Index,
      ∀ p ∈ closure (Set.range
        (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt)),
      ∀ z ∈ data.compactCoordinateSet i,
        (formalProfileMetricAt p (i : M) z).IsInvertible) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  have hChart : ∀ i : data.Index, ∃ C : ℝ,
      ∀ t : J, ∀ z ∈ data.compactCoordinateSet i,
        anchorChartCovRicciNormSqFamily gt (i : M) t z ≤ C := by
    intro i
    exact
      exists_uniformAnchorChartCovRicciNormSqFamilyBound_of_compact_profileClosure
        gt (i : M) hProfileCompact
        (data.isCompact_compactCoordinateSet i) (hnd i)
  choose C hC using hChart
  let S : ℝ := ∑ i : data.Index, |C i|
  let D : ℝ := S + 1
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _hi => abs_nonneg (C i))
  have hDpos : 0 < D := by
    dsimp [D]
    linarith
  refine ⟨D, hDpos, ?_⟩
  intro t y
  obtain ⟨i, _hyDomain, _hySource, hyCoordinate, hIntrinsic⟩ :=
    data.exists_chart_anchorCovRicciNormSqFamily_eq_intrinsic gt t y
  have hCiS : C i ≤ S := by
    calc
      C i ≤ |C i| := le_abs_self (C i)
      _ ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum
          (fun j _hj => abs_nonneg (C j)) (Finset.mem_univ i)
  have hDSq : S ≤ D ^ 2 := by
    have hDone : 1 ≤ D := by
      dsimp [D]
      linarith
    have hDle : D ≤ D ^ 2 := by
      nlinarith
    dsimp [D] at hDle ⊢
    linarith
  calc
    covRicciNormSqAt (gt t) y =
        anchorChartCovRicciNormSqFamily gt (i : M) t
          (extChartAt (closedSmoothModelWithCorners 3) (i : M) y) :=
      hIntrinsic.symm
    _ ≤ C i := hC i t _ hyCoordinate
    _ ≤ S := hCiS
    _ ≤ D ^ 2 := hDSq

/-- A positive lower comparison on each selected fixed chart discharges the
formal-invertibility premise and yields the same global intrinsic bound. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_anchor_lower
    {J : Type v} (gt : J → G)
    (data : FiniteFixedAnchorCutoffOneChartCover 3 M)
    (hProfileCompact : IsCompact
      (closure (Set.range
        (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt))))
    (c : data.Index → ℝ)
    (hLower : ∀ i : data.Index,
      UniformAnchorBlendedMetricLowerComparison gt (i : M)
        (data.compactCoordinateSet i) (c i)) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D :=
  exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_formal_invertibility
    gt data hProfileCompact
    (fun i p hp z hz =>
      formalProfileMetricAt_isInvertible_of_mem_closure
        gt (i : M) (c i) (hLower i) (p := p) hp (z := z) hz)

/-- Compact scalar-profile closure and one uniform intrinsic lower comparison
with a genuine reference metric suffice for the global covariant-Ricci bound.
The finite fixed-chart lower bounds are produced automatically. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_closedMetricLower
    {J : Type v} (gt : J → G)
    (data : FiniteFixedAnchorCutoffOneChartCover 3 M)
    (hProfileCompact : IsCompact
      (closure (Set.range
        (metricEntryThirdJetProfile (n := 3) (M := M) ∘ gt))))
    (gref : G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  have hChart : ∀ i : data.Index, ∃ d : ℝ,
      UniformAnchorBlendedMetricLowerComparison gt (i : M)
        (data.compactCoordinateSet i) d := by
    intro i
    exact
      exists_uniformAnchorBlendedMetricLowerComparison_of_closedMetricLowerComparison
        gref gt c hLower (i : M) (data.isCompact_compactCoordinateSet i)
  choose d hd using hChart
  exact
    exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_anchor_lower
      gt data hProfileCompact d hd

/-- Componentwise Arzela--Ascoli compactness and one uniform intrinsic metric
lower comparison give the full covariant-Ricci derivative bound without any
smooth-realization premise for profile limits. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_componentwise_and_closedMetricLower
    {J : Type v} (gt : J → G)
    (data : FiniteFixedAnchorCutoffOneChartCover 3 M)
    (hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : J =>
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseCompact : ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : E),
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ t : J, metricEntryThirdJetProfile (gt t) slot z ∈ Q)
    (gref : G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D :=
  exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_closedMetricLower
    gt data
      (isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise
        gt hequicontinuous hpointwiseCompact)
    gref c hLower

/-- Pointwise boundedness supplies the compact pointwise sets in the preceding
no-realization theorem. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_componentwise_bounded_and_closedMetricLower
    {J : Type v} (gt : J → G)
    (data : FiniteFixedAnchorCutoffOneChartCover 3 M)
    (hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : J =>
        (metricEntryThirdJetProfile (gt t) slot : E → ℝ)))
    (hpointwiseBounded : ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : E),
      Bornology.IsBounded (Set.range
        (fun t : J => metricEntryThirdJetProfile (gt t) slot z)))
    (gref : G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D :=
  exists_uniformCovariantRicciDerivativeNormBound_of_compact_profileClosure_and_closedMetricLower
    gt data
      (isCompact_closure_range_metricEntryThirdJetProfile_of_componentwise_bounded
        gt hequicontinuous hpointwiseBounded)
    gref c hLower

end Poincare
