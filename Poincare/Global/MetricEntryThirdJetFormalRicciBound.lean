import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.MetricEntryThirdJetFormalInvertibility
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

end Poincare
