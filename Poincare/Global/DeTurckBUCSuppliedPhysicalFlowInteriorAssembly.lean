import Poincare.Global.DeTurckBUCJointSpacetimeRealizationGerm
import Poincare.Global.DeTurckBUCInteriorInverseGaugeEvolution
import Poincare.Global.DeTurckBUCInteriorRicciAssembly

/-!
# Interior assembly for a supplied physical inverse DeTurck point flow

The existing positive-time inverse-gauge theorem constructs a fresh point
trajectory restarted at the time under consideration.  Global chartwise
metric assembly, however, realizes a caller-supplied physical endpoint family
`Phi` and its spatial differential `DPhi`.  This file connects those two
interfaces without identifying the supplied family with an unrelated choice.

The first theorem applies the arbitrary-time inverse-gauge calculation
directly to the supplied trajectory through one initial coordinate point.
The second combines that coordinate Ricci germ with exact chart realization.
The still-geometric curvature-locality comparison is kept as an explicit
hypothesis; exact equality of metric values alone is not silently treated as
an equality of curvature.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- At a strict interior time, a caller-supplied physical inverse DeTurck
endpoint trajectory and its variational differential produce the same genuine
two-sided coordinate Ricci-flow germ as the abstract arbitrary-time pullback
theorem.

The temporal point-flow equation, variational equation, invertibility, local
cutoff control, coefficient germ, and Ricci--DeTurck coefficient identity are
all explicit premises. -/
theorem exists_reconstructed_suppliedPhysicalPointFlow_with_RicciFlowAt_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y₁ : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan
        K : ℝ))
    (hy₁ : y₁ ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y₁),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (Phi : ℝ → E → E)
    (DPhi : ℝ → E → E →L[ℝ] E)
    (z₀ : E)
    (hendpoint : Phi t z₀ = extChartAt I anchor y₁)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[
            nhds (Phi t z₀)]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorGeneratorValue
              K u₀ t +
            D.base.nonlinearity
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                  K u₀ t +
                D.background))
          (Phi t z₀) =
        deTurckChartMetricEvolutionBilin gt bg anchor t (Phi t z₀))
    (hPhiTime : HasDerivAt (fun s : ℝ ↦ Phi s z₀)
      (inverseDeTurckChartCoordinateField gt bg anchor t (Phi t z₀)) t)
    (hDPhiTime : HasDerivAt (fun s : ℝ ↦ DPhi s z₀)
      (-(deTurckChartFieldDerivativeAt gt bg anchor t (Phi t z₀)).comp
        (DPhi t z₀)) t)
    (hDPhiInv : (DPhi t z₀).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 (Phi t) z₀)
    (hPhiD : HasFDerivAt (Phi t) (DPhi t z₀) z₀) :
    ∃ G : CoordinateLocalDiffeomorphGerm (Phi t) z₀ (DPhi t z₀),
      G.localHomeomorph z₀ = Phi t z₀ ∧
        reconstructedInverseGaugeMetric D K u₀
            (fun s : ℝ ↦ Phi s z₀) (fun s : ℝ ↦ DPhi s z₀) t =
          pullbackBilinearForm
            (CovariantDerivative.chartMetric (gt t).inner anchor (Phi t z₀))
            (G.tangentEquiv : E →L[ℝ] E) ∧
        IsCoordinateRicciFlowAt
          (reconstructedInverseGaugeMetric D K u₀
            (fun s : ℝ ↦ Phi s z₀) (fun s : ℝ ↦ DPhi s z₀))
          (pullbackCurvatureEnd G.tangentEquiv
            (chartRicciCurvatureEndAt (gt t) anchor
              (extChartAt I anchor y₁)
              ((extChartAt I anchor).map_source hy₁))) t := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let g' : CoordinateBUCTensor E :=
    A.uniformInteriorGeneratorValue K u₀ t +
      D.base.nonlinearity (A.uniformInteriorState K u₀ t + D.background)
  have hg : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) g' t := by
    simpa only [A, g'] using
      reconstructedCoordinateMetricPath_hasDerivAt_interior_automatic
        D K u₀ ht₀ htT
  have hfullGerm' :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[
            nhds ((fun s : ℝ ↦ Phi s z₀) t)]
        CovariantDerivative.chartMetric (gt t).inner anchor := by
    simpa only using hfullGerm
  have hidentifyRHS' :
      coordinateBilinearFormAt g' ((fun s : ℝ ↦ Phi s z₀) t) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          ((fun s : ℝ ↦ Phi s z₀) t) := by
    simpa only [g', A] using hidentifyRHS
  rcases
      exists_reconstructed_coordinateLocalDiffeomorphGerm_with_RicciFlowAt
        D K u₀ gt bg anchor hy₁ hχone
        (fun s : ℝ ↦ Phi s z₀) (fun s : ℝ ↦ DPhi s z₀)
        (Phi t) z₀ hendpoint (by rfl) hg hfullGerm' hidentifyRHS'
        hPhiTime hDPhiTime hDPhiInv hPhiC1 hPhiD
        (deTurckVectorFieldRegularAt_holds gt bg t) with
    ⟨G, hG, hmetric, hflow⟩
  refine ⟨G, hG, ?_, ?_⟩
  · simpa only using hmetric
  · have hzPhi : Phi t z₀ ∈ (extChartAt I anchor).target := by
      rw [hendpoint]
      exact (extChartAt I anchor).map_source hy₁
    have hcurv :
        chartRicciCurvatureEndAt (gt t) anchor (Phi t z₀) hzPhi =
          chartRicciCurvatureEndAt (gt t) anchor
            (extChartAt I anchor y₁)
            ((extChartAt I anchor).map_source hy₁) :=
      chartRicciCurvatureEndAt_congr (gt t) anchor hzPhi
        ((extChartAt I anchor).map_source hy₁) hendpoint
    simpa only [hcurv] using hflow

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Exact chartwise realization turns the supplied physical point-flow Ricci
germ into the intrinsic closed Ricci-flow equation at the represented initial
manifold point.

The curvature-rate premise is the honest remaining spatial locality boundary:
it compares the pulled source curvature supplied by the inverse-gauge theorem
with the Ricci tensor of the assembled metric. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_chartwiseRealization
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y₀ y₁ : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor)).uniformLifespan K : ℝ))
    (hy₀ : y₀ ∈ (extChartAt I anchor).source)
    (hy₁ : y₁ ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y₁),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hendpoint :
      Phi anchor t (extChartAt I anchor y₀) = extChartAt I anchor y₁)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath
            (D anchor) K (u₀ anchor) t) z') =ᶠ[
            nhds (Phi anchor t (extChartAt I anchor y₀))]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
              (D anchor)).uniformInteriorGeneratorValue K (u₀ anchor) t +
            (D anchor).base.nonlinearity
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
                  (D anchor)).uniformInteriorState K (u₀ anchor) t +
                (D anchor).background))
          (Phi anchor t (extChartAt I anchor y₀)) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          (Phi anchor t (extChartAt I anchor y₀)))
    (hPhiTime : HasDerivAt
      (fun s : ℝ ↦ Phi anchor s (extChartAt I anchor y₀))
      (inverseDeTurckChartCoordinateField gt bg anchor t
        (Phi anchor t (extChartAt I anchor y₀))) t)
    (hDPhiTime : HasDerivAt
      (fun s : ℝ ↦ DPhi anchor s (extChartAt I anchor y₀))
      (-(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t (extChartAt I anchor y₀))).comp
        (DPhi anchor t (extChartAt I anchor y₀))) t)
    (hDPhiInv :
      (DPhi anchor t (extChartAt I anchor y₀)).IsInvertible)
    (hPhiC1 : ContDiffAt ℝ 1 (Phi anchor t)
      (extChartAt I anchor y₀))
    (hPhiD : HasFDerivAt (Phi anchor t)
      (DPhi anchor t (extChartAt I anchor y₀))
      (extChartAt I anchor y₀))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z)
    (hcurvatureRate : ∀ e : E ≃L[ℝ] E,
      e.toContinuousLinearMap =
          DPhi anchor t (extChartAt I anchor y₀) →
      ∀ p q : E,
        (-2 : ℝ) * LinearMap.trace ℝ E
            (pullbackCurvatureEnd e
              (chartRicciCurvatureEndAt (gt t) anchor
                (extChartAt I anchor y₁)
                ((extChartAt I anchor).map_source hy₁)) p q) =
          CovariantDerivative.chartMetric
            (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) z)
            anchor (extChartAt I anchor y₀) p q) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  rcases
      exists_reconstructed_suppliedPhysicalPointFlow_with_RicciFlowAt_interior
        (D anchor) K (u₀ anchor) gt bg anchor ht₀ htT hy₁ hχone
        (Phi anchor) (DPhi anchor) z₀
        (by simpa only [z₀] using hendpoint)
        (by simpa only [z₀] using hfullGerm)
        (by simpa only [z₀] using hidentifyRHS)
        (by simpa only [z₀] using hPhiTime)
        (by simpa only [z₀] using hDPhiTime)
        (by simpa only [z₀] using hDPhiInv)
        (by simpa only [z₀] using hPhiC1)
        (by simpa only [z₀] using hPhiD) with
    ⟨G, _hG, _hsourceMetric, hflow⟩
  have hz₀ : z₀ ∈ (extChartAt I anchor).target := by
    simpa only [z₀] using (extChartAt I anchor).map_source hy₀
  have hmetric : ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        (D anchor) K (u₀ anchor)
        (fun tau : ℝ ↦ Phi anchor tau z₀)
        (fun tau : ℝ ↦ DPhi anchor tau z₀) s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀ p q) := by
    exact
      reconstructedInverseGaugeMetric_eventuallyEq_chartMetric_of_chartwiseRealization
        rt D K u₀ Phi DPhi anchor (t := t) (z₀ := z₀)
          hz₀ hrealize
  apply isClosedRicciFlowSolutionAt_of_reconstructedInverseGaugeMetric_germ
    (D anchor) K (u₀ anchor)
    (fun s : ℝ ↦ Phi anchor s z₀)
    (fun s : ℝ ↦ DPhi anchor s z₀)
    rt anchor hy₀
    (pullbackCurvatureEnd G.tangentEquiv
      (chartRicciCurvatureEndAt (gt t) anchor
        (extChartAt I anchor y₁)
        ((extChartAt I anchor).map_source hy₁)))
    hflow
  · intro p q
    exact hcurvatureRate G.tangentEquiv
      (by simpa only [z₀] using G.tangentEquiv_coe) p q
  · simpa only [z₀] using hmetric

end Poincare
