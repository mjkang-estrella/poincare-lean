import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowChartMetricRegularityAssembly
import Poincare.Global.GeodesicDependence

/-!
# Automatic Christoffel regularity in supplied physical-flow assembly

The anchor Christoffel field is built from the globally smooth blended chart
metric, so it is `C¹` at every chart coordinate.  Consequently the two
pointwise Christoffel derivative premises in curvature assembly are
automatic; cutoff-one germs are still retained only where they identify the
blended field with the genuine transported chart metric.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section AnchorChristoffelRegularity

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

set_option synthInstance.maxHeartbeats 1000000 in
/-- The fixed-time anchor Christoffel field has its canonical Fréchet
derivative at every model-space point. -/
theorem anchorChartChristoffelFieldFlow_hasFDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) (z : E) :
    HasFDerivAt
      (anchorChartChristoffelFieldFlow gt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow gt anchor t) z) z := by
  have hΓ : ContDiffAt ℝ 1
      (anchorChartChristoffelFieldFlow gt anchor t) z := by
    simpa only [anchorChartChristoffelFieldFlow] using
      (GeodesicTransport.chartChristoffelField_contDiffAt_base
        (g := gt t) (x₀ := anchor) z)
  exact (hΓ.differentiableAt (by norm_num)).hasFDerivAt

end AnchorChristoffelRegularity

section AutomaticChristoffelSuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow assembly with both source and target Christoffel
derivative premises generated from global blended-chart regularity. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_automaticChristoffelRegularity
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
    (hχ₀ : ∀ᶠ z' in nhds (extChartAt I anchor y₀),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hχ₁ : ∀ᶠ z' in nhds (extChartAt I anchor y₁),
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
    (hPhiC1 : ContDiffAt ℝ 1 (Phi anchor t)
      (extChartAt I anchor y₀))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z)
    (B : E → E →L[ℝ] E →L[ℝ] E)
    (hPhiSpaceNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      HasFDerivAt (Phi anchor t) (DPhi anchor t q) q)
    (hDPhiSpaceNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      HasFDerivAt (DPhi anchor t) (B q) q)
    (hBSpace : HasFDerivAt B
      (fderiv ℝ B (extChartAt I anchor y₀))
      (extChartAt I anchor y₀))
    (hDPhiInvNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      (DPhi anchor t q).IsInvertible)
    (hBsymmNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      ∀ a b : E, (B q a) b = (B q b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B (extChartAt I anchor y₀) a) b) c =
        ((fderiv ℝ B (extChartAt I anchor y₀) c) b) a) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  have hChristoffelRt : HasFDerivAt
      (anchorChartChristoffelFieldFlow rt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow rt anchor t)
        (extChartAt I anchor y₀))
      (extChartAt I anchor y₀) :=
    anchorChartChristoffelFieldFlow_hasFDerivAt
      rt anchor t (extChartAt I anchor y₀)
  have hChristoffelGt : HasFDerivAt
      (anchorChartChristoffelFieldFlow gt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow gt anchor t)
        (Phi anchor t (extChartAt I anchor y₀)))
      (Phi anchor t (extChartAt I anchor y₀)) :=
    anchorChartChristoffelFieldFlow_hasFDerivAt
      gt anchor t (Phi anchor t (extChartAt I anchor y₀))
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_automaticChartMetricRegularity
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hPhiC1 hrealize
        B hPhiSpaceNear hDPhiSpaceNear hBSpace hChristoffelRt hChristoffelGt
        hDPhiInvNear hBsymmNear hCsymm

end AutomaticChristoffelSuppliedFlowAssembly

end Poincare
