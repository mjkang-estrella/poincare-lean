import Poincare.Global.DeTurckBUCCurvatureRateLocality

/-!
# Curvature-local supplied physical-flow assembly

The supplied physical-flow theorem formerly accepted a scalar
`hcurvatureRate` premise.  The first theorem below replaces that opaque rate
boundary by the tensorial chart-curvature naturality statement from which the
rate follows.

The second theorem obtains tensorial curvature naturality from a germwise
signed Christoffel transition.  Its hypotheses keep the remaining spatial
regularity boundary honest: the endpoint map has a second spatial derivative
field `B`, that field is differentiable once more, both Christoffel fields are
differentiable, and the Hessian/third-derivative symmetries are explicit.
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
/-- Tensorial chart-curvature naturality discharges the curvature-rate premise
in supplied physical-flow assembly.  The source and target cutoff-one germs
are exactly the locality zones needed to identify chart curvature with the
intrinsic curvature endomorphism before taking its trace. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_chartCurvatureNatural
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
    (hcurvatureNatural : ∀ e : E ≃L[ℝ] E,
      e.toContinuousLinearMap =
          DPhi anchor t (extChartAt I anchor y₀) →
      ∀ u v w : E,
        anchorChartCurvatureFlow gt anchor t
            (extChartAt I anchor y₁) (e u) (e v) (e w) =
          e (anchorChartCurvatureFlow rt anchor t
            (extChartAt I anchor y₀) u v w)) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_chartwiseRealization
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hDPhiInv
        hPhiC1 hPhiD hrealize
  intro e he p q
  exact
    neg_two_trace_pullbackCurvatureEnd_eq_chartMetric_neg_two_ricci_of_chartCurvatureNatural
      rt gt anchor t
        ((extChartAt I anchor).map_source hy₀)
        ((extChartAt I anchor).map_source hy₁)
        hχ₀ hχ₁ e (hcurvatureNatural e he) p q

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- A spatial signed-Christoffel germ, together with explicit second- and
third-derivative data for the supplied endpoint map, implies the intrinsic
closed Ricci-flow equation at every strict interior time represented by the
input data. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_signedChristoffelGerm
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
    (B : E → E →L[ℝ] E →L[ℝ] E)
    (hDPhiSpace : HasFDerivAt (DPhi anchor t)
      (B (extChartAt I anchor y₀)) (extChartAt I anchor y₀))
    (hBSpace : HasFDerivAt B
      (fderiv ℝ B (extChartAt I anchor y₀))
      (extChartAt I anchor y₀))
    (hChristoffelRt : HasFDerivAt
      (anchorChartChristoffelFieldFlow rt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow rt anchor t)
        (extChartAt I anchor y₀))
      (extChartAt I anchor y₀))
    (hChristoffelGt : HasFDerivAt
      (anchorChartChristoffelFieldFlow gt anchor t)
      (fderiv ℝ (anchorChartChristoffelFieldFlow gt anchor t)
        (Phi anchor t (extChartAt I anchor y₀)))
      (Phi anchor t (extChartAt I anchor y₀)))
    (hBsymm : ∀ a b : E,
      (B (extChartAt I anchor y₀) a) b =
        (B (extChartAt I anchor y₀) b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B (extChartAt I anchor y₀) a) b) c =
        ((fderiv ℝ B (extChartAt I anchor y₀) c) b) a)
    (htransition : ∀ a b : E,
      (fun q : E ↦ anchorChartChristoffelFieldFlow gt anchor t
          (Phi anchor t q) (DPhi anchor t q a) (DPhi anchor t q b)) =ᶠ[
            nhds (extChartAt I anchor y₀)]
        (fun q : E ↦ DPhi anchor t q
            (anchorChartChristoffelFieldFlow rt anchor t q a b) -
          (B q b) a)) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_chartCurvatureNatural
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hDPhiInv
        hPhiC1 hPhiD hrealize
  intro e he u v w
  change
    anchorChartCurvatureFlow gt anchor t (extChartAt I anchor y₁)
        (e.toContinuousLinearMap u) (e.toContinuousLinearMap v)
        (e.toContinuousLinearMap w) =
      e.toContinuousLinearMap
        (anchorChartCurvatureFlow rt anchor t
          (extChartAt I anchor y₀) u v w)
  rw [he]
  rw [← hendpoint]
  exact
    anchorChartCurvatureFlow_natural_of_signedChristoffelGerm
      rt gt anchor t (Phi anchor t) (DPhi anchor t) B
        hPhiD hDPhiSpace hBSpace hChristoffelRt hChristoffelGt
        hBsymm hCsymm htransition u v w

end Poincare
