import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowMetricPullbackAssembly

/-!
# Automatic chart-metric regularity in supplied physical-flow assembly

The metric-pullback assembly only uses chart metrics at points in the target
of the fixed inverse chart.  Smoothness and Riemannian positivity therefore
supply their Fréchet derivatives and algebraic nondegeneracy automatically.
This removes four technical premises from the supplied-flow wrapper.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

set_option linter.unusedSectionVars false

section ChartMetricTargetRegularity

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- A smooth Riemannian metric has `C¹` bilinear-form-valued chart entries at
every point of the inverse-chart target. -/
theorem chartMetric_contDiffAt_one_of_mem_extChartAt_target
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) :
    ContDiffAt ℝ 1 (CovariantDerivative.chartMetric g.inner anchor) z := by
  have hone_le_top : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) = ((1 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hone_add_one_le_top : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (1 : ℕ∞ω) + 1 = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg₁ :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
        (fun y : M ↦
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦
                TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hone_le_top
  apply Poincare.contDiffAt_clm_of_apply
  intro v
  apply Poincare.contDiffAt_clm_of_apply
  intro w
  have hscalar :=
    CovariantDerivative.contMDiffOn_chartMetric_pairing
      g.inner anchor hone_add_one_le_top hg₁ v w z hz
  exact
    contMDiffAt_iff_contDiffAt.mp
      (hscalar.contMDiffAt ((isOpen_extChartAt_target anchor).mem_nhds hz))

/-- Canonical Fréchet derivative of the chart metric on the inverse-chart
target. -/
theorem chartMetric_hasFDerivAt_of_mem_extChartAt_target
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) :
    HasFDerivAt
      (CovariantDerivative.chartMetric g.inner anchor)
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) z :=
  ((chartMetric_contDiffAt_one_of_mem_extChartAt_target g anchor hz).differentiableAt
    (by norm_num)).hasFDerivAt

/-- Riemannian positivity makes the algebraic form underlying a chart metric
nondegenerate throughout the inverse-chart target. -/
theorem continuousBilinForm_chartMetric_nondegenerate_of_mem_extChartAt_target
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) :
    (continuousBilinForm
      (CovariantDerivative.chartMetric g.inner anchor z)).Nondegenerate := by
  have hgnd :
      ∀ (y : M) (v : TangentSpace I y),
        (∀ w, g.inner y v w = 0) → v = 0 := by
    intro y v hv
    by_contra hvne
    exact (ne_of_gt (g.inner_pos y hvne)) (hv v)
  have hinv := isInvertible_mfderivWithin_extChartAt_symm hz
  have hleft :
      ∀ v : E,
        (∀ w, CovariantDerivative.chartMetric g.inner anchor z v w = 0) →
          v = 0 :=
    CovariantDerivative.chartMetric_nondegenerate g.inner hgnd anchor hinv
  constructor
  · intro v hv
    apply hleft v
    intro w
    simpa only [continuousBilinForm_apply] using hv w
  · intro v hv
    apply hleft v
    intro w
    rw [CovariantDerivative.chartMetric_symm g.inner
      (fun y a b ↦ g.inner_symm y a b)]
    simpa only [continuousBilinForm_apply] using hv w

end ChartMetricTargetRegularity

section AutomaticChartMetricSuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow metric-pullback assembly with chart-metric
derivatives and nondegeneracy generated automatically from target membership.

Continuity of the supplied endpoint map and the endpoint identity keep its
nearby image in the same inverse-chart target, so no extra target-membership
premise is required. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_automaticChartMetricRegularity
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
    (hDPhiInvNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      (DPhi anchor t q).IsInvertible)
    (hBsymmNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      ∀ a b : E, (B q a) b = (B q b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B (extChartAt I anchor y₀) a) b) c =
        ((fderiv ℝ B (extChartAt I anchor y₀) c) b) a) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  have hPhiD : HasFDerivAt (Phi anchor t) (DPhi anchor t z₀) z₀ := by
    exact hPhiSpaceNear.self_of_nhds
  have hz₀ : z₀ ∈ (extChartAt I anchor).target := by
    simpa only [z₀] using (extChartAt I anchor).map_source hy₀
  have hPhiTarget :
      Phi anchor t z₀ ∈ (extChartAt I anchor).target := by
    rw [show Phi anchor t z₀ = extChartAt I anchor y₁ by
      simpa only [z₀] using hendpoint]
    exact (extChartAt I anchor).map_source hy₁
  have hsourceTargetNear : ∀ᶠ q in nhds z₀,
      q ∈ (extChartAt I anchor).target :=
    (isOpen_extChartAt_target anchor).mem_nhds hz₀
  have hPhiTargetNear : ∀ᶠ q in nhds z₀,
      Phi anchor t q ∈ (extChartAt I anchor).target :=
    hPhiD.continuousAt
      ((isOpen_extChartAt_target anchor).mem_nhds hPhiTarget)
  have hMetricRtNear : ∀ᶠ q in nhds z₀,
      HasFDerivAt
        (CovariantDerivative.chartMetric (rt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (rt t).inner anchor) q) q := by
    filter_upwards [hsourceTargetNear] with q hq
    exact chartMetric_hasFDerivAt_of_mem_extChartAt_target (rt t) anchor hq
  have hMetricGtNear : ∀ᶠ q in nhds z₀,
      HasFDerivAt
        (CovariantDerivative.chartMetric (gt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
          (Phi anchor t q)) (Phi anchor t q) := by
    filter_upwards [hPhiTargetNear] with q hq
    exact chartMetric_hasFDerivAt_of_mem_extChartAt_target (gt t) anchor hq
  have hMetricRtNondegNear : ∀ᶠ q in nhds z₀,
      (continuousBilinForm
        (CovariantDerivative.chartMetric (rt t).inner anchor q)).Nondegenerate := by
    filter_upwards [hsourceTargetNear] with q hq
    exact
      continuousBilinForm_chartMetric_nondegenerate_of_mem_extChartAt_target
        (rt t) anchor hq
  have hMetricGtNondegNear : ∀ᶠ q in nhds z₀,
      (continuousBilinForm
        (CovariantDerivative.chartMetric (gt t).inner anchor
          (Phi anchor t q))).Nondegenerate := by
    filter_upwards [hPhiTargetNear] with q hq
    exact
      continuousBilinForm_chartMetric_nondegenerate_of_mem_extChartAt_target
        (gt t) anchor hq
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_metricPullbackGerm
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hPhiC1 hrealize
        B hPhiSpaceNear hDPhiSpaceNear hBSpace hChristoffelRt hChristoffelGt
        (by simpa only [z₀] using hMetricRtNear)
        (by simpa only [z₀] using hMetricGtNear)
        hDPhiInvNear hBsymmNear hCsymm
        (by simpa only [z₀] using hMetricRtNondegNear)
        (by simpa only [z₀] using hMetricGtNondegNear)

end AutomaticChartMetricSuppliedFlowAssembly

end Poincare
