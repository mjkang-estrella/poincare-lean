import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowCurvatureAssembly
import Poincare.Global.GeodesicReanchor

/-!
# Metric-pullback curvature assembly for the supplied physical flow

A metric-pullback identity at one base point is not by itself enough to
differentiate Christoffel symbols there: the identity must hold as a germ at
each nearby point.  This file performs the needed open-neighborhood
refinement.  A single tensor-valued `EventuallyEq` is restricted to an open
set on which it holds pointwise; every point of that open set then inherits
the same identity as a neighborhood germ.

Under explicit nearby derivative, invertibility, nondegeneracy, and Hessian
symmetry hypotheses, Levi-Civita naturality turns those local metric germs
into the signed Christoffel germ consumed by curvature assembly.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

set_option linter.unusedSectionVars false

section ContinuousBilinearForm

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forget the topology on a continuous bilinear form while preserving both
linear slots. -/
def continuousBilinForm (G : E →L[ℝ] E →L[ℝ] ℝ) :
    LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w ↦ G v w)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)

@[simp] theorem continuousBilinForm_apply
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    continuousBilinForm G v w = G v w :=
  rfl

end ContinuousBilinearForm

section RawChristoffelIdentification

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

/-- On a cutoff-one germ, the actual anchor-chart Christoffel field is the
raw `christoffelAt` corrector of the genuine chart metric.  This is the
all-slots version of the diagonal coefficient bridge used by the geodesic
transition construction. -/
theorem anchorChartChristoffelFieldFlow_eq_christoffelAt_of_cutoffGerm
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ) {z : E}
    (hcut : ∀ᶠ q in nhds z,
      GeodesicTransport.cutoff (n := n) anchor q = 1)
    (hb : (continuousBilinForm
      (CovariantDerivative.chartMetric (gt t).inner anchor z)).Nondegenerate)
    (u v : E) :
    anchorChartChristoffelFieldFlow gt anchor t z u v =
      CovariantDerivative.christoffelAt
        (CovariantDerivative.chartMetric (gt t).inner anchor)
        z
        (continuousBilinForm
          (CovariantDerivative.chartMetric (gt t).inner anchor z))
        hb v u := by
  change GeodesicTransport.chartChristoffelField (gt t) anchor z u v = _
  apply sub_eq_zero.mp
  apply hb.1
  intro w
  simp only [map_sub, LinearMap.sub_apply, continuousBilinForm_apply]
  rw [GeodesicTransport.chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    (g := gt t) (x₀ := anchor) hcut]
  have hchrist :=
    CovariantDerivative.b_christoffelAt
      (CovariantDerivative.chartMetric (gt t).inner anchor)
      z
      (continuousBilinForm
        (CovariantDerivative.chartMetric (gt t).inner anchor z))
      hb v u w
  rw [show
      CovariantDerivative.chartMetric (gt t).inner anchor z
          (CovariantDerivative.christoffelAt
            (CovariantDerivative.chartMetric (gt t).inner anchor)
            z
            (continuousBilinForm
              (CovariantDerivative.chartMetric (gt t).inner anchor z))
            hb v u) w =
        (1 / 2 : ℝ) *
          ((fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor) z v) u w +
            (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor) z u) v w -
            (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor) z w) v u) by
      simpa only [continuousBilinForm_apply] using hchrist]
  ring

end RawChristoffelIdentification

section OpenMetricPullbackRefinement

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Promote one tensor-valued metric-pullback germ to a signed Christoffel
transition germ.

The open refinement is essential: at every nearby `q`, it supplies a full
metric-pullback germ at `q`, rather than merely the equality of metric values
at `q`. -/
theorem anchorChartChristoffelFieldFlow_signedTransition_of_metricPullbackGerm
    (rt gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (t : ℝ)
    (F : E → E) (D : E → E →L[ℝ] E)
    (B : E → E →L[ℝ] E →L[ℝ] E) {z : E}
    (hpull :
      (fun q : E ↦ pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt t).inner anchor (F q))
          (D q)) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (rt t).inner anchor)
    (hFnear : ∀ᶠ q in nhds z, HasFDerivAt F (D q) q)
    (hDnear : ∀ᶠ q in nhds z, HasFDerivAt D (B q) q)
    (hG₀near : ∀ᶠ q in nhds z,
      HasFDerivAt
        (CovariantDerivative.chartMetric (rt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (rt t).inner anchor) q) q)
    (hG₁near : ∀ᶠ q in nhds z,
      HasFDerivAt
        (CovariantDerivative.chartMetric (gt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
          (F q)) (F q))
    (hDinvNear : ∀ᶠ q in nhds z, (D q).IsInvertible)
    (hBsymmNear : ∀ᶠ q in nhds z,
      ∀ a b : E, (B q a) b = (B q b) a)
    (hb₀Near : ∀ᶠ q in nhds z,
      (continuousBilinForm
        (CovariantDerivative.chartMetric (rt t).inner anchor q)).Nondegenerate)
    (hb₁Near : ∀ᶠ q in nhds z,
      (continuousBilinForm
        (CovariantDerivative.chartMetric (gt t).inner anchor (F q))).Nondegenerate)
    (hcut₀Near : ∀ᶠ q in nhds z,
      ∀ᶠ r in nhds q,
        GeodesicTransport.cutoff (n := n) anchor r = 1)
    (hcut₁Near : ∀ᶠ q in nhds z,
      ∀ᶠ r in nhds (F q),
        GeodesicTransport.cutoff (n := n) anchor r = 1) :
    ∀ a b : E,
      (fun q : E ↦ anchorChartChristoffelFieldFlow gt anchor t
          (F q) (D q a) (D q b)) =ᶠ[nhds z]
        (fun q : E ↦ D q
            (anchorChartChristoffelFieldFlow rt anchor t q a b) -
          (B q b) a) := by
  have hpullSet :
      {q : E | pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt t).inner anchor (F q))
          (D q) =
        CovariantDerivative.chartMetric (rt t).inner anchor q} ∈ nhds z :=
    hpull
  rcases mem_nhds_iff.mp hpullSet with ⟨U, hUsub, hUopen, hzU⟩
  intro a b
  filter_upwards [hUopen.mem_nhds hzU, hFnear, hDnear, hG₀near,
    hG₁near, hDinvNear, hBsymmNear, hb₀Near, hb₁Near,
    hcut₀Near, hcut₁Near] with q hqU hFq hDq hG₀q hG₁q hDinvq
      hBsymmq hb₀q hb₁q hcut₀q hcut₁q
  have hpullq :
      (fun r : E ↦ pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt t).inner anchor (F r))
          (D r)) =ᶠ[nhds q]
        CovariantDerivative.chartMetric (rt t).inner anchor := by
    exact mem_nhds_iff.mpr ⟨U, hUsub, hUopen, hqU⟩
  have hpullqApply : ∀ x y : E,
      (fun r : E ↦
        CovariantDerivative.chartMetric (gt t).inner anchor (F r)
          (D r x) (D r y)) =ᶠ[nhds q]
        (fun r : E ↦
          CovariantDerivative.chartMetric (rt t).inner anchor r x y) := by
    intro x y
    filter_upwards [hpullq] with r hr
    exact congrArg
      (fun H : E →L[ℝ] E →L[ℝ] ℝ ↦ H x y) hr
  have hDcanonical : HasFDerivAt D (fderiv ℝ D q) q :=
    hDq.differentiableAt.hasFDerivAt
  have hD2symm : ∀ x y : E,
      (fderiv ℝ D q x) y = (fderiv ℝ D q y) x := by
    intro x y
    rw [hDq.fderiv]
    exact hBsymmq x y
  have hG₁symm : ∀ x y : E,
      CovariantDerivative.chartMetric (gt t).inner anchor (F q) x y =
        CovariantDerivative.chartMetric (gt t).inner anchor (F q) y x := by
    intro x y
    exact CovariantDerivative.chartMetric_symm (gt t).inner
      (fun p u v ↦ (gt t).inner_symm p u v) anchor (F q) x y
  let b₀ : LinearMap.BilinForm ℝ E :=
    continuousBilinForm
      (CovariantDerivative.chartMetric (rt t).inner anchor q)
  let b₁ : LinearMap.BilinForm ℝ E :=
    continuousBilinForm
      (CovariantDerivative.chartMetric (gt t).inner anchor (F q))
  have hb₀ : b₀.Nondegenerate := by
    simpa only [b₀] using hb₀q
  have hb₁ : b₁.Nondegenerate := by
    simpa only [b₁] using hb₁q
  have hb₀G : ∀ x y : E,
      b₀ x y =
        CovariantDerivative.chartMetric (rt t).inner anchor q x y := by
    intro x y
    rfl
  have hb₁G : ∀ x y : E,
      b₁ x y =
        CovariantDerivative.chartMetric (gt t).inner anchor (F q) x y := by
    intro x y
    rfl
  have hraw :=
    christoffelAt_map_eq_signed_transport_of_metricPullbackGerm
      (CovariantDerivative.chartMetric (rt t).inner anchor)
      (CovariantDerivative.chartMetric (gt t).inner anchor)
      F D hFq hDcanonical hG₀q hG₁q hpullqApply hDinvq hD2symm
        hG₁symm b₀ b₁ hb₀ hb₁ hb₀G hb₁G a b
  rw [anchorChartChristoffelFieldFlow_eq_christoffelAt_of_cutoffGerm
      gt anchor t hcut₁q hb₁,
    anchorChartChristoffelFieldFlow_eq_christoffelAt_of_cutoffGerm
      rt anchor t hcut₀q hb₀]
  simpa only [hDq.fderiv, hBsymmq a b] using hraw

end OpenMetricPullbackRefinement

section SuppliedPhysicalFlowMetricPullbackAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Exact chartwise realization and nearby spatial regularity eliminate the
signed-Christoffel premise from supplied physical-flow curvature assembly.

The metric-pullback germ is produced internally from exact realization and
the source coefficient germ.  The nearby hypotheses are the explicit local
`C²`/nondegeneracy/invertibility boundary needed to promote that one germ to
Christoffel germs at every point of an open refinement. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_metricPullbackGerm
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
    (hMetricRtNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      HasFDerivAt
        (CovariantDerivative.chartMetric (rt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (rt t).inner anchor) q) q)
    (hMetricGtNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      HasFDerivAt
        (CovariantDerivative.chartMetric (gt t).inner anchor)
        (fderiv ℝ (CovariantDerivative.chartMetric (gt t).inner anchor)
          (Phi anchor t q)) (Phi anchor t q))
    (hDPhiInvNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      (DPhi anchor t q).IsInvertible)
    (hBsymmNear : ∀ᶠ q in nhds (extChartAt I anchor y₀),
      ∀ a b : E, (B q a) b = (B q b) a)
    (hCsymm : ∀ a b c : E,
      ((fderiv ℝ B (extChartAt I anchor y₀) a) b) c =
        ((fderiv ℝ B (extChartAt I anchor y₀) c) b) a)
    (hMetricRtNondegNear :
      ∀ᶠ q in nhds (extChartAt I anchor y₀),
        (continuousBilinForm
          (CovariantDerivative.chartMetric (rt t).inner anchor q)).Nondegenerate)
    (hMetricGtNondegNear :
      ∀ᶠ q in nhds (extChartAt I anchor y₀),
        (continuousBilinForm
          (CovariantDerivative.chartMetric (gt t).inner anchor
            (Phi anchor t q))).Nondegenerate) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  have hPhiD : HasFDerivAt (Phi anchor t) (DPhi anchor t z₀) z₀ := by
    exact hPhiSpaceNear.self_of_nhds
  have hDPhiD : HasFDerivAt (DPhi anchor t) (B z₀) z₀ := by
    exact hDPhiSpaceNear.self_of_nhds
  have hDPhiInv : (DPhi anchor t z₀).IsInvertible :=
    hDPhiInvNear.self_of_nhds
  have hBsymm : ∀ a b : E, (B z₀ a) b = (B z₀ b) a :=
    hBsymmNear.self_of_nhds
  have hz₀ : z₀ ∈ (extChartAt I anchor).target := by
    simpa only [z₀] using (extChartAt I anchor).map_source hy₀
  have hpull :
      (fun q : E ↦ pullbackBilinearForm
          (CovariantDerivative.chartMetric (gt t).inner anchor
            (Phi anchor t q))
          (DPhi anchor t q)) =ᶠ[nhds z₀]
        CovariantDerivative.chartMetric (rt t).inner anchor := by
    exact
      pullback_chartMetric_eventuallyEq_chartMetric_of_chartwiseRealization_and_sourceGerm
        rt gt D K u₀ Phi DPhi anchor t hz₀ hPhiD.continuousAt
          (hrealize t) (by simpa only [z₀] using hfullGerm)
  have hcut₀Near : ∀ᶠ q in nhds z₀,
      ∀ᶠ r in nhds q,
        GeodesicTransport.cutoff (n := n) anchor r = 1 := by
    exact eventually_eventually_nhds.2 (by simpa only [z₀] using hχ₀)
  have hcut₁AtEndpoint :
      ∀ᶠ q in nhds (Phi anchor t z₀),
        ∀ᶠ r in nhds q,
          GeodesicTransport.cutoff (n := n) anchor r = 1 := by
    rw [show Phi anchor t z₀ = extChartAt I anchor y₁ by
      simpa only [z₀] using hendpoint]
    exact eventually_eventually_nhds.2 hχ₁
  have hcut₁Near : ∀ᶠ q in nhds z₀,
      ∀ᶠ r in nhds (Phi anchor t q),
        GeodesicTransport.cutoff (n := n) anchor r = 1 :=
    hPhiD.continuousAt hcut₁AtEndpoint
  have htransition : ∀ a b : E,
      (fun q : E ↦ anchorChartChristoffelFieldFlow gt anchor t
          (Phi anchor t q) (DPhi anchor t q a) (DPhi anchor t q b)) =ᶠ[
            nhds z₀]
        (fun q : E ↦ DPhi anchor t q
            (anchorChartChristoffelFieldFlow rt anchor t q a b) -
          (B q b) a) := by
    exact
      anchorChartChristoffelFieldFlow_signedTransition_of_metricPullbackGerm
        rt gt anchor t (Phi anchor t) (DPhi anchor t) B hpull
          (by simpa only [z₀] using hPhiSpaceNear)
          (by simpa only [z₀] using hDPhiSpaceNear)
          (by simpa only [z₀] using hMetricRtNear)
          (by simpa only [z₀] using hMetricGtNear)
          (by simpa only [z₀] using hDPhiInvNear)
          (by simpa only [z₀] using hBsymmNear)
          (by simpa only [z₀] using hMetricRtNondegNear)
          (by simpa only [z₀] using hMetricGtNondegNear)
          hcut₀Near hcut₁Near
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_signedChristoffelGerm
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi DPhi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hDPhiInv
        hPhiC1 (by simpa only [z₀] using hPhiD) hrealize B
        (by simpa only [z₀] using hDPhiD)
        (by simpa only [z₀] using hBSpace)
        (by simpa only [z₀] using hChristoffelRt)
        (by simpa only [z₀] using hChristoffelGt)
        (by simpa only [z₀] using hBsymm)
        (by simpa only [z₀] using hCsymm)
        (by simpa only [z₀] using htransition)

end SuppliedPhysicalFlowMetricPullbackAssembly

end Poincare
