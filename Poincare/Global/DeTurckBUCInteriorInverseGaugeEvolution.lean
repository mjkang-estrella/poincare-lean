import Poincare.Global.DeTurckBUCInteriorCoefficientIdentification

/-!
# Interior inverse-gauge Ricci evolution

At a strict positive time the reconstructed `BUC` coefficient has an ordinary
Banach-valued derivative.  Joint `C²` regularity of the coordinate DeTurck
field restarts the inverse-gauge trajectory and its variational equation at
that time.  Combining these facts with the arbitrary-time pullback theorem
produces a genuine two-sided coordinate Ricci-flow germ.

The remaining hypotheses are the actual geometric assembly boundary: a
metric germ for the current reconstructed coefficient, identification of the
selected generator plus remainder with the Ricci--DeTurck right-hand side,
and the preferred-chart cutoff germ.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology NNReal

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
/--
Automatic positive-time classicality and a restarted inverse DeTurck gauge
give a genuine coordinate Ricci-flow germ at every strict interior time.
The endpoint map is the identity at the restart time, so its local
diffeomorphism data require no separate smooth-dependence premise.
-/
theorem exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ))
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[
            nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorGeneratorValue
              K u₀ t +
            D.base.nonlinearity
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                  K u₀ t +
                D.background))
          (extChartAt I anchor y) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          (extChartAt I anchor y))
    (hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun s z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg s) z))
      (t, extChartAt I anchor y)) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi t = extChartAt I anchor y ∧
        J t = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I anchor y) (J t),
          G.localHomeomorph (extChartAt I anchor y) = phi t ∧
            reconstructedInverseGaugeMetric D K u₀ phi J t =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt t).inner anchor (phi t))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt t) anchor
                  (extChartAt I anchor y)
                  ((extChartAt I anchor).map_source hy))) t := by
  let z₀ : E := extChartAt I anchor y
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  let g' : CoordinateBUCTensor E :=
    A.uniformInteriorGeneratorValue K u₀ t +
      D.base.nonlinearity
        (A.uniformInteriorState K u₀ t + D.background)
  have hg : HasDerivAt
      (reconstructedCoordinateMetricPath D K u₀) g' t := by
    simpa only [A, g'] using
      reconstructedCoordinateMetricPath_hasDerivAt_interior_automatic
        D K u₀ ht₀ htT
  have hWone : ContDiffAt ℝ 1 (Function.uncurry
      (fun s z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg s) z)) (t, z₀) := by
    simpa only [z₀] using hW.of_le (by norm_num)
  have hDWone : ContDiffAt ℝ 1 (Function.uncurry
      (fun s z ↦ deTurckChartFieldDerivativeAt gt bg anchor s z))
      (t, z₀) := by
    exact
      deTurckChartFieldDerivativeAt_jointContDiffAt_one_of_coordinateField_jointContDiffAt_two
        gt bg anchor t z₀ (by simpa only [z₀] using hW)
  rcases exists_inverseDeTurckChartGauge_variational_data_at
      gt bg anchor t z₀ hWone hDWone Set.univ with
    ⟨phi, J, hphi_t, hJ_t, hphiWithin, hJWithin, hJinv⟩
  have hphi : HasDerivAt phi
      (inverseDeTurckChartCoordinateField gt bg anchor t (phi t)) t := by
    simpa only [hasDerivWithinAt_univ] using hphiWithin
  have hJ : HasDerivAt J
      (-(deTurckChartFieldDerivativeAt gt bg anchor t (phi t)).comp
        (J t)) t := by
    simpa only [hasDerivWithinAt_univ] using hJWithin
  have hfullGerm' :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[nhds (phi t)]
        CovariantDerivative.chartMetric (gt t).inner anchor := by
    simpa only [hphi_t, z₀] using hfullGerm
  have hidentifyRHS' :
      coordinateBilinearFormAt g' (phi t) =
        deTurckChartMetricEvolutionBilin gt bg anchor t (phi t) := by
    simpa only [g', A, hphi_t, z₀] using hidentifyRHS
  have hPhi_t : (fun z : E ↦ z) z₀ = phi t := by
    exact hphi_t.symm
  have hPhiD : HasFDerivAt (fun z : E ↦ z) (J t) z₀ := by
    rw [hJ_t]
    exact hasFDerivAt_id (x := z₀)
  rcases
      exists_reconstructed_coordinateLocalDiffeomorphGerm_with_RicciFlowAt
        D K u₀ gt bg anchor hy hχone phi J (fun z : E ↦ z) z₀
        hphi_t hPhi_t hg hfullGerm' hidentifyRHS' hphi hJ hJinv
        contDiffAt_id hPhiD (deTurckVectorFieldRegularAt_holds gt bg t) with
    ⟨G, hG, hmetric, hflow⟩
  have hzphi : phi t ∈ (extChartAt I anchor).target := by
    simpa only [hphi_t, z₀] using (extChartAt I anchor).map_source hy
  have hcurv :
      chartRicciCurvatureEndAt (gt t) anchor (phi t) hzphi =
        chartRicciCurvatureEndAt (gt t) anchor
          (extChartAt I anchor y) ((extChartAt I anchor).map_source hy) := by
    exact chartRicciCurvatureEndAt_congr
      (gt t) anchor hzphi ((extChartAt I anchor).map_source hy)
        (by simpa only [z₀] using hphi_t)
  refine ⟨phi, J, hphi_t, hJ_t, G, hG, hmetric, ?_⟩
  simpa only [hcurv] using hflow

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/--
The strongest germ-level interior inverse-gauge wrapper.  Full and background
metric germs, together with the isolated lower-order remainder formula,
automatically identify the canonical positive-time Banach slope with the
Ricci--DeTurck chart evolution.  The reconstructed path is explicitly
rewritten from background-plus-state to state-plus-background before the
metric germ is passed to the inverse-gauge theorem.
-/
theorem exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_of_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan K : ℝ))
    (hy : y ∈ (extChartAt I anchor).source)
    (hχone : ∀ᶠ z' in nhds (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
              K u₀ t +
            D.background) z') =ᶠ[nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background)) (extChartAt I anchor y) v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t
            (extChartAt I anchor y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background) (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I anchor y) v w)
    (hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun s z ↦ chartCoordinateTangentField anchor
        (deTurckVectorField gt bg s) z))
      (t, extChartAt I anchor y)) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi t = extChartAt I anchor y ∧
        J t = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I anchor y) (J t),
          G.localHomeomorph (extChartAt I anchor y) = phi t ∧
            reconstructedInverseGaugeMetric D K u₀ phi J t =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt t).inner anchor (phi t))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt t) anchor
                  (extChartAt I anchor y)
                  ((extChartAt I anchor).map_source hy))) t := by
  let A :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
  have hz : extChartAt I anchor y ∈ (extChartAt I anchor).target :=
    (extChartAt I anchor).map_source hy
  have hidentifyRHS :
      coordinateBilinearFormAt
          (A.uniformInteriorGeneratorValue K u₀ t +
            D.base.nonlinearity
              (A.uniformInteriorState K u₀ t + D.background))
          (extChartAt I anchor y) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          (extChartAt I anchor y) := by
    simpa only [A] using
      coordinateBilinearFormAt_reconstructedInteriorSlope_eq_deTurckChartMetricEvolutionBilin_of_germs
        D K u₀ ht₀ htT gt bg anchor hz hfullGerm hbackgroundGerm hremainder
  have hreconstructed :
      reconstructedCoordinateMetricPath D K u₀ t =
        A.uniformInteriorState K u₀ t + D.background := by
    simp only [reconstructedCoordinateMetricPath,
      AffineRecenteredDeTurckShapedBUCRemainderData.reconstructedMetricCoefficient,
      AffineRecenteredDeTurckShapedBUCRemainderData.uniformInteriorState,
      A, AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground]
    rw [add_comm]
  have hfullReconstructedGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath D K u₀ t) z') =ᶠ[
            nhds (extChartAt I anchor y)]
        CovariantDerivative.chartMetric (gt t).inner anchor := by
    rw [hreconstructed]
    simpa only [A] using hfullGerm
  exact
    exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior
      D K u₀ gt bg anchor ht₀ htT hy hχone hfullReconstructedGerm
        (by simpa only [A] using hidentifyRHS) hW

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Self-chart specialization of the automatic interior inverse-gauge
construction.  At the chart anchor, source membership and the cutoff-one
germ are unconditional, so only the genuine metric/background germs,
lower-order coefficient identity, and joint DeTurck-field regularity remain.
-/
theorem exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_selfChart_of_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (y : M) {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan
        K : ℝ))
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
              K u₀ t +
            D.background) z') =ᶠ[nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric (gt t).inner y)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric bg.inner y)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background)) (extChartAt I y y) v w =
        deTurckChartMetricEvolutionBilin gt bg y t
            (extChartAt I y y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background) (extChartAt I y y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I y y) v w)
    (hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun s z ↦ chartCoordinateTangentField y
        (deTurckVectorField gt bg s) z))
      (t, extChartAt I y y)) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi t = extChartAt I y y ∧
        J t = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I y y) (J t),
          G.localHomeomorph (extChartAt I y y) = phi t ∧
            reconstructedInverseGaugeMetric D K u₀ phi J t =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt t).inner y (phi t))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt t) y
                  (extChartAt I y y)
                  ((extChartAt I y).map_source
                    (mem_extChartAt_source y)))) t := by
  exact
    exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_of_germs
      D K u₀ gt bg y ht₀ htT (mem_extChartAt_source y)
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) y)
      hfullGerm hbackgroundGerm hremainder hW

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Joint C3 entries of the ambient Ricci--DeTurck metric discharge the
last coordinate-field regularity premise in the self-chart interior
construction.  The remaining premises are precisely the current/full and
background spatial germs and the lower-order coefficient formula. -/
theorem exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_selfChart_of_metricEntries
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (y : M) {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformLifespan
        K : ℝ))
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
              K u₀ t +
            D.background) z') =ᶠ[nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric (gt t).inner y)
    (hbackgroundGerm :
      (fun z' ↦ coordinateBilinearFormAt D.background z') =ᶠ[
          nhds (extChartAt I y y)]
        CovariantDerivative.chartMetric bg.inner y)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background)) (extChartAt I y y) v w =
        deTurckChartMetricEvolutionBilin gt bg y t
            (extChartAt I y y) v w -
          coordinateMetricLaplacianValue
            ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D).uniformInteriorState
                K u₀ t +
              D.background) (extChartAt I y y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I y y) v w)
    (hJoint : MetricEntriesJointContDiffAt gt t y 3) :
    ∃ phi : ℝ → E, ∃ J : ℝ → E →L[ℝ] E,
      phi t = extChartAt I y y ∧
        J t = ContinuousLinearMap.id ℝ E ∧
        ∃ G : CoordinateLocalDiffeomorphGerm
            (fun z : E ↦ z) (extChartAt I y y) (J t),
          G.localHomeomorph (extChartAt I y y) = phi t ∧
            reconstructedInverseGaugeMetric D K u₀ phi J t =
              pullbackBilinearForm
                (CovariantDerivative.chartMetric (gt t).inner y (phi t))
                (G.tangentEquiv : E →L[ℝ] E) ∧
            IsCoordinateRicciFlowAt
              (reconstructedInverseGaugeMetric D K u₀ phi J)
              (pullbackCurvatureEnd G.tangentEquiv
                (chartRicciCurvatureEndAt (gt t) y
                  (extChartAt I y y)
                  ((extChartAt I y).map_source
                    (mem_extChartAt_source y)))) t := by
  have hW : ContDiffAt ℝ 2 (Function.uncurry
      (fun s z ↦ chartCoordinateTangentField y
        (deTurckVectorField gt bg s) z))
      (t, extChartAt I y y) :=
    DeTurckCoordinateJointRegularity.deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries
      (bg := bg) hJoint
  exact
    exists_reconstructed_inverseDeTurckGauge_with_RicciFlowAt_interior_selfChart_of_germs
      D K u₀ gt bg y ht₀ htT hfullGerm hbackgroundGerm hremainder hW

end Poincare
