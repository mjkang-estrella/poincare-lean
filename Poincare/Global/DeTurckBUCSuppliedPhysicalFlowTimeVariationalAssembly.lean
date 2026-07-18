import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowSpatialC3Assembly
import Poincare.Global.DeTurckCoordinateJointRegularityOverlap

/-!
# Automatic time-variational equation for a supplied physical point flow

A jointly `C^2` point-flow endpoint has commuting time and spatial
derivatives.  Consequently, a spatial germ of the point-flow ODE determines
the time derivative of its canonical spatial differential.  For the inverse
DeTurck coordinate field, the required fixed-time spatial derivative is
automatic from smoothness of the frozen Riemannian metric.

The final wrapper combines this observation with the spatial-`C^3` assembly:
one joint `C^3` premise supplies both mixed regularity and all fixed-time
spatial derivatives, while the ODE is required only as a germ in the initial
point.
-/

noncomputable section

open Bundle FiberBundle Filter Function Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section AbstractPointFlowVariationalEquation

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Differentiate a jointly `C^2` point-flow ODE in its initial point.

The ODE is stated as a spatial germ of its ordinary time derivative.  This is
the weakest form needed to identify the spatial derivative of the time
partial. -/
theorem hasDerivAt_spatialDifferential_of_jointContDiffAt_two_and_ODE_germ
    (Phi : ℝ → E → E) (V : E → E) (DV : E →L[ℝ] E)
    (t : ℝ) (z : E)
    (hPhiJoint : ContDiffAt ℝ 2 (Function.uncurry Phi) (t, z))
    (hODE :
      (fun q ↦ deriv (fun s ↦ Phi s q) t) =ᶠ[nhds z]
        (fun q ↦ V (Phi t q)))
    (hV : HasFDerivAt V DV (Phi t z)) :
    HasDerivAt (fun s ↦ fderiv ℝ (Phi s) z)
      (DV.comp (fderiv ℝ (Phi t) z)) t := by
  have hPhiSpace : HasFDerivAt (Phi t) (fderiv ℝ (Phi t) z) z := by
    have hslice : ContDiffAt ℝ 2 (Phi t) z := by
      have hpath : ContDiffAt ℝ 2 (fun q : E ↦ (t, q)) z :=
        contDiffAt_const.prodMk contDiffAt_id
      simpa only [Function.uncurry] using hPhiJoint.comp z hpath
    exact (hslice.differentiableAt (by norm_num)).hasFDerivAt
  have hVcomp : HasFDerivAt (fun q ↦ V (Phi t q))
      (DV.comp (fderiv ℝ (Phi t) z)) z :=
    hV.comp z hPhiSpace
  have htimePartialFDeriv :
      fderiv ℝ (fun q ↦ deriv (fun s ↦ Phi s q) t) z =
        DV.comp (fderiv ℝ (Phi t) z) := by
    rw [hODE.fderiv_eq, hVcomp.fderiv]
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro a
  have hmixed :=
    hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      Phi t z a hPhiJoint
  exact hmixed.congr_deriv
    (congrArg (fun L : E →L[ℝ] E ↦ L a) htimePartialFDeriv)

end AbstractPointFlowVariationalEquation

section InverseDeTurckCoordinateFieldDerivative

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The fixed-time inverse DeTurck coordinate field has derivative equal to
the negative ordinary coordinate derivative of the DeTurck field at every
genuine target point.

No time regularity of `gt` is needed: freeze `gt t` into a constant metric
family and invoke the existing joint chart-coordinate regularity theorem. -/
theorem inverseDeTurckChartCoordinateField_hasFDerivAt_of_mem_source
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) {y : M} (hy : y ∈ (extChartAt I anchor).source) :
    HasFDerivAt (inverseDeTurckChartCoordinateField gt bg anchor t)
      (-(deTurckChartFieldDerivativeAt gt bg anchor t
        (extChartAt I anchor y)))
      (extChartAt I anchor y) := by
  let frozen : ℝ → ClosedSmoothRiemannianMetric n M := fun _ ↦ gt t
  have hentries : MetricEntriesJointContDiffAt frozen t y 3 := by
    simpa only [frozen] using metricEntriesJointContDiffAt_const (gt t) t y
  have hjoint : ContDiffAt ℝ 2
      (Function.uncurry (fun s z ↦
        chartCoordinateTangentField anchor
          (deTurckVectorField frozen bg s) z))
      (t, extChartAt I anchor y) :=
    DeTurckCoordinateJointRegularityOverlap.deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries_of_mem_source
        (gt := frozen) (bg := bg) (t₀ := t) (anchor := anchor)
        (y := y) hy hentries
  have hcoordinate : ContDiffAt ℝ 2
      (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
      (extChartAt I anchor y) := by
    have hpath : ContDiffAt ℝ 2
        (fun z : E ↦ (t, z)) (extChartAt I anchor y) :=
      contDiffAt_const.prodMk contDiffAt_id
    simpa only [Function.uncurry, frozen] using
      hjoint.comp (extChartAt I anchor y) hpath
  have hcoordinateDeriv : HasFDerivAt
      (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
      (fderiv ℝ
        (chartCoordinateTangentField anchor (deTurckVectorField gt bg t))
        (extChartAt I anchor y))
      (extChartAt I anchor y) :=
    (hcoordinate.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [inverseDeTurckChartCoordinateField,
    deTurckChartFieldDerivativeAt] using hcoordinateDeriv.neg

end InverseDeTurckCoordinateFieldDerivative

section AutomaticTimeVariationalSuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow assembly with the canonical spatial variational
equation generated by joint endpoint regularity and the point-flow ODE germ.

The single joint `C^3` endpoint premise also supplies the fixed-time `C^3`
premise consumed by the spatial assembly theorem. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_jointC3_ODEGerm
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
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
    (hPhiJointC3 : ContDiffAt ℝ 3
      (Function.uncurry (Phi anchor))
      (t, extChartAt I anchor y₀))
    (hPhiODEGerm :
      (fun q ↦ deriv (fun s ↦ Phi anchor s q) t) =ᶠ[
          nhds (extChartAt I anchor y₀)]
        (fun q ↦ inverseDeTurckChartCoordinateField
          gt bg anchor t (Phi anchor t q)))
    (hDPhiInv :
      (suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor t (extChartAt I anchor y₀)).IsInvertible)
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi (suppliedPhysicalPointFlowSpatialDifferential Phi)
            s anchor z) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  have hPhiJointC2 : ContDiffAt ℝ 2
      (Function.uncurry (Phi anchor)) (t, z₀) :=
    hPhiJointC3.of_le (by norm_num)
  have hPhiSpatialC3 : ContDiffAt ℝ 3 (Phi anchor t) z₀ := by
    have hpath : ContDiffAt ℝ 3 (fun q : E ↦ (t, q)) z₀ :=
      contDiffAt_const.prodMk contDiffAt_id
    simpa only [Function.uncurry] using hPhiJointC3.comp z₀ hpath
  have hPhiTime : HasDerivAt (fun s : ℝ ↦ Phi anchor s z₀)
      (inverseDeTurckChartCoordinateField gt bg anchor t
        (Phi anchor t z₀)) t := by
    have hpath : ContDiffAt ℝ 1 (fun s : ℝ ↦ (s, z₀)) t :=
      contDiffAt_id.prodMk contDiffAt_const
    have htimeC1 : ContDiffAt ℝ 1
        (fun s : ℝ ↦ Phi anchor s z₀) t := by
      simpa only [Function.uncurry] using
        (hPhiJointC3.of_le (by norm_num)).comp t hpath
    have htime : HasDerivAt (fun s : ℝ ↦ Phi anchor s z₀)
        (deriv (fun s : ℝ ↦ Phi anchor s z₀) t) t :=
      (hasDerivAt_deriv_iff (f := fun s : ℝ ↦ Phi anchor s z₀)
        (x := t)).2 (htimeC1.differentiableAt (by norm_num))
    exact htime.congr_deriv hPhiODEGerm.self_of_nhds
  have hInverseField : HasFDerivAt
      (inverseDeTurckChartCoordinateField gt bg anchor t)
      (-(deTurckChartFieldDerivativeAt gt bg anchor t
        (Phi anchor t z₀)))
      (Phi anchor t z₀) := by
    have h := inverseDeTurckChartCoordinateField_hasFDerivAt_of_mem_source
      gt bg anchor t hy₁
    simpa only [z₀, hendpoint] using h
  have hDPhiTime : HasDerivAt
      (fun s : ℝ ↦ suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor s z₀)
      ((-(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t z₀))).comp
        (suppliedPhysicalPointFlowSpatialDifferential Phi anchor t z₀)) t := by
    simpa only [suppliedPhysicalPointFlowSpatialDifferential] using
      hasDerivAt_spatialDifferential_of_jointContDiffAt_two_and_ODE_germ
        (Phi anchor)
        (inverseDeTurckChartCoordinateField gt bg anchor t)
        (-(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t z₀))) t z₀ hPhiJointC2 hPhiODEGerm hInverseField
  apply isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_spatialC3
    (y₀ := y₀) (y₁ := y₁) (t := t)
    rt D K u₀ Phi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
      hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime hPhiSpatialC3
      hDPhiInv hrealize

end AutomaticTimeVariationalSuppliedFlowAssembly

end Poincare
