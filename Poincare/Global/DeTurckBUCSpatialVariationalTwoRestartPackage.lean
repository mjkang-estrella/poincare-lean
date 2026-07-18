import Poincare.Global.DeTurckBUCTwoRestartPointFlowCore

/-!
# A spatial-variational two-restart package

The inverse-gauge reconstruction does not need three joint derivatives of a
point flow in `(time, initialPoint)`.  The downstream metric calculation uses
only:

* `C³` regularity of the selected forward endpoint as a function of its
  initial point;
* `C¹` regularity of the fixed-time backward endpoint;
* the ordinary point-flow ODE; and
* the first spatial variational equation in time.

This module records that anisotropic contract and proves that it is sufficient
for the supplied physical-flow assembly.  It is tailored to nonautonomous ODE
constructions, where the vector field may be merely continuous in time while
remaining smooth in space.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open Bundle FiberBundle Filter Function Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section AbstractSpatialVariationalPackage

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ODE core plus exactly the fixed-time spatial regularity and first
variational time equation consumed by inverse-gauge metric reconstruction.

Unlike `TwoRestartPointFlowPackage`, this structure assumes no joint time-space
`ContDiffAt` statement. -/
structure TwoRestartSpatialVariationalPointFlowPackage
    (V : ℝ → E → E) (Phi Psi : ℝ → E → E)
    (t : ℝ) (z₀ y₁ : E) where
  core : TwoRestartPointFlowCore V Phi Psi t z₀ y₁
  forward_spatialC3 : ContDiffAt ℝ 3 (Phi t) z₀
  backward_zero_spatialC1 : ContDiffAt ℝ 1 (Psi 0) y₁
  forward_spatialDifferential_time :
    HasDerivAt
      (fun s : ℝ ↦ fderiv ℝ (Phi s) z₀)
      ((fderiv ℝ (V t) (Phi t z₀)).comp
        (fderiv ℝ (Phi t) z₀)) t

namespace TwoRestartPointFlowCore

variable {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
variable {t : ℝ} {z₀ y₁ : E}

/-- The point-flow core already supplies the endpoint ODE derivative germ.
No differentiability in the initial-point parameter is used. -/
theorem forward_ODE_germ_core
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (ht : 0 < t) :
    (fun q ↦ deriv (fun s ↦ Phi s q) t) =ᶠ[nhds z₀]
      (fun q ↦ V t (Phi t q)) := by
  filter_upwards [H.forward_flow] with q hq
  exact (hq.2 t ⟨ht.le, le_rfl⟩).1.deriv

/-- Interval uniqueness gives the two local inverse germs from the ODE core
once continuity of the two fixed-time endpoint maps is supplied. -/
theorem endpoint_twoSidedInverseGerms_of_fixedTime_continuousAt
    (H : TwoRestartPointFlowCore V Phi Psi t z₀ y₁)
    (ht : 0 < t)
    (hPhi : ContinuousAt (Phi t) z₀)
    (hPsi : ContinuousAt (Psi 0) y₁) :
    (fun q ↦ Psi 0 (Phi t q)) =ᶠ[nhds z₀] (fun q ↦ q) ∧
      (fun q ↦ Phi t (Psi 0 q)) =ᶠ[nhds y₁] (fun q ↦ q) := by
  have hPhiToTarget : Tendsto (Phi t) (nhds z₀) (nhds y₁) := by
    rw [← H.endpoint_eq]
    exact hPhi
  have hbackwardAfterForward : ∀ᶠ q in nhds z₀,
      Psi t (Phi t q) = Phi t q ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Psi tau (Phi t q))
              (V s (Psi s (Phi t q))) s ∧
            Psi s (Phi t q) ∈ H.controlledSet :=
    hPhiToTarget H.backward_flow
  have hleft :
      (fun q ↦ Psi 0 (Phi t q)) =ᶠ[nhds z₀] (fun q ↦ q) := by
    filter_upwards [H.forward_flow, hbackwardAfterForward] with q hforward hbackward
    have heq := odeSolutions_eqOn_Icc_of_eq_at_rightEndpoint
      (V := V) (S := H.controlledSet) (K := H.K)
      (alpha := fun s ↦ Phi s q)
      (beta := fun s ↦ Psi s (Phi t q))
      H.lipschitzOn
      (fun s hs ↦ (hforward.2 s hs).1)
      (fun s hs ↦ (hforward.2 s hs).2)
      (fun s hs ↦ (hbackward.2 s hs).1)
      (fun s hs ↦ (hbackward.2 s hs).2)
      hbackward.1.symm
    calc
      Psi 0 (Phi t q) = Phi 0 q :=
        (heq ⟨le_rfl, ht.le⟩).symm
      _ = q := hforward.1
  have hPsiBase : Psi 0 y₁ = z₀ := by
    have h := hleft.self_of_nhds
    simpa only [H.endpoint_eq] using h
  have hPsiToSource : Tendsto (Psi 0) (nhds y₁) (nhds z₀) := by
    rw [← hPsiBase]
    exact hPsi
  have hforwardAfterBackward : ∀ᶠ q in nhds y₁,
      Phi 0 (Psi 0 q) = Psi 0 q ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Phi tau (Psi 0 q))
              (V s (Phi s (Psi 0 q))) s ∧
            Phi s (Psi 0 q) ∈ H.controlledSet :=
    hPsiToSource H.forward_flow
  have hright :
      (fun q ↦ Phi t (Psi 0 q)) =ᶠ[nhds y₁] (fun q ↦ q) := by
    filter_upwards [H.backward_flow, hforwardAfterBackward] with q hbackward hforward
    have heq := odeSolutions_eqOn_Icc_of_eq_at_leftEndpoint
      (V := V) (S := H.controlledSet) (K := H.K)
      (alpha := fun s ↦ Phi s (Psi 0 q))
      (beta := fun s ↦ Psi s q)
      H.lipschitzOn
      (fun s hs ↦ (hforward.2 s hs).1)
      (fun s hs ↦ (hforward.2 s hs).2)
      (fun s hs ↦ (hbackward.2 s hs).1)
      (fun s hs ↦ (hbackward.2 s hs).2)
      hforward.1
    calc
      Phi t (Psi 0 q) = Psi t q := heq ⟨ht.le, le_rfl⟩
      _ = q := hbackward.1
  exact ⟨hleft, hright⟩

end TwoRestartPointFlowCore

namespace TwoRestartSpatialVariationalPointFlowPackage

variable {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
variable {t : ℝ} {z₀ y₁ : E}

/-- The anisotropic package supplies the two fixed-time inverse germs. -/
theorem endpoint_twoSidedInverseGerms
    (H : TwoRestartSpatialVariationalPointFlowPackage
      V Phi Psi t z₀ y₁)
    (ht : 0 < t) :
    (fun q ↦ Psi 0 (Phi t q)) =ᶠ[nhds z₀] (fun q ↦ q) ∧
      (fun q ↦ Phi t (Psi 0 q)) =ᶠ[nhds y₁] (fun q ↦ q) :=
  H.core.endpoint_twoSidedInverseGerms_of_fixedTime_continuousAt ht
    H.forward_spatialC3.continuousAt
    H.backward_zero_spatialC1.continuousAt

/-- The forward fixed-time differential is invertible, derived from the
genuine backward restart rather than stored as an algebraic premise. -/
theorem forward_fderiv_isInvertible
    (H : TwoRestartSpatialVariationalPointFlowPackage
      V Phi Psi t z₀ y₁)
    (ht : 0 < t) :
    (fderiv ℝ (Phi t) z₀).IsInvertible := by
  rcases H.endpoint_twoSidedInverseGerms ht with ⟨hleft, hright⟩
  have hPsiAt : ContDiffAt ℝ 1 (Psi 0) (Phi t z₀) := by
    simpa only [H.core.endpoint_eq] using H.backward_zero_spatialC1
  exact fderiv_isInvertible_of_contDiffAt_one_twoSidedInverseGerm
    (Phi t) (Psi 0) z₀
    (H.forward_spatialC3.of_le (by norm_num)) hPsiAt hleft
    (by simpa only [H.core.endpoint_eq] using hright)

end TwoRestartSpatialVariationalPointFlowPackage

end AbstractSpatialVariationalPackage

section SuppliedPhysicalFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/-- The anisotropic two-restart package is sufficient for the complete
supplied physical-flow assembly.  In particular, no joint time-space `C³`
premise is present.

The first variational equation stored in the package is converted to the
canonical inverse-DeTurck coefficient using the fixed-time derivative theorem
for the coordinate field. -/
theorem isClosedRicciFlowSolutionAt_of_spatialVariationalTwoRestartPackage
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (Psi : ℝ → E → E)
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
    (H : TwoRestartSpatialVariationalPointFlowPackage
      (fun s ↦ inverseDeTurckChartCoordinateField gt bg anchor s)
      (Phi anchor) Psi t
      (extChartAt I anchor y₀) (extChartAt I anchor y₁))
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
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi (suppliedPhysicalPointFlowSpatialDifferential Phi)
            s anchor z) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  let z₀ : E := extChartAt I anchor y₀
  let z₁ : E := extChartAt I anchor y₁
  let V : ℝ → E → E :=
    fun s ↦ inverseDeTurckChartCoordinateField gt bg anchor s
  have hendpoint : Phi anchor t z₀ = z₁ := H.core.endpoint_eq
  have hPhiTime : HasDerivAt (fun s : ℝ ↦ Phi anchor s z₀)
      (inverseDeTurckChartCoordinateField gt bg anchor t
        (Phi anchor t z₀)) t := by
    have hbase := H.core.forward_flow.self_of_nhds
    simpa only [V] using (hbase.2 t ⟨ht₀.le, le_rfl⟩).1
  have hfieldDerivative :
      fderiv ℝ (V t) (Phi anchor t z₀) =
        -(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t z₀)) := by
    have h := inverseDeTurckChartCoordinateField_hasFDerivAt_of_mem_source
      gt bg anchor t hy₁
    have h' : HasFDerivAt (V t)
        (-(deTurckChartFieldDerivativeAt gt bg anchor t z₁)) z₁ := by
      simpa only [V, z₁] using h
    simpa only [hendpoint] using h'.fderiv
  have hDPhiTime : HasDerivAt
      (fun s : ℝ ↦ suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor s z₀)
      ((-(deTurckChartFieldDerivativeAt gt bg anchor t
          (Phi anchor t z₀))).comp
        (suppliedPhysicalPointFlowSpatialDifferential
          Phi anchor t z₀)) t := by
    rw [← hfieldDerivative]
    simpa only [suppliedPhysicalPointFlowSpatialDifferential, V, z₀] using
      H.forward_spatialDifferential_time
  have hDPhiInv :
      (suppliedPhysicalPointFlowSpatialDifferential
        Phi anchor t z₀).IsInvertible := by
    simpa only [suppliedPhysicalPointFlowSpatialDifferential] using
      H.forward_fderiv_isInvertible ht₀
  apply isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_spatialC3
    (y₀ := y₀) (y₁ := y₁) (t := t)
    rt D K u₀ Phi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
      hendpoint hfullGerm hidentifyRHS hPhiTime hDPhiTime
      H.forward_spatialC3 hDPhiInv hrealize

end SuppliedPhysicalFlowAssembly

end Poincare
