import Poincare.Global.MetricFlowJointScalarTraceZoneBridge
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction

/-!
# Automatic joint continuity of the scalar time derivative

Joint `C³` metric entries make the finite anchor-chart scalar trace jointly
`C¹`.  A general product-calculus lemma identifies the continuous time
partial of a jointly `C¹` function with the actual one-variable `deriv`.

On the cutoff-one part of an honest anchor chart, the finite scalar trace is
intrinsic scalar curvature for every time.  The cutoff and chart-source
conditions are purely spatial, so this identity may be differentiated
slice-wise before composing the continuous chart partial back to the
manifold.  Pointwise continuity at every spacetime anchor then gives global
joint continuity.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section ProductCalculus

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual time derivative of a jointly `C¹` function is jointly
continuous.  The proof identifies it locally with the total Fréchet
derivative applied to the fixed time direction `(1,0)`. -/
theorem continuousAt_joint_timeDeriv_of_joint_contDiffAt_one
    (F : ℝ → V → ℝ) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t₀, x)) :
    ContinuousAt
      (fun p : ℝ × V ↦ deriv (fun t ↦ F t p.2) p.1) (t₀, x) := by
  let U : ℝ × V → ℝ := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  let dt : ℝ × V := (1, 0)
  let B : ℝ × V → ℝ := fun q ↦ deriv (fun t ↦ F t q.2) q.1
  let Btotal : ℝ × V → ℝ := fun q ↦ fderiv ℝ U q dt
  have hU : ContDiffAt ℝ 1 U p := by
    simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 0 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 0) (by norm_num)
  have hBtotal : ContinuousAt Btotal p := by
    simpa [Btotal] using
      hDU.continuousAt.clm_apply (continuousAt_const :
        ContinuousAt (fun _ : ℝ × V ↦ dt) p)
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt one_ne_zero
  have hBeq : B =ᶠ[nhds p] Btotal := by
    filter_upwards [hUnear] with q hq
    rcases q with ⟨s, z⟩
    have hcomp : HasFDerivAt (U ∘ fun t : ℝ ↦ (t, z))
        ((fderiv ℝ U (s, z)).comp
          (ContinuousLinearMap.inl ℝ ℝ V)) s :=
      hq.hasFDerivAt.comp s (hasFDerivAt_prodMk_left s z)
    have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  exact hBtotal.congr_of_eventuallyEq hBeq

end ProductCalculus

section IntrinsicScalar

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Joint `C³` metric-entry regularity at one spacetime point makes the
actual scalar-curvature time derivative jointly continuous there. -/
theorem continuousAt_scalarTimeDerivative_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt (fun p : ℝ × M ↦
      deriv (fun t ↦ (gt t).scalarAt p.2) p.1) (t₀, x) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : ℝ × M ↦ extChartAt I x p.2) (t₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (t₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : ℝ × M ↦ (p.1, extChartAt I x p.2)) (t₀, x) :=
    continuousAt_fst.prodMk hchart
  have htrace : ContinuousAt
      (fun p : ℝ × E ↦
        deriv (fun t ↦ anchorChartScalarTraceFlow gt x t p.2) p.1)
      (t₀, extChartAt I x x) :=
    continuousAt_joint_timeDeriv_of_joint_contDiffAt_one
      (anchorChartScalarTraceFlow gt x) t₀ (extChartAt I x x)
      (anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries
        hJoint)
  have hchartDerivative : ContinuousAt
      (fun p : ℝ × M ↦
        deriv
          (fun t ↦ anchorChartScalarTraceFlow gt x t
            (extChartAt I x p.2)) p.1) (t₀, x) := by
    exact ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      (g := fun p : ℝ × E ↦
        deriv (fun t ↦ anchorChartScalarTraceFlow gt x t p.2) p.1)
      (x := (t₀, x)) htrace hchartPair
  have hsource : ∀ᶠ y : M in nhds x,
      y ∈ (extChartAt I x).source :=
    extChartAt_source_mem_nhds x
  have hone : ∀ᶠ y : M in nhds x,
      extChartAt I x y ∈ oneLocus :=
    (continuousAt_extChartAt x).eventually hone_mem
  have hDerivativeEqSpace : ∀ᶠ y : M in nhds x, ∀ t : ℝ,
      deriv (fun s ↦ (gt s).scalarAt y) t =
        deriv (fun s ↦
          anchorChartScalarTraceFlow gt x s (extChartAt I x y)) t := by
    filter_upwards [hsource, hone] with y hySource hyOne
    intro t
    have hz : extChartAt I x y ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hySource
    have hχone : ∀ᶠ z' in nhds (extChartAt I x y),
        GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hyOne
    have hfun : (fun s ↦ (gt s).scalarAt y) =
        (fun s ↦
          anchorChartScalarTraceFlow gt x s (extChartAt I x y)) := by
      funext s
      symm
      calc
        anchorChartScalarTraceFlow gt x s (extChartAt I x y) =
            (gt s).scalarAt
              ((extChartAt I x).symm (extChartAt I x y)) :=
          anchorChartScalarTraceFlow_eq_scalarAt_zone gt x s hz hχone
        _ = (gt s).scalarAt y := by
          rw [(extChartAt I x).left_inv hySource]
    rw [hfun]
  have hDerivativeEq :
      (fun p : ℝ × M ↦
        deriv (fun t ↦ (gt t).scalarAt p.2) p.1) =ᶠ[nhds (t₀, x)]
      (fun p : ℝ × M ↦
        deriv
          (fun t ↦ anchorChartScalarTraceFlow gt x t
            (extChartAt I x p.2)) p.1) := by
    filter_upwards [continuousAt_snd.eventually hDerivativeEqSpace] with p hp
    exact hp p.1
  exact hchartDerivative.congr_of_eventuallyEq hDerivativeEq

/-- Pointwise joint `C³` metric entries make the actual scalar time
derivative globally jointly continuous. -/
theorem continuous_scalarTimeDerivative_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    Continuous (fun p : ℝ × M ↦
      deriv (fun t ↦ (gt t).scalarAt p.2) p.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact
    continuousAt_scalarTimeDerivative_joint_of_metricEntriesJointContDiffAt_three
      (hJoint p.1 p.2)

/-- Alias in the exact contract consumed by the Hausdorff domination
reduction. -/
theorem scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    ScalarTimeDerivativeJointContinuous gt :=
  continuous_scalarTimeDerivative_joint_of_metricEntriesJointContDiffAt_three
    hJoint

end IntrinsicScalar

end Poincare
