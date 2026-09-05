import Mathlib.Analysis.Normed.Operator.NormedSpace
import Poincare.Global.MetricFlowJointIteratedConnectionRegularity

/-!
# Joint regularity of anchor-chart curvature

This module takes the next coordinate-level step from joint regularity of a
metric flow toward joint regularity of its scalar curvature.  A jointly `C²`
vector-valued map has a jointly `C¹` spatial Fréchet derivative.  Applying
this to the genuine, unflipped anchor-chart Christoffel field shows that its
`chartCurvatureOf` values on fixed chart vectors are jointly `C¹`.

The conclusion is deliberately chart-level.  Identifying the resulting
finite-basis contractions with intrinsic scalar curvature additionally needs
the inverse-metric trace bridge, which is not asserted here.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

section VectorValuedSpatialDerivative

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A jointly `C²` vector-valued map has a jointly `C¹` spatial Fréchet
derivative.  Only the second factor is differentiated. -/
theorem contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 1 (fun p : ℝ × V ↦ fderiv ℝ (F p.1) p.2) (t₀, x) := by
  let U : ℝ × V → W := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  have hU : ContDiffAt ℝ 2 U p := by
    simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 1 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 1) (by norm_num)
  have hcomp : ContDiffAt ℝ 1
      (fun q : ℝ × V ↦
        (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V)) p :=
    hDU.clm_comp contDiffAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt two_ne_zero
  have heq :
      (fun q : ℝ × V ↦ fderiv ℝ (F q.1) q.2) =ᶠ[nhds p]
        fun q ↦ (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    filter_upwards [hUnear] with q hq
    rcases q with ⟨t, z⟩
    have hslice : HasFDerivAt (fun z' : V ↦ U (t, z'))
        ((fderiv ℝ U (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ V)) z :=
      hq.hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)
    simpa [U] using hslice.fderiv
  exact hcomp.congr_of_eventuallyEq heq

/-- A jointly `C¹` vector-valued map has a jointly continuous spatial
Fréchet derivative. Only the second factor is differentiated. -/
theorem continuousAt_spatial_fderiv_of_joint_contDiffAt_one_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t₀, x)) :
    ContinuousAt (fun p : ℝ × V ↦ fderiv ℝ (F p.1) p.2) (t₀, x) := by
  let U : ℝ × V → W := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  have hU : ContDiffAt ℝ 1 U p := by
    simpa [U, p] using hF
  have hDU : ContinuousAt (fderiv ℝ U) p :=
    (hU.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hcomp : ContinuousAt
      (fun q : ℝ × V ↦
        (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V)) p :=
    hDU.clm_comp continuousAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt one_ne_zero
  have heq :
      (fun q : ℝ × V ↦ fderiv ℝ (F q.1) q.2) =ᶠ[nhds p]
        fun q ↦ (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    filter_upwards [hUnear] with q hq
    rcases q with ⟨t, z⟩
    have hslice : HasFDerivAt (fun z' : V ↦ U (t, z'))
        ((fderiv ℝ U (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ V)) z :=
      hq.hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)
    simpa [U] using hslice.fderiv
  exact hcomp.congr_of_eventuallyEq heq

end VectorValuedSpatialDerivative

section AbstractChartCurvature

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Joint `C²` regularity of a Christoffel field makes every fixed-vector
chart-curvature value jointly `C¹` in time and base point. -/
theorem chartCurvatureOf_jointContDiffAt_one_of_jointContDiffAt_two
    (Γ : ℝ → V → V →L[ℝ] V →L[ℝ] V)
    (t₀ : ℝ) (z u v w : V)
    (hΓ : ContDiffAt ℝ 2 (Function.uncurry Γ) (t₀, z)) :
    ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ chartCurvatureOf (Γ p.1) p.2 u v w) (t₀, z) := by
  have hΓ₁ : ContDiffAt ℝ 1 (Function.uncurry Γ) (t₀, z) :=
    hΓ.of_le (by norm_num)
  have hu₂ : ContDiffAt ℝ 2 (fun _ : ℝ × V ↦ u) (t₀, z) :=
    contDiffAt_const
  have hv₂ : ContDiffAt ℝ 2 (fun _ : ℝ × V ↦ v) (t₀, z) :=
    contDiffAt_const
  have hw₂ : ContDiffAt ℝ 2 (fun _ : ℝ × V ↦ w) (t₀, z) :=
    contDiffAt_const
  have hu : ContDiffAt ℝ 1 (fun _ : ℝ × V ↦ u) (t₀, z) :=
    contDiffAt_const
  have hv : ContDiffAt ℝ 1 (fun _ : ℝ × V ↦ v) (t₀, z) :=
    contDiffAt_const
  have hw : ContDiffAt ℝ 1 (fun _ : ℝ × V ↦ w) (t₀, z) :=
    contDiffAt_const
  have hΓvw₂ : ContDiffAt ℝ 2
      (Function.uncurry (fun t y ↦ Γ t y v w)) (t₀, z) := by
    simpa [Function.uncurry] using (hΓ.clm_apply hv₂).clm_apply hw₂
  have hΓuw₂ : ContDiffAt ℝ 2
      (Function.uncurry (fun t y ↦ Γ t y u w)) (t₀, z) := by
    simpa [Function.uncurry] using (hΓ.clm_apply hu₂).clm_apply hw₂
  have hDvw : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦
        fderiv ℝ (fun y ↦ Γ p.1 y v w) p.2) (t₀, z) :=
    contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      (fun t y ↦ Γ t y v w) t₀ z hΓvw₂
  have hDuw : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦
        fderiv ℝ (fun y ↦ Γ p.1 y u w) p.2) (t₀, z) :=
    contDiffAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      (fun t y ↦ Γ t y u w) t₀ z hΓuw₂
  have hDu : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦
        fderiv ℝ (fun y ↦ Γ p.1 y v w) p.2 u) (t₀, z) :=
    hDvw.clm_apply hu
  have hDv : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦
        fderiv ℝ (fun y ↦ Γ p.1 y u w) p.2 v) (t₀, z) :=
    hDuw.clm_apply hv
  have hΓu : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 u) (t₀, z) :=
    hΓ₁.clm_apply hu
  have hΓv : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 v) (t₀, z) :=
    hΓ₁.clm_apply hv
  have hΓvw : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 v w) (t₀, z) :=
    hΓv.clm_apply hw
  have hΓuw : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 u w) (t₀, z) :=
    hΓu.clm_apply hw
  have hProd₁ : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 u (Γ p.1 p.2 v w)) (t₀, z) :=
    hΓu.clm_apply hΓvw
  have hProd₂ : ContDiffAt ℝ 1
      (fun p : ℝ × V ↦ Γ p.1 p.2 v (Γ p.1 p.2 u w)) (t₀, z) :=
    hΓv.clm_apply hΓuw
  let R : ℝ × V → V := fun p ↦
    fderiv ℝ (fun y ↦ Γ p.1 y v w) p.2 u
      - fderiv ℝ (fun y ↦ Γ p.1 y u w) p.2 v
      + Γ p.1 p.2 u (Γ p.1 p.2 v w)
      - Γ p.1 p.2 v (Γ p.1 p.2 u w)
  have hR : ContDiffAt ℝ 1 R (t₀, z) := by
    simpa [R] using ((hDu.sub hDv).add hProd₁).sub hProd₂
  have hUnear : ∀ᶠ p in nhds (t₀, z),
      DifferentiableAt ℝ (Function.uncurry Γ) p :=
    (hΓ.eventually (by norm_num)).mono fun _ hp ↦
      hp.differentiableAt two_ne_zero
  have heq :
      (fun p : ℝ × V ↦ chartCurvatureOf (Γ p.1) p.2 u v w)
        =ᶠ[nhds (t₀, z)] R := by
    filter_upwards [hUnear] with p hp
    rcases p with ⟨t, y⟩
    have hslice : DifferentiableAt ℝ (Γ t) y := by
      have hpath : DifferentiableAt ℝ (fun y' : V ↦ (t, y')) y :=
        (hasFDerivAt_prodMk_right t y).differentiableAt
      have hcomp : DifferentiableAt ℝ
          ((Function.uncurry Γ) ∘ fun y' : V ↦ (t, y')) y :=
        DifferentiableAt.comp (𝕜 := ℝ)
          (f := fun y' : V ↦ (t, y'))
          (g := Function.uncurry Γ) (x := y) hp hpath
      simpa [Function.uncurry, Function.comp_def] using
        hcomp
    exact ChartCurvatureBridge.chartCurvatureOf_eq_fderiv_apply
      hslice u v w
  exact hR.congr_of_eventuallyEq heq

end AbstractChartCurvature

section AnchorChartCurvature

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "Iₘ" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The genuine section-first Christoffel field in a fixed anchor chart.
Unlike `anchorChartChristoffelFlow`, this definition is not flipped. -/
noncomputable def anchorChartChristoffelFieldFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) :
    ℝ → E → E →L[ℝ] E →L[ℝ] E := fun t ↦
  GeodesicTransport.chartChristoffelField (gt t) x

omit [T2Space M] in
@[simp] theorem anchorChartChristoffelFieldFlow_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z u v : E) :
    anchorChartChristoffelFieldFlow gt x t z u v =
      anchorChartChristoffelFlow gt x t z v u :=
  rfl

/-- Global joint `C³` metric entries make the actual, unflipped
anchor-chart Christoffel field jointly `C²`. -/
theorem anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 2
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  have hΓ :=
    anchorChartChristoffelFlow_jointContDiffAt_two_of_metricEntries hJoint
  apply contDiffAt_clm_path_of_apply
  intro u
  apply contDiffAt_clm_path_of_apply
  intro v
  have hu : ContDiffAt ℝ 2
      (fun _ : ℝ × E ↦ u) (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  have hv : ContDiffAt ℝ 2
      (fun _ : ℝ × E ↦ v) (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  simpa [Function.uncurry] using (hΓ.clm_apply hv).clm_apply hu

/-- Chart curvature of the actual unflipped anchor Christoffel field. -/
noncomputable def anchorChartCurvatureFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z u v w : E) : E :=
  chartCurvatureOf (anchorChartChristoffelFieldFlow gt x t) z u v w

/-- Global joint `C³` metric entries make every fixed-vector anchor-chart
curvature value jointly `C¹` in time and chart base point. -/
theorem anchorChartCurvatureFlow_jointContDiffAt_one_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (u v w : E) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (fun t z ↦ anchorChartCurvatureFlow gt x t z u v w))
      (t₀, extChartAt Iₘ x x) := by
  exact chartCurvatureOf_jointContDiffAt_one_of_jointContDiffAt_two
    (anchorChartChristoffelFieldFlow gt x) t₀
    (extChartAt Iₘ x x) u v w
    (anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries
      hJoint)

/-- In particular, fixed-vector anchor-chart curvature is jointly continuous
at the time-space anchor. -/
theorem anchorChartCurvatureFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (u v w : E) :
    ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCurvatureFlow gt x t z u v w))
      (t₀, extChartAt Iₘ x x) :=
  (anchorChartCurvatureFlow_jointContDiffAt_one_of_metricEntries
    hJoint u v w).continuousAt

/-! ## Finite-basis Ricci and scalar contractions -/

/-- The coordinate Ricci entry obtained by tracing
`u ↦ chartCurvatureOf Γ u v w` in the fixed model basis. -/
noncomputable def anchorChartRicciEntryFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z v w : E) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, LinearMap.toContinuousLinearMap (b.coord i)
    (anchorChartCurvatureFlow gt x t z (b i) v w)

/-- Fixed-vector coordinate Ricci entries inherit joint `C¹` regularity from
the chart-curvature flow. -/
theorem anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (v w : E) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (fun t z ↦ anchorChartRicciEntryFlow gt x t z v w))
      (t₀, extChartAt Iₘ x x) := by
  classical
  let b := Module.finBasis ℝ E
  unfold anchorChartRicciEntryFlow
  dsimp only
  apply ContDiffAt.sum
  intro i _
  have hR := anchorChartCurvatureFlow_jointContDiffAt_one_of_metricEntries
    hJoint (b i) v w
  have hcoord : ContDiffAt ℝ 1
      (fun _ : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord i))
      (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  simpa [Function.uncurry] using hcoord.clm_apply hR

/-- The inverse cutoff-blended chart metric is jointly `C²` at the anchor.
This is the coordinate index-raising operator used below. -/
theorem anchorBlendedMetricFlow_inverse_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, extChartAt Iₘ x x) := by
  let q : E := extChartAt Iₘ x x
  have hG : ContDiffAt ℝ 3
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    anchorBlendedMetricFlow_jointContDiffAt_three_of_metricEntries hJoint
  have hG₂ : ContDiffAt ℝ 2
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    hG.of_le (by norm_num)
  exact ((anchorBlendedMetricFlow_isInvertible gt x t₀ q)
    |>.contDiffAt_map_inverse).comp (t₀, q) hG₂

/-- A fixed matrix coefficient of the inverse cutoff-blended chart metric. -/
noncomputable def anchorChartInverseMetricCoeffFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E)
    (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  let b := Module.finBasis ℝ E
  LinearMap.toContinuousLinearMap (b.coord k)
    ((anchorBlendedMetricFlow gt x t z).inverse
      (LinearMap.toContinuousLinearMap (b.coord i)))

/-- Inverse-metric coefficients are jointly `C²` under joint `C³` metric
entries. -/
theorem anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ 2
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z i k))
      (t₀, extChartAt Iₘ x x) := by
  let b := Module.finBasis ℝ E
  have hInv :=
    anchorBlendedMetricFlow_inverse_jointContDiffAt_two_of_metricEntries hJoint
  have hcoordI : ContDiffAt ℝ 2
      (fun _ : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord i))
      (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  have hraised : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse
        (LinearMap.toContinuousLinearMap (b.coord i)))
      (t₀, extChartAt Iₘ x x) :=
    hInv.clm_apply hcoordI
  have hcoordK : ContDiffAt ℝ 2
      (fun _ : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord k))
      (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  simpa [anchorChartInverseMetricCoeffFlow, b, Function.uncurry] using
    hcoordK.clm_apply hraised

/-- The finite-coordinate scalar contraction of the anchor-chart curvature.
It is the inverse-metric trace of `anchorChartRicciEntryFlow`, expanded in the
fixed model basis.  No equality with intrinsic scalar curvature is built into
this definition. -/
noncomputable def anchorChartScalarTraceFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, ∑ k,
    anchorChartInverseMetricCoeffFlow gt x t z i k *
      anchorChartRicciEntryFlow gt x t z (b i) (b k)

/-- The finite-coordinate scalar trace is jointly `C¹` at the time-space
anchor. -/
theorem anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 1
      (Function.uncurry (anchorChartScalarTraceFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  classical
  let b := Module.finBasis ℝ E
  unfold anchorChartScalarTraceFlow
  dsimp only
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  have hInv : ContDiffAt ℝ 1
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z i k))
      (t₀, extChartAt Iₘ x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint i k).of_le (by norm_num)
  have hRic :=
    anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
      hJoint (b i) (b k)
  exact hInv.mul hRic

/-- In particular, the finite-coordinate scalar trace is jointly continuous
at the time-space anchor. -/
theorem anchorChartScalarTraceFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt
      (Function.uncurry (anchorChartScalarTraceFlow gt x))
      (t₀, extChartAt Iₘ x x) :=
  (anchorChartScalarTraceFlow_jointContDiffAt_one_of_metricEntries
    hJoint).continuousAt

end AnchorChartCurvature

end Poincare
