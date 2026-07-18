import Poincare.Global.DeTurckCoordinateJointRegularity

/-!
# Joint C3 regularity of the coordinate DeTurck field

The DeTurck coordinate field contains one spatial derivative of the metric.
Consequently joint `C⁴` metric entries give the joint `C³` vector-field
regularity required by the third-order point-flow variational tower.

This module is the one-order-higher counterpart of
`DeTurckCoordinateJointRegularity`: it proves the complete regularity budget
from metric entries, through the Christoffel contraction, to the actual
coordinate representative in the cutoff-one chart zone.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace Poincare

section FourthOrderSpatialDerivative

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A jointly `C⁴` vector-valued family has a jointly `C³` spatial
Frechet derivative. -/
theorem contDiffAt_spatial_fderiv_of_joint_contDiffAt_four_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 4 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 3
      (fun p : ℝ × V ↦ fderiv ℝ (F p.1) p.2) (t₀, x) := by
  let U : ℝ × V → W := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  have hU : ContDiffAt ℝ 4 U p := by
    simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 3 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 3) (by norm_num)
  have hcomp : ContDiffAt ℝ 3
      (fun q : ℝ × V ↦
        (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V)) p :=
    hDU.clm_comp contDiffAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt (by norm_num)
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

end FourthOrderSpatialDerivative

namespace DeTurckCoordinateJointRegularityThree

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "Iₘ" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace Iₘ : M → Type _)

/-- A fixed smooth metric has joint `C⁴` entries when regarded as a
time-independent family. -/
theorem metricEntriesJointContDiffAt_const_four
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    MetricEntriesJointContDiffAt (fun _ : ℝ ↦ bg) t₀ x 4 := by
  intro b c
  let e := extChartAt Iₘ x
  let q : E := e x
  letI : RiemannianBundle TM := bg.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle Iₘ ∞ E TM :=
    bg.toIsContMDiffRiemannianBundle
  have hpair : ContMDiffAt Iₘ 𝓘(ℝ) 4
      (fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) x := by
    have hinner : ContMDiffAt Iₘ 𝓘(ℝ) 4
        (fun y : M ↦ inner ℝ (extend E b y) (extend E c y)) x :=
      ContMDiffAt.inner_bundle
        (FiberBundle.contMDiffAt_extend' (k := 4) Iₘ E b)
        (FiberBundle.contMDiffAt_extend' (k := 4) Iₘ E c)
    simpa [ClosedSmoothRiemannianMetric.fiber_inner_eq] using hinner
  have heSymmTop : ContMDiffOn 𝓘(ℝ, E) Iₘ ∞ e.symm e.target := by
    simpa [e] using (contMDiffOn_extChartAt_symm (I := Iₘ) x)
  have hfour_le_top : (4 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (4 : ℕ∞ω) = ((4 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have heSymm : ContMDiffAt 𝓘(ℝ, E) Iₘ 4 e.symm q := by
    exact (heSymmTop.of_le hfour_le_top).contMDiffAt
      ((isOpen_extChartAt_target (I := Iₘ) x).mem_nhds
        (mem_extChartAt_target (I := Iₘ) x))
  have heSymm_q : e.symm q = x :=
    e.left_inv (mem_extChartAt_source (I := Iₘ) x)
  have hpair' : ContMDiffAt Iₘ 𝓘(ℝ) 4
      (fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) (e.symm q) := by
    simpa only [heSymm_q] using hpair
  have hchartMD : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 4
      ((fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) ∘ e.symm) q :=
    hpair'.comp q heSymm
  have hchart : ContDiffAt ℝ 4
      ((fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) ∘ e.symm) q :=
    contMDiffAt_iff_contDiffAt.mp hchartMD
  have hjoint := hchart.comp (t₀, q)
    (contDiffAt_snd : ContDiffAt ℝ 4 (Prod.snd : ℝ × E → E) (t₀, q))
  simpa [metricEntryJointChart, e, q, Function.comp_def] using hjoint

/-- Joint `C⁴` entries give joint `C⁴` regularity of the cutoff-blended
chart metric near the preferred-chart anchor. -/
theorem anchorBlendedMetricFlow_jointContDiffAt_four_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 4 (Function.uncurry (anchorBlendedMetricFlow gt x))
      (t₀, extChartAt Iₘ x x) :=
  (anchorChartMetricFlow_jointContDiffAt_of_metricEntries hJoint)
    |>.congr_of_eventuallyEq
      (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow gt t₀ x)

/-- A joint `C⁴` metric family has a joint `C³` spatial Koszul
covector. -/
theorem jointChristoffelCovectorAt_contDiffAt_three
    (G : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (t₀ : ℝ) (z u v : E)
    (hG : ContDiffAt ℝ 4 (Function.uncurry G) (t₀, z)) :
    ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ jointChristoffelCovectorAt G p.1 p.2 u v)
      (t₀, z) := by
  have hD := contDiffAt_spatial_fderiv_of_joint_contDiffAt_four_vector
    G t₀ z hG
  apply contDiffAt_clm_path_of_apply
  intro w
  have hu : ContDiffAt ℝ 3 (fun _ : ℝ × E ↦ u) (t₀, z) :=
    contDiffAt_const
  have hv : ContDiffAt ℝ 3 (fun _ : ℝ × E ↦ v) (t₀, z) :=
    contDiffAt_const
  have hw : ContDiffAt ℝ 3 (fun _ : ℝ × E ↦ w) (t₀, z) :=
    contDiffAt_const
  have h₁ := ((hD.clm_apply hu).clm_apply hv).clm_apply hw
  have h₂ := ((hD.clm_apply hv).clm_apply hu).clm_apply hw
  have h₃ := ((hD.clm_apply hw).clm_apply hu).clm_apply hv
  simpa [jointChristoffelCovectorAt, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply] using
      ((h₁.add h₂).sub h₃).const_smul (1 / 2 : ℝ)

/-- Joint `C⁴` metric entries make the flipped anchor-chart Christoffel
flow jointly `C³`. -/
theorem anchorChartChristoffelFlow_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 3 (Function.uncurry (anchorChartChristoffelFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  let q : E := extChartAt Iₘ x x
  have hG : ContDiffAt ℝ 4
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    anchorBlendedMetricFlow_jointContDiffAt_four_of_metricEntries hJoint
  have hG₃ : ContDiffAt ℝ 3
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    hG.of_le (show (3 : ℕ∞ω) ≤ 4 by norm_num)
  have hInv : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, q) := by
    exact ((anchorBlendedMetricFlow_isInvertible gt x t₀ q)
      |>.contDiffAt_map_inverse).comp (t₀, q) hG₃
  apply contDiffAt_clm_path_of_apply
  intro u
  apply contDiffAt_clm_path_of_apply
  intro v
  have hK : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ jointChristoffelCovectorAt
        (anchorBlendedMetricFlow gt x) p.1 p.2 u v) (t₀, q) :=
    jointChristoffelCovectorAt_contDiffAt_three
      (anchorBlendedMetricFlow gt x) t₀ q u v hG
  have heq :
      (fun p : ℝ × E ↦ anchorChartChristoffelFlow gt x p.1 p.2 u v) =
        fun p ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse
          (jointChristoffelCovectorAt
            (anchorBlendedMetricFlow gt x) p.1 p.2 u v) := by
    funext p
    exact anchorChartChristoffelFlow_apply_eq_inverse_koszul
      gt x p.1 p.2 u v
  change ContDiffAt ℝ 3
    (fun p : ℝ × E ↦ anchorChartChristoffelFlow gt x p.1 p.2 u v)
    (t₀, q)
  rw [heq]
  exact hInv.clm_apply hK

/-- The genuine unflipped anchor-chart Christoffel field is jointly `C³`
under joint `C⁴` metric-entry regularity. -/
theorem anchorChartChristoffelFieldFlow_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 3
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  have hGamma :=
    anchorChartChristoffelFlow_jointContDiffAt_three_of_metricEntries hJoint
  apply contDiffAt_clm_path_of_apply
  intro u
  apply contDiffAt_clm_path_of_apply
  intro v
  have hu : ContDiffAt ℝ 3
      (fun _ : ℝ × E ↦ u) (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  have hv : ContDiffAt ℝ 3
      (fun _ : ℝ × E ↦ v) (t₀, extChartAt Iₘ x x) :=
    contDiffAt_const
  simpa [Function.uncurry] using (hGamma.clm_apply hv).clm_apply hu

/-- The inverse cutoff-blended chart metric is jointly `C³` under joint
`C⁴` metric-entry regularity. -/
theorem anchorBlendedMetricFlow_inverse_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, extChartAt Iₘ x x) := by
  let q : E := extChartAt Iₘ x x
  have hG : ContDiffAt ℝ 4
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    anchorBlendedMetricFlow_jointContDiffAt_four_of_metricEntries hJoint
  exact ((anchorBlendedMetricFlow_isInvertible gt x t₀ q)
    |>.contDiffAt_map_inverse).comp (t₀, q)
      (hG.of_le (show (3 : ℕ∞ω) ≤ 4 by norm_num))

/-- Joint `C⁴` evolving metric entries make the explicit coordinate
DeTurck contraction jointly `C³`. -/
theorem anchorChartDeTurckContractionFlow_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 3
      (Function.uncurry
        (DeTurckCoordinateJointRegularity.anchorChartDeTurckContractionFlow
          gt bg x))
      (t₀, extChartAt Iₘ x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt Iₘ x x
  have hbg : MetricEntriesJointContDiffAt (fun _ : ℝ ↦ bg) t₀ x 4 :=
    metricEntriesJointContDiffAt_const_four bg t₀ x
  have hGammaG : ContDiffAt ℝ 3
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_three_of_metricEntries hgt
  have hGammaB : ContDiffAt ℝ 3
      (Function.uncurry
        (anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_three_of_metricEntries hbg
  have hInv : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, q) := by
    simpa [q] using
      anchorBlendedMetricFlow_inverse_jointContDiffAt_three_of_metricEntries hgt
  unfold DeTurckCoordinateJointRegularity.anchorChartDeTurckContractionFlow
  apply ContDiffAt.sum
  intro i _hi
  let coord : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (b.coord i)
  have hcoord : ContDiffAt ℝ 3 (fun _ : ℝ × E ↦ coord) (t₀, q) :=
    contDiffAt_const
  have hraised : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦
        (anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (t₀, q) :=
    hInv.clm_apply hcoord
  have hbi : ContDiffAt ℝ 3 (fun _ : ℝ × E ↦ b i) (t₀, q) :=
    contDiffAt_const
  have hGammaGi : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦ anchorChartChristoffelFieldFlow gt x p.1 p.2
        ((anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (b i))
      (t₀, q) := by
    simpa [Function.uncurry] using
      (hGammaG.clm_apply hraised).clm_apply hbi
  have hGammaBi : ContDiffAt ℝ 3
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x p.1 p.2
          ((anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (b i))
      (t₀, q) := by
    simpa [Function.uncurry] using
      (hGammaB.clm_apply hraised).clm_apply hbi
  simpa [Function.uncurry, q, coord] using hGammaGi.sub hGammaBi

/-- Joint `C⁴` metric entries make the actual coordinate representative
of the intrinsic DeTurck field jointly `C³` at the preferred-chart anchor. -/
theorem deTurckChartCoordinateField_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : MetricEntriesJointContDiffAt gt t₀ x 4) :
    ContDiffAt ℝ 3
      (Function.uncurry (fun t z ↦
        chartCoordinateTangentField x (deTurckVectorField gt bg t) z))
      (t₀, extChartAt Iₘ x x) := by
  let q : E := extChartAt Iₘ x x
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have htargetMem : (extChartAt Iₘ x).target ∈ nhds q :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have honeOpen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have honeMem : oneLocus ∈ nhds q := by
    apply honeOpen.mem_nhds
    simpa [oneLocus, q] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have htargetPair :
      ∀ᶠ p : ℝ × E in nhds (t₀, q), p.2 ∈ (extChartAt Iₘ x).target :=
    continuousAt_snd.eventually htargetMem
  have honePair :
      ∀ᶠ p : ℝ × E in nhds (t₀, q), p.2 ∈ oneLocus :=
    continuousAt_snd.eventually honeMem
  have heq :
      Function.uncurry (fun t z ↦
          chartCoordinateTangentField x (deTurckVectorField gt bg t) z)
        =ᶠ[nhds (t₀, q)]
      Function.uncurry
        (DeTurckCoordinateJointRegularity.anchorChartDeTurckContractionFlow
          gt bg x) := by
    filter_upwards [htargetPair, honePair] with p hpTarget hpOne
    have hχone : ∀ᶠ z' in nhds p.2,
        GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    simpa only [Function.uncurry] using
      (DeTurckCoordinateJointRegularity.anchorChartDeTurckContractionFlow_eq_chartCoordinateTangentField_zone
        gt bg x p.1 hpTarget hχone).symm
  have hcontraction :=
    anchorChartDeTurckContractionFlow_jointContDiffAt_three_of_metricEntries
      (bg := bg) hgt
  simpa [q] using hcontraction.congr_of_eventuallyEq heq

end DeTurckCoordinateJointRegularityThree

end Poincare
