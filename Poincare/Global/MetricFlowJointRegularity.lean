import Poincare.Global.ScalarEvolution

/-!
# Joint time-space regularity for metric flows

The scalar-evolution assembly needs a Schwarz interchange between the time
derivative of a metric and one spatial exterior derivative.  This module
derives that interchange from ordinary `C²` regularity of the corresponding
joint chart entry.  At `C³`, the same hypothesis also supplies pointwise time
differentiability and spatial `C²` regularity of the metric variation.

The remaining `MetricFlowRegularAt` input concerns time differentiation of
iterated Levi-Civita connection values.  It is kept explicit: deriving that
structure requires a separate joint regularity theorem for the Christoffel
formula, not merely scalar mixed-partial symmetry.
-/

noncomputable section

open Bundle FiberBundle Filter Set Function
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

section EuclideanMixedPartial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A `C²` scalar function on time-space has commuting time and spatial
partials.  The conclusion is phrased as the exact `HasDerivAt` statement
consumed by the metric Koszul argument. -/
theorem hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
    (F : ℝ → V → ℝ) (t₀ : ℝ) (x a : V)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
    HasDerivAt
      (fun t ↦ fderiv ℝ (F t) x a)
      (fderiv ℝ (fun z ↦ deriv (fun t ↦ F t z) t₀) x a) t₀ := by
  let U : ℝ × V → ℝ := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  let dt : ℝ × V := (1, 0)
  let dx : ℝ × V := (0, a)
  have hU : ContDiffAt ℝ 2 U p := by
    simpa [U, p] using hF
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) p :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have htimePath : HasDerivAt (fun t : ℝ ↦ (t, x)) dt t₀ := by
    simpa [dt] using
      (hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ x)
  have hDtime : HasDerivAt (fun t : ℝ ↦ fderiv ℝ U (t, x))
      (fderiv ℝ (fderiv ℝ U) p dt) t₀ := by
    simpa [p] using
      (hDU.hasFDerivAt.comp t₀ htimePath.hasFDerivAt).hasDerivAt
  have hAtotal : HasDerivAt
      (fun t : ℝ ↦ fderiv ℝ U (t, x) dx)
      (fderiv ℝ (fderiv ℝ U) p dt dx) t₀ := by
    simpa using hDtime.clm_apply (hasDerivAt_const t₀ dx)
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt two_ne_zero
  have hUnearTime : ∀ᶠ t in nhds t₀, DifferentiableAt ℝ U (t, x) :=
    htimePath.continuousAt.eventually hUnear
  have hspaceEq :
      (fun t : ℝ ↦ fderiv ℝ U (t, x) dx) =ᶠ[nhds t₀]
        fun t ↦ fderiv ℝ (F t) x a := by
    filter_upwards [hUnearTime] with t ht
    have hcomp : HasFDerivAt (fun z : V ↦ U (t, z))
        ((fderiv ℝ U (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V)) x :=
      ht.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    have happ := congrArg (fun L : V →L[ℝ] ℝ ↦ L a) hcomp.fderiv
    simpa [U, dx, Function.comp_def, ContinuousLinearMap.comp_apply] using
      happ.symm
  have hA : HasDerivAt
      (fun t ↦ fderiv ℝ (F t) x a)
      (fderiv ℝ (fderiv ℝ U) p dt dx) t₀ :=
    hAtotal.congr_of_eventuallyEq hspaceEq.symm
  let B : V → ℝ := fun z ↦ deriv (fun t ↦ F t z) t₀
  let Btotal : V → ℝ := fun z ↦ fderiv ℝ U (t₀, z) dt
  have hspacePath : HasFDerivAt (fun z : V ↦ (t₀, z))
      (ContinuousLinearMap.inr ℝ ℝ V) x :=
    hasFDerivAt_prodMk_right t₀ x
  have hDspace : HasFDerivAt (fun z : V ↦ fderiv ℝ U (t₀, z))
      ((fderiv ℝ (fderiv ℝ U) p).comp
        (ContinuousLinearMap.inr ℝ ℝ V)) x := by
    simpa [p] using hDU.hasFDerivAt.comp x hspacePath
  have hBtotal := hDspace.clm_apply (hasFDerivAt_const dt x)
  have hUnearSpace : ∀ᶠ z in nhds x, DifferentiableAt ℝ U (t₀, z) :=
    hspacePath.continuousAt.eventually hUnear
  have hBeq : B =ᶠ[nhds x] Btotal := by
    filter_upwards [hUnearSpace] with z hz
    have hcomp : HasFDerivAt (U ∘ fun t : ℝ ↦ (t, z))
        ((fderiv ℝ U (t₀, z)).comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ :=
      hz.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_left t₀ z)
    have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  have hBvalue : fderiv ℝ B x a =
      fderiv ℝ (fderiv ℝ U) p dx dt := by
    rw [hBeq.fderiv_eq, hBtotal.fderiv]
    simp [Btotal, dx, dt, ContinuousLinearMap.comp_apply]
  have hsymm := hU.isSymmSndFDerivAt (by norm_num) dt dx
  apply hA.congr_deriv
  rw [hBvalue]
  exact hsymm

/-- A joint `C²` function has a spatially `C¹` time partial. -/
theorem contDiffAt_timeDeriv_one_of_joint_contDiffAt_two
    (F : ℝ → V → ℝ) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 1 (fun z ↦ deriv (fun t ↦ F t z) t₀) x := by
  let U : ℝ × V → ℝ := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  let dt : ℝ × V := (1, 0)
  let B : V → ℝ := fun z ↦ deriv (fun t ↦ F t z) t₀
  let Btotal : V → ℝ := fun z ↦ fderiv ℝ U (t₀, z) dt
  have hU : ContDiffAt ℝ 2 U p := by simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 1 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 1) (by norm_num)
  have hspacePath : ContDiffAt ℝ 1 (fun z : V ↦ (t₀, z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  have hBtotal : ContDiffAt ℝ 1 Btotal x := by
    have hcomp := hDU.comp x hspacePath
    simpa [Btotal, p] using hcomp.clm_apply contDiffAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt two_ne_zero
  have hspacePath' : ContinuousAt (fun z : V ↦ (t₀, z)) x :=
    continuousAt_const.prodMk continuousAt_id
  have hUnearSpace : ∀ᶠ z in nhds x, DifferentiableAt ℝ U (t₀, z) :=
    hspacePath'.eventually hUnear
  have hBeq : B =ᶠ[nhds x] Btotal := by
    filter_upwards [hUnearSpace] with z hz
    have hcomp : HasFDerivAt (U ∘ fun t : ℝ ↦ (t, z))
        ((fderiv ℝ U (t₀, z)).comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ :=
      hz.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_left t₀ z)
    have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  exact hBtotal.congr_of_eventuallyEq hBeq

/-- A joint `C³` function has a spatially `C²` time partial. -/
theorem contDiffAt_timeDeriv_two_of_joint_contDiffAt_three
    (F : ℝ → V → ℝ) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 3 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 2 (fun z ↦ deriv (fun t ↦ F t z) t₀) x := by
  let U : ℝ × V → ℝ := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  let dt : ℝ × V := (1, 0)
  let B : V → ℝ := fun z ↦ deriv (fun t ↦ F t z) t₀
  let Btotal : V → ℝ := fun z ↦ fderiv ℝ U (t₀, z) dt
  have hU : ContDiffAt ℝ 3 U p := by simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 2 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 2) (by norm_num)
  have hspacePath : ContDiffAt ℝ 2 (fun z : V ↦ (t₀, z)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  have hBtotal : ContDiffAt ℝ 2 Btotal x := by
    have hcomp := hDU.comp x hspacePath
    simpa [Btotal, p] using hcomp.clm_apply contDiffAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt three_ne_zero
  have hspacePath' : ContinuousAt (fun z : V ↦ (t₀, z)) x :=
    continuousAt_const.prodMk continuousAt_id
  have hUnearSpace : ∀ᶠ z in nhds x, DifferentiableAt ℝ U (t₀, z) :=
    hspacePath'.eventually hUnear
  have hBeq : B =ᶠ[nhds x] Btotal := by
    filter_upwards [hUnearSpace] with z hz
    have hcomp : HasFDerivAt (U ∘ fun t : ℝ ↦ (t, z))
        ((fderiv ℝ U (t₀, z)).comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ :=
      hz.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_left t₀ z)
    have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  exact hBtotal.congr_of_eventuallyEq hBeq

end EuclideanMixedPartial

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "Iₘ" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace Iₘ : M → Type _)

/-- The joint time-chart representative of a metric entry in the canonical
extension frame based at `x`. -/
noncomputable def metricEntryJointChart
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (b c : TM x) : ℝ × E → ℝ := fun p ↦
  let y := (extChartAt Iₘ x).symm p.2
  (gt p.1).inner y (extend E b y) (extend E c y)

/-- Natural joint time-space regularity of all metric entries in the
canonical frame of the anchor chart. -/
def MetricEntriesJointContDiffAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (k : ℕ∞ω) : Prop :=
  ∀ b c : TM x, ContDiffAt ℝ k (metricEntryJointChart gt x b c)
    (t₀, extChartAt Iₘ x x)

theorem MetricEntriesJointContDiffAt.of_le
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    {k l : ℕ∞ω} (h : MetricEntriesJointContDiffAt gt t₀ x l)
    (hkl : k ≤ l) : MetricEntriesJointContDiffAt gt t₀ x k :=
  fun b c ↦ (h b c).of_le hkl

/-- A fixed smooth Riemannian metric has jointly `C³` entries when regarded
as a time-independent metric family. -/
theorem metricEntriesJointContDiffAt_const
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    MetricEntriesJointContDiffAt (fun _ : ℝ ↦ bg) t₀ x 3 := by
  intro b c
  let e := extChartAt Iₘ x
  let q : E := e x
  letI : RiemannianBundle TM := bg.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle Iₘ ∞ E TM :=
    bg.toIsContMDiffRiemannianBundle
  have hpair : ContMDiffAt Iₘ 𝓘(ℝ) 3
      (fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) x := by
    have hinner : ContMDiffAt Iₘ 𝓘(ℝ) 3
        (fun y : M ↦ inner ℝ (extend E b y) (extend E c y)) x :=
      ContMDiffAt.inner_bundle
        (FiberBundle.contMDiffAt_extend' (k := 3) Iₘ E b)
        (FiberBundle.contMDiffAt_extend' (k := 3) Iₘ E c)
    simpa [ClosedSmoothRiemannianMetric.fiber_inner_eq] using hinner
  have heSymmTop : ContMDiffOn 𝓘(ℝ, E) Iₘ ∞ e.symm e.target := by
    simpa [e] using (contMDiffOn_extChartAt_symm (I := Iₘ) x)
  have hthree_le_top : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have heSymm : ContMDiffAt 𝓘(ℝ, E) Iₘ 3 e.symm q := by
    exact (heSymmTop.of_le hthree_le_top).contMDiffAt
        ((isOpen_extChartAt_target (I := Iₘ) x).mem_nhds
          (mem_extChartAt_target (I := Iₘ) x))
  have heSymm_q : e.symm q = x := by
    exact e.left_inv (mem_extChartAt_source (I := Iₘ) x)
  have hpair' : ContMDiffAt Iₘ 𝓘(ℝ) 3
      (fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) (e.symm q) := by
    simpa only [heSymm_q] using hpair
  have hchartMD : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 3
      ((fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) ∘ e.symm) q :=
    hpair'.comp q heSymm
  have hchart : ContDiffAt ℝ 3
      ((fun y : M ↦ bg.inner y (extend E b y) (extend E c y)) ∘ e.symm) q :=
    contMDiffAt_iff_contDiffAt.mp hchartMD
  have hjoint := hchart.comp (t₀, q)
    (contDiffAt_snd : ContDiffAt ℝ 3 (Prod.snd : ℝ × E → E) (t₀, q))
  simpa [metricEntryJointChart, e, q, Function.comp_def] using hjoint

/-- Lift a regular scalar representative in the anchor chart back to a
manifold `ContMDiffAt` statement. -/
private theorem contMDiffAt_of_comp_extChartAt_symm
    {f : M → ℝ} {x : M} {k : ℕ∞ω}
    (hf : ContDiffAt ℝ k (f ∘ (extChartAt Iₘ x).symm)
      (extChartAt Iₘ x x)) :
    ContMDiffAt Iₘ 𝓘(ℝ) k f x := by
  let e := extChartAt Iₘ x
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) k
      (f ∘ e.symm) (e x) :=
    contMDiffAt_iff_contDiffAt.mpr (by simpa [e] using hf)
  have hcomp : ContMDiffAt Iₘ 𝓘(ℝ) k ((f ∘ e.symm) ∘ e) x :=
    hchart.comp x (contMDiffAt_extChartAt (I := Iₘ) (n := k) (x := x))
  have heq : f =ᶠ[nhds x] (f ∘ e.symm) ∘ e := by
    filter_upwards [(isOpen_extChartAt_source (I := Iₘ) x).mem_nhds
      (mem_extChartAt_source (I := Iₘ) x)] with y hy
    change f y = f (e.symm (e y))
    exact congrArg f (e.left_inv hy).symm
  exact hcomp.congr_of_eventuallyEq heq

/-- Joint `C¹` chart entries imply pointwise time differentiability of the
metric in every fiber direction. -/
theorem timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 1) :
    TimeDifferentiableAt gt t₀ x := by
  intro v w
  let e := extChartAt Iₘ x
  let q : E := e x
  have hU := hJoint v w
  have hpath : DifferentiableAt ℝ (fun t : ℝ ↦ (t, q)) t₀ :=
    ((hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ q)).differentiableAt
  have hdiff : DifferentiableAt ℝ
      (fun t : ℝ ↦ metricEntryJointChart gt x v w (t, q)) t₀ := by
    exact (hU.differentiableAt one_ne_zero).comp t₀ hpath
  have hqx : (extChartAt Iₘ x).symm (extChartAt Iₘ x x) = x :=
    (extChartAt Iₘ x).left_inv (mem_extChartAt_source (I := Iₘ) x)
  change DifferentiableAt ℝ
    (fun t : ℝ ↦
      (gt t).inner
        ((extChartAt Iₘ x).symm (extChartAt Iₘ x x))
        (extend E v ((extChartAt Iₘ x).symm (extChartAt Iₘ x x)))
        (extend E w ((extChartAt Iₘ x).symm (extChartAt Iₘ x x)))) t₀ at hdiff
  rw [hqx, extend_apply_self, extend_apply_self] at hdiff
  exact hdiff

/-- Joint `C²` chart entries make the time variation spatially `C¹`. -/
theorem timeVariationExtContMDiffAt_one_of_metricEntriesJointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 2) :
    TimeVariationExtContMDiffAt gt t₀ x 1 := by
  intro b c
  let e := extChartAt Iₘ x
  let q : E := e x
  let F : ℝ → E → ℝ := fun t z ↦
    metricEntryJointChart gt x b c (t, z)
  have hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, q) := by
    simpa [F, e, q, Function.uncurry] using hJoint b c
  have hB := contDiffAt_timeDeriv_one_of_joint_contDiffAt_two
    F t₀ q hF
  apply contMDiffAt_of_comp_extChartAt_symm
  simpa [F, metricEntryJointChart, e, q, timeDerivAt,
    Function.comp_def] using hB

/-- Joint `C³` chart entries make the time variation spatially `C²`, the
regularity class consumed by Hamilton scalar evolution. -/
theorem timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    TimeVariationExtContMDiffAt gt t₀ x 2 := by
  intro b c
  let e := extChartAt Iₘ x
  let q : E := e x
  let F : ℝ → E → ℝ := fun t z ↦
    metricEntryJointChart gt x b c (t, z)
  have hF : ContDiffAt ℝ 3 (Function.uncurry F) (t₀, q) := by
    simpa [F, e, q, Function.uncurry] using hJoint b c
  have hB := contDiffAt_timeDeriv_two_of_joint_contDiffAt_three
    F t₀ q hF
  apply contMDiffAt_of_comp_extChartAt_symm
  simpa [F, metricEntryJointChart, e, q, timeDerivAt,
    Function.comp_def] using hB

/-- The mixed spatial-entry derivative required by `deltaGamma_koszul`
follows from joint `C²` chart regularity. -/
theorem metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 2)
    (a b c : TM x) :
    HasDerivAt
      (fun t ↦
        extDerivFun
          (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y))
          x a)
      (extDerivFun
        (fun y : M ↦
          timeDerivAt gt t₀ y (extend E b y) (extend E c y))
        x a) t₀ := by
  let e := extChartAt Iₘ x
  let q : E := e x
  let F : ℝ → E → ℝ := fun t z ↦
    metricEntryJointChart gt x b c (t, z)
  have hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, q) := by
    simpa [F, e, q, Function.uncurry] using hJoint b c
  have hmix := hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
    F t₀ q a hF
  have hleft :
      (fun t ↦
        extDerivFun
          (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y))
          x a) =
      fun t ↦ fderiv ℝ (F t) q a := by
    funext t
    have hm := metricExtContMDiffAt_two (gt t) x b c
    simpa [F, metricEntryJointChart, e, q] using
      extDerivFun_apply_chart (hm.mdifferentiableAt two_ne_zero) a
  have hTime₁ : TimeVariationExtContMDiffAt gt t₀ x 1 :=
    timeVariationExtContMDiffAt_one_of_metricEntriesJointContDiffAt_two hJoint
  have hright := extDerivFun_apply_chart
    ((hTime₁ b c).mdifferentiableAt one_ne_zero) a
  rw [hleft]
  apply hmix.congr_deriv
  simpa [F, metricEntryJointChart, e, q, timeDerivAt,
    Function.comp_def] using hright.symm

/-- Package the old neighborhood Koszul premise from an eventual
`MetricFlowRegularAt` statement and joint `C²` metric entries. -/
theorem eventually_metricFlowRegularAt_and_mixed_of_jointContDiffAt_two
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hReg : ∀ᶠ y in nhds x, MetricFlowRegularAt gt t₀ y)
    (hJoint : ∀ᶠ y in nhds x, MetricEntriesJointContDiffAt gt t₀ y 2) :
    ∀ᶠ y in nhds x,
      MetricFlowRegularAt gt t₀ y ∧
      (∀ a b c : TM y,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun z : M ↦
                (gt t).inner z (extend E b z) (extend E c z)) y a)
          (extDerivFun
            (fun z : M ↦
              timeDerivAt gt t₀ z (extend E b z) (extend E c z))
            y a) t₀) := by
  filter_upwards [hReg, hJoint] with y hyReg hyJoint
  exact ⟨hyReg, metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
    hyJoint⟩

/-- Hamilton scalar evolution from a genuine Ricci-flow slice and one natural
joint `C³` metric-entry hypothesis.  The only remaining mixed-flow input is
`MetricFlowRegularAt`, isolated as the iterated-connection boundary. -/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hNearReg : ∀ᶠ y in nhds x, MetricFlowRegularAt gt t₀ y) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y := fun y ↦
    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint y).of_le (by norm_num))
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hNear :=
    eventually_metricFlowRegularAt_and_mixed_of_jointContDiffAt_two
      hNearReg (Filter.Eventually.of_forall fun y ↦
        (hJoint y).of_le (by norm_num))
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_no_raise_hypothesis
    hFlow hNear hgt hEntries

end Poincare
