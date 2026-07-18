import Poincare.Global.MetricFlowJointConnectionRegularity
import Poincare.Global.GeodesicTransport
import Poincare.Global.ChartCurvatureBridgeZoneClose

/-!
# Joint regularity and iterated connection values

This module develops the Euclidean mixed-partial calculation underlying the
remaining `MetricFlowRegularAt` fields.  In an anchor chart, the inner
connection on canonical extensions is a Christoffel field `Γ(t,z) u w`, and
the outer connection is

`D_z (Γ(t,z) u w) a + Γ(t,q) a (Γ(t,q) u w)`.

The theorem below differentiates this expression from ordinary joint `C²`
regularity of `Γ`.  Its derivative is precisely the coordinate form of
`∇_a δΓ(u,w) + δΓ(a, Γ(u,w))`.
-/

noncomputable section

open Bundle FiberBundle Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

section VectorValuedMixedPartial

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Finite-dimensional continuous-linear-map paths are `C^k` when their
values on every fixed input are `C^k`.  Unlike the older same-domain helper,
the path domain and operator domain may differ. -/
theorem contDiffAt_clm_path_of_apply
    {X A B : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {k : ℕ∞ω} {Φ : X → A →L[ℝ] B} {x : X}
    (h : ∀ a : A, ContDiffAt ℝ k (fun y ↦ Φ y a) x) :
    ContDiffAt ℝ k Φ x := by
  let b := Module.finBasis ℝ A
  let coordC : Fin (Module.finrank ℝ A) → A →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  have hrepr : ∀ ρ : A →L[ℝ] B,
      ρ = ∑ i, (coordC i).smulRight (ρ (b i)) := by
    intro ρ
    ext a
    have ha := b.sum_repr a
    conv_lhs => rw [← ha]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show coordC i a = b.coord i a from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun y ↦
      ∑ i, (coordC i).smulRight (Φ y (b i)) := by
    funext y
    exact hrepr (Φ y)
  rw [hfun]
  apply ContDiffAt.sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ A B (coordC i)).contDiff.contDiffAt).comp
    x (h (b i))

/-- Vector-valued joint `C²` regularity commutes one time derivative with one
spatial derivative. -/
theorem hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x a : V)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
    HasDerivAt
      (fun t ↦ fderiv ℝ (F t) x a)
      (fderiv ℝ (fun z ↦ deriv (fun t ↦ F t z) t₀) x a) t₀ := by
  let U : ℝ × V → W := Function.uncurry F
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
    have happ := congrArg (fun L : V →L[ℝ] W ↦ L a) hcomp.fderiv
    simpa [U, dx, Function.comp_def, ContinuousLinearMap.comp_apply] using
      happ.symm
  have hA : HasDerivAt
      (fun t ↦ fderiv ℝ (F t) x a)
      (fderiv ℝ (fderiv ℝ U) p dt dx) t₀ :=
    hAtotal.congr_of_eventuallyEq hspaceEq.symm
  let B : V → W := fun z ↦ deriv (fun t ↦ F t z) t₀
  let Btotal : V → W := fun z ↦ fderiv ℝ U (t₀, z) dt
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
    have happ := congrArg (fun L : ℝ →L[ℝ] W ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  have hBvalue : fderiv ℝ B x a =
      fderiv ℝ (fderiv ℝ U) p dx dt := by
    rw [hBeq.fderiv_eq, hBtotal.fderiv]
    simp [dx, dt, ContinuousLinearMap.comp_apply]
  have hsymm := hU.isSymmSndFDerivAt (by norm_num) dt dx
  apply hA.congr_deriv
  rw [hBvalue]
  exact hsymm

/-- A jointly `C³` vector-valued map has a jointly `C²` spatial Fréchet
derivative.  The derivative is taken only in the second factor. -/
theorem contDiffAt_spatial_fderiv_of_joint_contDiffAt_three_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 3 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 2 (fun p : ℝ × V ↦ fderiv ℝ (F p.1) p.2) (t₀, x) := by
  let U : ℝ × V → W := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  have hU : ContDiffAt ℝ 3 U p := by
    simpa [U, p] using hF
  have hDU : ContDiffAt ℝ 2 (fderiv ℝ U) p :=
    hU.fderiv_right (m := 2) (by norm_num)
  have hcomp : ContDiffAt ℝ 2
      (fun q : ℝ × V ↦
        (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V)) p :=
    hDU.clm_comp contDiffAt_const
  have hUnear : ∀ᶠ q in nhds p, DifferentiableAt ℝ U q :=
    (hU.eventually (by norm_num)).mono fun _ hq ↦
      hq.differentiableAt three_ne_zero
  have heq :
      (fun q : ℝ × V ↦ fderiv ℝ (F q.1) q.2) =ᶠ[nhds p]
        fun q ↦ (fderiv ℝ U q).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    filter_upwards [hUnear] with q hq
    rcases q with ⟨t, z⟩
    have hslice : HasFDerivAt (fun z' : V ↦ U (t, z'))
        ((fderiv ℝ U (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ V)) z := by
      exact hq.hasFDerivAt.comp z
        (hasFDerivAt_prodMk_right t z)
    simpa [U] using hslice.fderiv
  exact hcomp.congr_of_eventuallyEq heq

/-- A vector-valued joint `C²` map has a spatially `C¹` time partial. -/
theorem contDiffAt_timeDeriv_one_of_jointContDiffAt_two_vector
    (F : ℝ → V → W) (t₀ : ℝ) (x : V)
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (t₀, x)) :
    ContDiffAt ℝ 1 (fun z ↦ deriv (fun t ↦ F t z) t₀) x := by
  let U : ℝ × V → W := Function.uncurry F
  let p : ℝ × V := (t₀, x)
  let dt : ℝ × V := (1, 0)
  let B : V → W := fun z ↦ deriv (fun t ↦ F t z) t₀
  let Btotal : V → W := fun z ↦ fderiv ℝ U (t₀, z) dt
  have hU : ContDiffAt ℝ 2 U p := by
    simpa [U, p] using hF
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
    have happ := congrArg (fun L : ℝ →L[ℝ] W ↦ L 1) hcomp.fderiv
    simpa [B, Btotal, U, dt, Function.comp_def,
      ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv] using happ
  exact hBtotal.congr_of_eventuallyEq hBeq

end VectorValuedMixedPartial

section EuclideanIteratedConnection

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Coordinate expression for an iterated connection on two constant fields. -/
noncomputable def euclideanIteratedConnectionValue
    (Γ : ℝ → V → V →L[ℝ] V →L[ℝ] V)
    (q a u w : V) (t : ℝ) : V :=
  fderiv ℝ (fun z ↦ Γ t z u w) q a
    + Γ t q a (Γ t q u w)

/-- The three-term coordinate derivative of an iterated connection value. -/
noncomputable def euclideanIteratedConnectionTimeDerivAt
    (Γ : ℝ → V → V →L[ℝ] V →L[ℝ] V)
    (t₀ : ℝ) (q a u w : V) : V :=
  fderiv ℝ (fun z ↦ deriv (fun t ↦ Γ t z u w) t₀) q a
    + (deriv (fun t ↦ Γ t q) t₀) a (Γ t₀ q u w)
    + Γ t₀ q a ((deriv (fun t ↦ Γ t q) t₀) u w)

/-- A jointly `C²` Christoffel field differentiates the coordinate iterated
connection expression, with the exact product-rule derivative. -/
theorem hasDerivAt_euclideanIteratedConnectionValue_of_jointContDiffAt_two
    (Γ : ℝ → V → V →L[ℝ] V →L[ℝ] V)
    (t₀ : ℝ) (q a u w : V)
    (hΓ : ContDiffAt ℝ 2 (Function.uncurry Γ) (t₀, q)) :
    HasDerivAt
      (euclideanIteratedConnectionValue Γ q a u w)
      (euclideanIteratedConnectionTimeDerivAt Γ t₀ q a u w) t₀ := by
  have hΓuw : ContDiffAt ℝ 2
      (Function.uncurry (fun t z ↦ Γ t z u w)) (t₀, q) := by
    simpa [Function.uncurry] using
      (hΓ.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hSpatial :=
    hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two_vector
      (fun t z ↦ Γ t z u w) t₀ q a hΓuw
  have htimePath : DifferentiableAt ℝ (fun t : ℝ ↦ (t, q)) t₀ :=
    ((hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ q)).differentiableAt
  have hΓtimeDiff : DifferentiableAt ℝ (fun t ↦ Γ t q) t₀ :=
    by
      simpa [Function.uncurry, Function.comp_def] using
        (hΓ.differentiableAt two_ne_zero).comp t₀ htimePath
  have hΓtime : HasDerivAt (fun t ↦ Γ t q)
      (deriv (fun t ↦ Γ t q) t₀) t₀ :=
    (hasDerivAt_deriv_iff (𝕜 := ℝ)
      (f := fun t ↦ Γ t q) (x := t₀)).2 hΓtimeDiff
  have hInner : HasDerivAt (fun t ↦ Γ t q u w)
      ((deriv (fun t ↦ Γ t q) t₀) u w) t₀ := by
    simpa using
      (hΓtime.clm_apply (hasDerivAt_const t₀ u)).clm_apply
        (hasDerivAt_const t₀ w)
  have hOuter : HasDerivAt (fun t ↦ Γ t q a)
      ((deriv (fun t ↦ Γ t q) t₀) a) t₀ := by
    simpa using hΓtime.clm_apply (hasDerivAt_const t₀ a)
  have hProduct : HasDerivAt
      (fun t ↦ Γ t q a (Γ t q u w))
      ((deriv (fun t ↦ Γ t q) t₀) a (Γ t₀ q u w)
        + Γ t₀ q a ((deriv (fun t ↦ Γ t q) t₀) u w)) t₀ := by
    simpa using hOuter.clm_apply hInner
  simpa [euclideanIteratedConnectionValue,
    euclideanIteratedConnectionTimeDerivAt, add_assoc] using
      hSpatial.add hProduct

end EuclideanIteratedConnection

section AnchorChartChristoffelFlow

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "Iₘ" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace Iₘ : M → Type _)

/-- The genuine metric flow transported to one fixed anchor chart. -/
noncomputable def anchorChartMetricFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) :
    ℝ → E → E →L[ℝ] E →L[ℝ] ℝ := fun t z ↦
  CovariantDerivative.chartMetric (gt t).inner x z

/-- The cutoff-blended metric flow used by the chart Levi-Civita
construction.  It agrees with `anchorChartMetricFlow` near the anchor. -/
noncomputable def anchorBlendedMetricFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) :
    ℝ → E → E →L[ℝ] E →L[ℝ] ℝ := fun t z ↦
  CovariantDerivative.blendedChartMetric
    (GeodesicTransport.cutoff (n := n) x)
    (GeodesicTransport.backgroundMetric (n := n)) (gt t).inner x z

/-- The chart Christoffel flow, with its arguments reordered so that the
first vector is the covariant-derivative direction and the second is the
section value. -/
noncomputable def anchorChartChristoffelFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) :
    ℝ → E → E →L[ℝ] E →L[ℝ] E := fun t z ↦
  (GeodesicTransport.chartChristoffelField (gt t) x z).flip

omit [T2Space M] in
/-- On the target of the anchor chart, fixed entries of the transported
metric are exactly `metricEntryJointChart`. -/
theorem anchorChartMetricFlow_apply_eventuallyEq_metricEntryJointChart
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (b c : TM x) :
    (fun p : ℝ × E ↦ anchorChartMetricFlow gt x p.1 p.2 b c)
      =ᶠ[nhds (t₀, extChartAt Iₘ x x)]
    metricEntryJointChart gt x b c := by
  have htarget : ∀ᶠ p : ℝ × E in nhds (t₀, extChartAt Iₘ x x),
      p.2 ∈ (extChartAt Iₘ x).target :=
    continuousAt_snd.eventually
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  filter_upwards [htarget] with p hp
  let y : M := (extChartAt Iₘ x).symm p.2
  have hy : y ∈ (extChartAt Iₘ x).source :=
    (extChartAt Iₘ x).map_target hp
  have hz : extChartAt Iₘ x y = p.2 :=
    (extChartAt Iₘ x).right_inv hp
  let B : ∀ y : M, TM y := FiberBundle.extend E b
  let C : ∀ y : M, TM y := FiberBundle.extend E c
  have hbRound :=
    CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
      (I := Iₘ) x hy (B y)
  have hbPush :
      mfderiv Iₘ 𝓘(ℝ, E) (extChartAt Iₘ x) y (B y) = b := by
    simpa [B] using mfderiv_extChartAt_extend_apply
      (n := n) (M := M) (x := x) (y := y) hy b
  rw [hbPush, hz] at hbRound
  have hcRound :=
    CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
      (I := Iₘ) x hy (C y)
  have hcPush :
      mfderiv Iₘ 𝓘(ℝ, E) (extChartAt Iₘ x) y (C y) = c := by
    simpa [C] using mfderiv_extChartAt_extend_apply
      (n := n) (M := M) (x := x) (y := y) hy c
  rw [hcPush, hz] at hcRound
  change CovariantDerivative.chartMetric (gt p.1).inner x p.2 b c =
    (gt p.1).inner y (B y) (C y)
  rw [CovariantDerivative.chartMetric_apply, hbRound, hcRound]

/-- Joint regularity of all canonical metric entries is joint regularity of
the actual continuous-bilinear transported chart metric. -/
theorem anchorChartMetricFlow_jointContDiffAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    {k : ℕ∞ω} (hJoint : MetricEntriesJointContDiffAt gt t₀ x k) :
    ContDiffAt ℝ k (Function.uncurry (anchorChartMetricFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  apply contDiffAt_clm_path_of_apply
  intro b
  apply contDiffAt_clm_path_of_apply
  intro c
  exact (hJoint b c).congr_of_eventuallyEq
    (anchorChartMetricFlow_apply_eventuallyEq_metricEntryJointChart
      gt t₀ x b c)

omit [T2Space M] in
/-- The blended and genuine transported metric flows agree jointly near the
anchor because the cutoff is identically one there. -/
theorem anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    Function.uncurry (anchorBlendedMetricFlow gt x)
      =ᶠ[nhds (t₀, extChartAt Iₘ x x)]
    Function.uncurry (anchorChartMetricFlow gt x) := by
  have hone : ∀ᶠ p : ℝ × E in nhds (t₀, extChartAt Iₘ x x),
      GeodesicTransport.cutoff (n := n) x p.2 = 1 := by
    have hsnd : ContinuousAt (fun p : ℝ × E ↦ p.2)
        (t₀, extChartAt Iₘ x x) := continuousAt_snd
    exact hsnd.eventually
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  filter_upwards [hone] with p hp
  exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    (GeodesicTransport.cutoff (n := n) x)
    (GeodesicTransport.backgroundMetric (n := n)) (gt p.1).inner x hp

/-- Global joint `C³` metric entries make the cutoff-blended chart metric
jointly `C³` at the anchor. -/
theorem anchorBlendedMetricFlow_jointContDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 3 (Function.uncurry (anchorBlendedMetricFlow gt x))
      (t₀, extChartAt Iₘ x x) :=
  (anchorChartMetricFlow_jointContDiffAt_of_metricEntries hJoint)
    |>.congr_of_eventuallyEq
      (anchorBlendedMetricFlow_eventuallyEq_anchorChartMetricFlow gt t₀ x)

/-- The continuous Koszul covector of a parameterized Euclidean metric,
taking spatial derivatives only. -/
noncomputable def jointChristoffelCovectorAt
    (G : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (t : ℝ) (z u v : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    (((fderiv ℝ (G t) z) u) v
      + ((fderiv ℝ (G t) z) v) u
      - ((fderiv ℝ (G t) z).flip u).flip v)

/-- Joint `C³` regularity of a metric family makes its spatial Koszul
covector jointly `C²`. -/
theorem jointChristoffelCovectorAt_contDiffAt_two
    (G : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (t₀ : ℝ) (z u v : E)
    (hG : ContDiffAt ℝ 3 (Function.uncurry G) (t₀, z)) :
    ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ jointChristoffelCovectorAt G p.1 p.2 u v)
      (t₀, z) := by
  have hD := contDiffAt_spatial_fderiv_of_joint_contDiffAt_three_vector
    G t₀ z hG
  apply contDiffAt_clm_path_of_apply
  intro w
  have hu : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ u) (t₀, z) :=
    contDiffAt_const
  have hv : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ v) (t₀, z) :=
    contDiffAt_const
  have hw : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ w) (t₀, z) :=
    contDiffAt_const
  have h₁ := ((hD.clm_apply hu).clm_apply hv).clm_apply hw
  have h₂ := ((hD.clm_apply hv).clm_apply hu).clm_apply hw
  have h₃ := ((hD.clm_apply hw).clm_apply hu).clm_apply hv
  simpa [jointChristoffelCovectorAt, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply] using
      ((h₁.add h₂).sub h₃).const_smul (1 / 2 : ℝ)

omit [T2Space M] in
/-- Every blended metric operator is invertible, by the nondegenerate chart
bilinear form used in the transported Levi-Civita construction. -/
theorem anchorBlendedMetricFlow_isInvertible
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) :
    (anchorBlendedMetricFlow gt x t z).IsInvertible := by
  exact CovariantDerivative.metric_isInvertible
    (anchorBlendedMetricFlow gt x t)
    (CovariantDerivative.chartBilin
      (GeodesicTransport.cutoff (n := n) x)
      (GeodesicTransport.backgroundMetric (n := n)) (gt t).inner x z)
    (CovariantDerivative.chartBilin_nondegenerate
      (GeodesicTransport.cutoff (n := n) x)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_pos (n := n)) (gt t).inner
      (fun y a ha ↦ (gt t).inner_pos y (v := a) ha) x
      (GeodesicTransport.cutoff_nonneg (n := n) x)
      (GeodesicTransport.cutoff_le_one (n := n) x)
      (GeodesicTransport.cutoff_support_invertible (n := n) x) z)
    (by intro a b; rfl)

omit [T2Space M] in
/-- The chart Christoffel flow is the inverse blended metric applied to the
spatial Koszul covector. -/
theorem anchorChartChristoffelFlow_apply_eq_inverse_koszul
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z u v : E) :
    anchorChartChristoffelFlow gt x t z u v =
      (anchorBlendedMetricFlow gt x t z).inverse
        (jointChristoffelCovectorAt
          (anchorBlendedMetricFlow gt x) t z u v) := by
  let G := anchorBlendedMetricFlow gt x t
  let b := CovariantDerivative.chartBilin
    (GeodesicTransport.cutoff (n := n) x)
    (GeodesicTransport.backgroundMetric (n := n)) (gt t).inner x z
  let hb := CovariantDerivative.chartBilin_nondegenerate
    (GeodesicTransport.cutoff (n := n) x)
    (GeodesicTransport.backgroundMetric (n := n))
    (GeodesicTransport.backgroundMetric_pos (n := n)) (gt t).inner
    (fun y a ha ↦ (gt t).inner_pos y (v := a) ha) x
    (GeodesicTransport.cutoff_nonneg (n := n) x)
    (GeodesicTransport.cutoff_le_one (n := n) x)
    (GeodesicTransport.cutoff_support_invertible (n := n) x) z
  have hK : LinearMap.toContinuousLinearMap
      (CovariantDerivative.christoffelFunctional G z u v) =
        jointChristoffelCovectorAt (anchorBlendedMetricFlow gt x) t z u v := by
    ext w
    simp [jointChristoffelCovectorAt, G,
      CovariantDerivative.christoffelFunctional,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      smul_eq_mul]
  change CovariantDerivative.christoffelAt G z b hb u v = _
  rw [CovariantDerivative.christoffelAt_eq_inverse G b hb
    (by intro a c; rfl) u v, hK]

/-- Global joint `C³` metric entries make the actual anchor-chart
Christoffel flow jointly `C²`. -/
theorem anchorChartChristoffelFlow_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 2 (Function.uncurry (anchorChartChristoffelFlow gt x))
      (t₀, extChartAt Iₘ x x) := by
  let q : E := extChartAt Iₘ x x
  have hG : ContDiffAt ℝ 3
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    anchorBlendedMetricFlow_jointContDiffAt_three_of_metricEntries hJoint
  have hG₂ : ContDiffAt ℝ 2
      (Function.uncurry (anchorBlendedMetricFlow gt x)) (t₀, q) :=
    hG.of_le (by norm_num)
  have hInv : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, q) := by
    exact ((anchorBlendedMetricFlow_isInvertible gt x t₀ q)
      |>.contDiffAt_map_inverse).comp (t₀, q) hG₂
  apply contDiffAt_clm_path_of_apply
  intro u
  apply contDiffAt_clm_path_of_apply
  intro v
  have hK : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ jointChristoffelCovectorAt
        (anchorBlendedMetricFlow gt x) p.1 p.2 u v) (t₀, q) :=
    jointChristoffelCovectorAt_contDiffAt_two
      (anchorBlendedMetricFlow gt x) t₀ q u v hG
  have heq :
      (fun p : ℝ × E ↦ anchorChartChristoffelFlow gt x p.1 p.2 u v) =
        fun p ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse
          (jointChristoffelCovectorAt
            (anchorBlendedMetricFlow gt x) p.1 p.2 u v) := by
    funext p
    exact anchorChartChristoffelFlow_apply_eq_inverse_koszul
      gt x p.1 p.2 u v
  change ContDiffAt ℝ 2
    (fun p : ℝ × E ↦ anchorChartChristoffelFlow gt x p.1 p.2 u v)
    (t₀, q)
  rw [heq]
  exact hInv.clm_apply hK

/-! ## Identification with intrinsic iterated connection values -/

/-- The time derivative of a Levi-Civita connection on any fixed
differentiable field depends only on the field value.  This extends the
canonical-extension definition of `deltaGammaAt` by tensoriality of the
difference of two connections. -/
theorem hasDerivAt_leviCivita_fixed_field
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hΓ : ConnectionValueTimeDifferentiableAt gt t₀ x)
    {Y : ∀ y : M, TM y} (hY : MDiffAtTangentField Y x) (v : TM x) :
    HasDerivAt (fun t ↦ (gt t).leviCivita Y x v)
      (deltaGammaAt gt t₀ x v (Y x)) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  let Y₀ : ∀ y : M, TM y := extend E (Y x)
  let c : TM x :=
    (gt t₀).leviCivita Y x v - (gt t₀).leviCivita Y₀ x v
  have hY₀ : MDiffAtTangentField Y₀ x := by
    simpa [Y₀, MDiffAtTangentField] using
      (mdifferentiableAt_extend Iₘ E (Y x))
  have hpath :
      (fun t ↦ (gt t).leviCivita Y x v) =
        fun t ↦ (gt t).leviCivita Y₀ x v + c := by
    funext t
    have hYdiff :
        ((gt t).leviCivita.difference (gt t₀).leviCivita) x (Y x) v =
          (gt t).leviCivita Y x v - (gt t₀).leviCivita Y x v := by
      simpa [CovariantDerivative.difference] using congrArg
        (fun L : TM x →L[ℝ] TM x ↦ L v)
        (IsCovariantDerivativeOn.difference_apply
          ((gt t).leviCivita.isCovariantDerivativeOn (s := Set.univ))
          ((gt t₀).leviCivita.isCovariantDerivativeOn (s := Set.univ))
          (x := x) (σ := Y) (by trivial)
          (by simpa [MDiffAtTangentField] using hY))
    have hY₀diff :
        ((gt t).leviCivita.difference (gt t₀).leviCivita) x (Y₀ x) v =
          (gt t).leviCivita Y₀ x v - (gt t₀).leviCivita Y₀ x v := by
      simpa [CovariantDerivative.difference] using congrArg
        (fun L : TM x →L[ℝ] TM x ↦ L v)
        (IsCovariantDerivativeOn.difference_apply
          ((gt t).leviCivita.isCovariantDerivativeOn (s := Set.univ))
          ((gt t₀).leviCivita.isCovariantDerivativeOn (s := Set.univ))
          (x := x) (σ := Y₀) (by trivial)
          (by simpa [MDiffAtTangentField] using hY₀))
    have hY₀x : Y₀ x = Y x := by simp [Y₀]
    have heq :
        (gt t).leviCivita Y x v - (gt t₀).leviCivita Y x v =
          (gt t).leviCivita Y₀ x v - (gt t₀).leviCivita Y₀ x v := by
      rw [← hYdiff, ← hY₀diff, hY₀x]
    dsimp [c]
    calc
      (gt t).leviCivita Y x v =
          ((gt t).leviCivita Y x v - (gt t₀).leviCivita Y x v)
            + (gt t₀).leviCivita Y x v := by abel
      _ = ((gt t).leviCivita Y₀ x v - (gt t₀).leviCivita Y₀ x v)
            + (gt t₀).leviCivita Y x v := by rw [heq]
      _ = (gt t).leviCivita Y₀ x v
            + ((gt t₀).leviCivita Y x v
              - (gt t₀).leviCivita Y₀ x v) := by abel
  rw [hpath]
  simpa [Y₀, deltaGammaAt] using
    (hΓ v (Y x)).hasDerivAt.add_const c

/-- A canonical extension based at `x` remains differentiable at all points
whose anchor-chart coordinates are sufficiently close to the anchor. -/
theorem eventually_mdiffAt_extend_in_anchorChart
    (x : M) (w : TM x) :
    ∀ᶠ z in nhds (extChartAt Iₘ x x),
      MDiffAtTangentField (extend E w) ((extChartAt Iₘ x).symm z) := by
  have hnear : ∀ᶠ y in nhds x,
      MDiffAtTangentField (extend E w) y :=
    (eventually_contMDiffAt_two_canonical_extend (n := n) (M := M) w).mono
      fun _ hy ↦ by
        simpa [MDiffAtTangentField] using hy.mdifferentiableAt two_ne_zero
  have hleft :
      (extChartAt Iₘ x).symm (extChartAt Iₘ x x) = x :=
    (extChartAt Iₘ x).left_inv (mem_extChartAt_source x)
  have hnear' : ∀ᶠ y in
      nhds ((extChartAt Iₘ x).symm (extChartAt Iₘ x x)),
      MDiffAtTangentField (extend E w) y := by
    simpa [hleft] using hnear
  exact (continuousAt_extChartAt_symm x).eventually hnear'

/-- On one fixed cutoff-one chart germ, the transported inner closed
connection path is exactly the direction-first Christoffel path.  The germ
is uniform in time because the cutoff and chart are fixed. -/
theorem chartTransported_innerConnectionPath_eventuallyEq_anchorChristoffel
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) :
    (fun z : E ↦ fun t : ℝ ↦
      CovariantDerivative.chartTransportedLeviCivitaSection x
        (fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y)) z)
      =ᶠ[nhds (extChartAt Iₘ x x)]
    (fun z : E ↦ fun t : ℝ ↦
      anchorChartChristoffelFlow gt x t z u w) := by
  let q : E := extChartAt Iₘ x x
  have htarget : ∀ᶠ z in nhds q, z ∈ (extChartAt Iₘ x).target :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hcut : ∀ᶠ z in nhds q,
      ∀ᶠ z' in nhds z,
        GeodesicTransport.cutoff (n := n) x z' = 1 :=
    eventually_eventually_nhds.2
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hWdiff := eventually_mdiffAt_extend_in_anchorChart
    (n := n) (M := M) x w
  filter_upwards [htarget, hcut, hWdiff] with z hz hcz hWz
  let y : M := (extChartAt Iₘ x).symm z
  have hy : y ∈ (extChartAt Iₘ x).source :=
    (extChartAt Iₘ x).map_target hz
  have hzy : extChartAt Iₘ x y = z :=
    (extChartAt Iₘ x).right_inv hz
  let W : ∀ y : M, TM y := extend E w
  let U : ∀ y : M, TM y := extend E u
  have hW : MDiffAtTangentField W y := by simpa [W, y] using hWz
  have hWconst :
      CovariantDerivative.chartTransportedLeviCivitaSection x W
        =ᶠ[nhds z] fun _ : E ↦ w := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with z' hz'
    let y' : M := (extChartAt Iₘ x).symm z'
    have hy' : y' ∈ (extChartAt Iₘ x).source :=
      (extChartAt Iₘ x).map_target hz'
    have hz' : extChartAt Iₘ x y' = z' :=
      (extChartAt Iₘ x).right_inv hz'
    have hw' := chartTransportedLeviCivitaSection_extend_apply_chart
      (n := n) (M := M) (x := x) (y := y') hy' w
    rw [hz'] at hw'
    simpa [W] using hw'
  have hUc :
      CovariantDerivative.chartTransportedLeviCivitaSection x U z = u := by
    have hu' := chartTransportedLeviCivitaSection_extend_apply_chart
      (n := n) (M := M) (x := x) (y := y) hy u
    rw [hzy] at hu'
    simpa [U] using hu'
  funext t
  have hcz' : ∀ᶠ z' in nhds (extChartAt Iₘ x y),
      GeodesicTransport.cutoff (n := n) x z' = 1 := by
    rw [hzy]
    exact hcz
  have hnat :=
    ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
        (g := gt t) (x₀ := x) (y := y) hy hcz' W U hW
  rw [hzy, hUc] at hnat
  have hformula :
      (GeodesicTransport.chartLeviCivita (gt t) x)
          (CovariantDerivative.chartTransportedLeviCivitaSection x W) z u =
        fderiv ℝ
            (CovariantDerivative.chartTransportedLeviCivitaSection x W) z u
          + anchorChartChristoffelFlow gt x t z u
              (CovariantDerivative.chartTransportedLeviCivitaSection x W z) := by
    rfl
  rw [hformula, hWconst.fderiv_eq, hWconst.self_of_nhds] at hnat
  simpa [W, U] using hnat

/-- Differentiability of an anchor-chart representative pulls back to
differentiability of the intrinsic tangent field. -/
theorem mdiffAt_tangentField_of_chartTransported_eventuallyEq
    (x : M) (S : ∀ y : M, TM y) (V : E → E)
    (hV : DifferentiableAt ℝ V (extChartAt Iₘ x x))
    (hEq : CovariantDerivative.chartTransportedLeviCivitaSection x S
      =ᶠ[nhds (extChartAt Iₘ x x)] V) :
    MDiffAtTangentField S x := by
  let f : M → E := (extChartAt Iₘ x : PartialEquiv M E)
  let Vt : ∀ z : E, TangentSpace 𝓘(ℝ, E) z := fun z ↦ V z
  let W : ∀ y : M, TM y :=
    VectorField.mpullback Iₘ 𝓘(ℝ, E) f Vt
  have hVmdiff : MDifferentiableAt 𝓘(ℝ, E)
      ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (T% Vt) (extChartAt Iₘ x x) :=
    mdiffAt_vectorSpace_iff_differentiableAt.mpr (by
      simpa [Vt] using hV)
  have hf : ContMDiffAt Iₘ 𝓘(ℝ, E) 2 f x := by
    simpa [f] using
      (contMDiffAt_extChartAt : ContMDiffAt Iₘ 𝓘(ℝ, E) 2
        ((extChartAt Iₘ x : PartialEquiv M E) : M → E) x)
  have hfinv : (mfderiv Iₘ 𝓘(ℝ, E) f x).IsInvertible := by
    simpa [f] using
      (isInvertible_mfderiv_extChartAt (I := Iₘ)
        (x := x) (y := x) (mem_extChartAt_source x))
  have hW : MDiffAtTangentField W x := by
    simpa [W, MDiffAtTangentField] using
      hVmdiff.mpullback_vectorField (f := f) hf hfinv (by norm_num)
  have hbase :
      S =ᶠ[nhds x]
        VectorField.mpullback Iₘ 𝓘(ℝ, E) f
          (CovariantDerivative.chartTransportedLeviCivitaSection x S) := by
    simpa [f, CovariantDerivative.chartTransportedLeviCivitaSection,
      nhdsWithin_univ] using
      (VectorField.eventuallyEq_mpullback_mpullbackWithin_extChartAt
        (I := Iₘ) (s := Set.univ) (x := x) S)
  have hsource : ∀ᶠ y in nhds x, y ∈ (extChartAt Iₘ x).source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  have hEqpre : ∀ᶠ y in nhds x,
      CovariantDerivative.chartTransportedLeviCivitaSection x S
          (extChartAt Iₘ x y) = V (extChartAt Iₘ x y) :=
    (continuousAt_extChartAt x).eventually hEq
  have hpull :
      VectorField.mpullback Iₘ 𝓘(ℝ, E) f
          (CovariantDerivative.chartTransportedLeviCivitaSection x S)
        =ᶠ[nhds x] W := by
    filter_upwards [hsource, hEqpre] with y _hy heq
    simp only [W, Vt, VectorField.mpullback_apply]
    exact congrArg (mfderiv Iₘ 𝓘(ℝ, E) f y).inverse heq
  refine hW.congr_of_eventuallyEq ?_
  filter_upwards [hbase.trans hpull] with y hy
  rw [hy]

/-- The transported `deltaGammaFieldAt` is the time derivative of the
anchor Christoffel field on the anchor germ. -/
theorem chartTransported_deltaGammaField_eventuallyEq_anchorTimeDeriv
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y)
    (u w : TM x) :
    CovariantDerivative.chartTransportedLeviCivitaSection x
        (deltaGammaFieldAt gt t₀ u w)
      =ᶠ[nhds (extChartAt Iₘ x x)]
    (fun z : E ↦
      deriv (fun t ↦ anchorChartChristoffelFlow gt x t z u w) t₀) := by
  let q : E := extChartAt Iₘ x x
  have hpaths :=
    chartTransported_innerConnectionPath_eventuallyEq_anchorChristoffel
      gt x u w
  have htarget : ∀ᶠ z in nhds q, z ∈ (extChartAt Iₘ x).target :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hWdiff := eventually_mdiffAt_extend_in_anchorChart
    (n := n) (M := M) x w
  filter_upwards [hpaths, htarget, hWdiff] with z hzpath hz hWz
  let y : M := (extChartAt Iₘ x).symm z
  letI : NormedAddCommGroup (TM y) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM y) := inferInstanceAs (NormedSpace ℝ E)
  let W : ∀ y : M, TM y := extend E w
  let U : ∀ y : M, TM y := extend E u
  have hW : MDiffAtTangentField W y := by simpa [W, y] using hWz
  have hfield := hasDerivAt_leviCivita_fixed_field
    (hConn y) hW (U y)
  let D : TM y →L[ℝ] E :=
    (mfderivWithin 𝓘(ℝ, E) Iₘ (extChartAt Iₘ x).symm
      (Set.range Iₘ) z).inverse
  have htransport : HasDerivAt
      (fun t ↦ D ((gt t).leviCivita W y (U y)))
      (D (deltaGammaAt gt t₀ y (U y) (W y))) t₀ := by
    simpa using
      (D.hasFDerivAt.comp t₀ hfield.hasFDerivAt).hasDerivAt
  have htransport' : HasDerivAt
      (fun t ↦ CovariantDerivative.chartTransportedLeviCivitaSection x
        (fun y : M ↦ (gt t).leviCivita (extend E w) y (extend E u y)) z)
      (CovariantDerivative.chartTransportedLeviCivitaSection x
        (deltaGammaFieldAt gt t₀ u w) z) t₀ := by
    simpa [D, y, W, U, deltaGammaFieldAt,
      CovariantDerivative.chartTransportedLeviCivitaSection_apply] using
      htransport
  rw [hzpath] at htransport'
  exact htransport'.deriv.symm

/-- Joint `C³` metric entries make the vector-valued `deltaGammaFieldAt`
intrinsically differentiable. -/
theorem deltaGammaFieldMDifferentiableAt_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y) :
    DeltaGammaFieldMDifferentiableAt gt t₀ x := by
  intro u w
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  let q : E := extChartAt Iₘ x x
  let Γ := anchorChartChristoffelFlow gt x
  have hΓ : ContDiffAt ℝ 2 (Function.uncurry Γ) (t₀, q) := by
    simpa [Γ, q] using
      anchorChartChristoffelFlow_jointContDiffAt_two_of_metricEntries hJoint
  have hΓuw : ContDiffAt ℝ 2
      (Function.uncurry (fun t z ↦ Γ t z u w)) (t₀, q) := by
    have hu : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ u) (t₀, q) :=
      contDiffAt_const
    have hw : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ w) (t₀, q) :=
      contDiffAt_const
    simpa [Function.uncurry] using (hΓ.clm_apply hu).clm_apply hw
  have htime : ContDiffAt ℝ 1
      (fun z ↦ deriv (fun t ↦ Γ t z u w) t₀) q :=
    contDiffAt_timeDeriv_one_of_jointContDiffAt_two_vector
      (fun t z ↦ Γ t z u w) t₀ q hΓuw
  apply mdiffAt_tangentField_of_chartTransported_eventuallyEq
    (x := x) (V := fun z ↦ deriv (fun t ↦ Γ t z u w) t₀)
  · exact htime.differentiableAt one_ne_zero
  · simpa [Γ, q] using
      chartTransported_deltaGammaField_eventuallyEq_anchorTimeDeriv
        hConn u w

/-- At the anchor, the intrinsic closed Levi-Civita derivative is exactly the
model Levi-Civita derivative of the transported section. -/
theorem leviCivita_eq_anchorChartLeviCivita
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (S : ∀ y : M, TM y) (hS : MDiffAtTangentField S x) (a : TM x) :
    g.leviCivita S x a =
      (GeodesicTransport.chartLeviCivita g x)
        (CovariantDerivative.chartTransportedLeviCivitaSection x S)
        (extChartAt Iₘ x x) a := by
  let A : ∀ y : M, TM y := extend E a
  have hnat :=
    ChartCurvatureBridge6.chartTransportedLeviCivitaSection_closed_hom_apply_anchor
        (g := g) (x₀ := x) (σ := S) (X := A) hS
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x
          (fun y : M ↦ g.leviCivita S y (A y))
          (extChartAt Iₘ x x) =
        g.leviCivita S x a := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := Iₘ) (x₀ := x)
        (σ := fun y : M ↦ g.leviCivita S y (A y))
        (y := x) (mem_extChartAt_source x)
    rw [mfderiv_extChartAt_self] at happly
    simpa [A, extend_apply_self] using happly
  have hA :
      CovariantDerivative.chartTransportedLeviCivitaSection x A
          (extChartAt Iₘ x x) = a := by
    simpa [A] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x) (y := x)
        (mem_extChartAt_source x) a)
  rw [hleft, hA] at hnat
  exact hnat

/-- The intrinsic connection value on canonical extensions is the anchor
Christoffel field. -/
theorem connectionValue_eq_anchorChartChristoffelFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (u w : TM x) :
    (gt t).leviCivita (extend E w) x u =
      anchorChartChristoffelFlow gt x t (extChartAt Iₘ x x) u w := by
  have h := congrFun
    ((chartTransported_innerConnectionPath_eventuallyEq_anchorChristoffel
      gt x u w).self_of_nhds) t
  change
    CovariantDerivative.chartTransportedLeviCivitaSection x
        (fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y))
        (extChartAt Iₘ x x) =
      anchorChartChristoffelFlow gt x t (extChartAt Iₘ x x) u w at h
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x
          (fun y : M ↦
            (gt t).leviCivita (extend E w) y (extend E u y))
          (extChartAt Iₘ x x) =
        (gt t).leviCivita (extend E w) x u := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := Iₘ) (x₀ := x)
        (σ := fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y))
        (y := x) (mem_extChartAt_source x)
    rw [mfderiv_extChartAt_self] at happly
    simpa [extend_apply_self] using happly
  rw [hleft] at h
  exact h

/-- The intrinsic connection variation is the time derivative of the anchor
Christoffel field. -/
theorem deltaGammaAt_eq_anchorChartChristoffelTimeDeriv
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y)
    (u w : TM x) :
    deltaGammaAt gt t₀ x u w =
      deriv (fun t ↦
        anchorChartChristoffelFlow gt x t (extChartAt Iₘ x x) u w) t₀ := by
  have h :=
    (chartTransported_deltaGammaField_eventuallyEq_anchorTimeDeriv
      hConn u w).self_of_nhds
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x
          (deltaGammaFieldAt gt t₀ u w) (extChartAt Iₘ x x) =
        deltaGammaAt gt t₀ x u w := by
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := Iₘ) (x₀ := x)
        (σ := deltaGammaFieldAt gt t₀ u w)
        (y := x) (mem_extChartAt_source x)
    rw [mfderiv_extChartAt_self] at happly
    simpa [deltaGammaFieldAt, extend_apply_self] using happly
  rw [hleft] at h
  exact h

/-- The actual iterated closed connection value is the Euclidean Christoffel
formula in the fixed anchor chart. -/
theorem iteratedConnectionValue_eq_euclidean
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (a u w : TM x) :
    (gt t).leviCivita
        (fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y)) x a =
      euclideanIteratedConnectionValue
        (anchorChartChristoffelFlow gt x)
        (extChartAt Iₘ x x) a u w t := by
  let q : E := extChartAt Iₘ x x
  let W : ∀ y : M, TM y := fun y ↦
    (gt t).leviCivita (extend E w) y (extend E u y)
  let Wc : E → E :=
    CovariantDerivative.chartTransportedLeviCivitaSection x W
  let Γ := anchorChartChristoffelFlow gt x
  have hW : MDiffAtTangentField W x := by
    simpa [W, MDiffAtTangentField] using
      (leviCivita_extend_connection_field_mdiffAt
        (g := gt t) (x := x) w u)
  have hbase := leviCivita_eq_anchorChartLeviCivita
    (g := gt t) x W hW a
  have hsec : Wc =ᶠ[nhds q] fun z : E ↦ Γ t z u w := by
    have hpaths :=
      chartTransported_innerConnectionPath_eventuallyEq_anchorChristoffel
        gt x u w
    filter_upwards [hpaths] with z hz
    exact congrFun hz t
  have hformula :
      (GeodesicTransport.chartLeviCivita (gt t) x) Wc q a =
        fderiv ℝ Wc q a + Γ t q a (Wc q) := by
    rfl
  rw [hformula, hsec.fderiv_eq, hsec.self_of_nhds] at hbase
  simpa [W, Wc, Γ, q, euclideanIteratedConnectionValue] using hbase

/-- The coordinate derivative of the Euclidean iterated-connection formula
is precisely the intrinsic `iteratedConnectionDerivAt`. -/
theorem euclideanIteratedConnectionTimeDerivAt_eq_iteratedConnectionDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y)
    (a u w : TM x) :
    euclideanIteratedConnectionTimeDerivAt
        (anchorChartChristoffelFlow gt x) t₀
        (extChartAt Iₘ x x) a u w =
      iteratedConnectionDerivAt gt t₀ x a u w := by
  let q : E := extChartAt Iₘ x x
  let Γ := anchorChartChristoffelFlow gt x
  let S : ∀ y : M, TM y := deltaGammaFieldAt gt t₀ u w
  let Sc : E → E :=
    CovariantDerivative.chartTransportedLeviCivitaSection x S
  let V : E → E := fun z ↦ deriv (fun t ↦ Γ t z u w) t₀
  have hΓ : ContDiffAt ℝ 2 (Function.uncurry Γ) (t₀, q) := by
    simpa [Γ, q] using
      anchorChartChristoffelFlow_jointContDiffAt_two_of_metricEntries hJoint
  have htimePath : DifferentiableAt ℝ (fun t : ℝ ↦ (t, q)) t₀ :=
    ((hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ q)).differentiableAt
  have hΓtimeDiff : DifferentiableAt ℝ (fun t ↦ Γ t q) t₀ := by
    simpa [Function.uncurry, Function.comp_def] using
      (hΓ.differentiableAt two_ne_zero).comp t₀ htimePath
  have hΓtime : HasDerivAt (fun t ↦ Γ t q)
      (deriv (fun t ↦ Γ t q) t₀) t₀ :=
    (hasDerivAt_deriv_iff (f := fun t ↦ Γ t q) (x := t₀)).2 hΓtimeDiff
  have heval : ∀ v r : E,
      deriv (fun t ↦ Γ t q v r) t₀ =
        (deriv (fun t ↦ Γ t q) t₀) v r := by
    intro v r
    simpa using
      ((hΓtime.clm_apply (hasDerivAt_const t₀ v)).clm_apply
        (hasDerivAt_const t₀ r)).deriv
  have hS : MDiffAtTangentField S x := by
    simpa [S, DeltaGammaFieldMDifferentiableAt, MDiffAtTangentField] using
      (deltaGammaFieldMDifferentiableAt_of_metricEntriesJointContDiffAt_three
        hJoint hConn u w)
  have hsec : Sc =ᶠ[nhds q] V := by
    simpa [Sc, S, V, Γ, q] using
      (chartTransported_deltaGammaField_eventuallyEq_anchorTimeDeriv
        hConn u w)
  have hbase := leviCivita_eq_anchorChartLeviCivita
    (g := gt t₀) x S hS a
  have hformula :
      (GeodesicTransport.chartLeviCivita (gt t₀) x) Sc q a =
        fderiv ℝ Sc q a + Γ t₀ q a (Sc q) := by
    rfl
  rw [hformula, hsec.fderiv_eq, hsec.self_of_nhds] at hbase
  have hVq : V q = (deriv (fun t ↦ Γ t q) t₀) u w := by
    simpa [V] using heval u w
  rw [hVq] at hbase
  have hfirst :
      (gt t₀).leviCivita (deltaGammaFieldAt gt t₀ u w) x a =
        fderiv ℝ V q a
          + Γ t₀ q a ((deriv (fun t ↦ Γ t q) t₀) u w) := by
    simpa [S, Sc] using hbase
  let b : TM x := (gt t₀).leviCivita (extend E w) x u
  have hb : b = Γ t₀ q u w := by
    simpa [b, Γ, q] using
      connectionValue_eq_anchorChartChristoffelFlow gt x t₀ u w
  have hsecond :
      deltaGammaAt gt t₀ x a b =
        (deriv (fun t ↦ Γ t q) t₀) a (Γ t₀ q u w) := by
    calc
      deltaGammaAt gt t₀ x a b =
          deriv (fun t ↦ Γ t q a b) t₀ := by
            simpa [b, Γ, q] using
              deltaGammaAt_eq_anchorChartChristoffelTimeDeriv
                hConn a b
      _ = (deriv (fun t ↦ Γ t q) t₀) a b := heval a b
      _ = (deriv (fun t ↦ Γ t q) t₀) a (Γ t₀ q u w) := by
        rw [hb]
  rw [iteratedConnectionDerivAt]
  change
    fderiv ℝ V q a
        + (deriv (fun t ↦ Γ t q) t₀) a (Γ t₀ q u w)
        + Γ t₀ q a ((deriv (fun t ↦ Γ t q) t₀) u w) =
      (gt t₀).leviCivita (deltaGammaFieldAt gt t₀ u w) x a
        + deltaGammaAt gt t₀ x a b
  rw [hfirst, hsecond]
  abel

/-- Joint `C³` metric entries differentiate every actual iterated connection
path with the derivative prescribed by `MetricFlowRegularAt`. -/
theorem hasDerivAt_iteratedConnectionValue_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y)
    (a u w : TM x) :
    HasDerivAt
      (fun t ↦ (gt t).leviCivita
        (fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y)) x a)
      (iteratedConnectionDerivAt gt t₀ x a u w) t₀ := by
  let q : E := extChartAt Iₘ x x
  let Γ := anchorChartChristoffelFlow gt x
  have hΓ : ContDiffAt ℝ 2 (Function.uncurry Γ) (t₀, q) := by
    simpa [Γ, q] using
      anchorChartChristoffelFlow_jointContDiffAt_two_of_metricEntries hJoint
  have hcoord :=
    hasDerivAt_euclideanIteratedConnectionValue_of_jointContDiffAt_two
      Γ t₀ q a u w hΓ
  have hpath :
      (fun t ↦ (gt t).leviCivita
        (fun y : M ↦
          (gt t).leviCivita (extend E w) y (extend E u y)) x a) =
        euclideanIteratedConnectionValue Γ q a u w := by
    funext t
    simpa [Γ, q] using
      iteratedConnectionValue_eq_euclidean gt x t a u w
  rw [hpath]
  exact hcoord.congr_deriv
    (euclideanIteratedConnectionTimeDerivAt_eq_iteratedConnectionDerivAt
      hJoint hConn a u w)

/-- Global joint `C³` metric-entry regularity discharges the complete
`MetricFlowRegularAt` boundary. -/
theorem metricFlowRegularAt_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    MetricFlowRegularAt gt t₀ x := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have hConn : ∀ y : M, ConnectionValueTimeDifferentiableAt gt t₀ y :=
    connectionValueTimeDifferentiableAt_all_of_jointContDiffAt_two
      (fun y ↦ (hJoint y).of_le (by norm_num))
  refine ⟨hConn, ?_, ?_⟩
  · intro a u w
    exact (hasDerivAt_iteratedConnectionValue_of_metricEntriesJointContDiffAt_three
      (hJoint x) hConn a u w).differentiableAt
  · intro a u w
    exact (hasDerivAt_iteratedConnectionValue_of_metricEntriesJointContDiffAt_three
      (hJoint x) hConn a u w).deriv

/-- Hamilton scalar evolution follows from the Ricci-flow equation and one
global joint `C³` metric-entry hypothesis, with no separate
`MetricFlowRegularAt` premise. -/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
  satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries
    hFlow hJoint
      (Filter.Eventually.of_forall fun y ↦
        metricFlowRegularAt_of_metricEntriesJointContDiffAt_three
          (x := y) hJoint)

end AnchorChartChristoffelFlow

end Poincare
