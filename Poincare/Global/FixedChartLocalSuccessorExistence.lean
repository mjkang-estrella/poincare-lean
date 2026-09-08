import Poincare.Global.CartanSuppliedDifferentialTransfer
import Poincare.Global.TangentAlignmentFiberCompactness
import Poincare.Global.UniformTangentAlignmentRigidity

/-!
# Compact control of retained normal domains

These estimates concern the actual retained patch domains. The uniform
strict differential and metric-pullback witnesses needed for successor data
are not constructed here.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartLocalSuccessorExistence
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3) (η : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ Q.sourceAnchors ∧ map Q ⟨x, p, L⟩ z ∈ Q.targetAnchors ∧
    z ∈ (germ Q ⟨x, p, L⟩).source ∧ Nonempty (Data Q ⟨x, p, L⟩ z)

/-- A compact set of retained anchors has a common normal source radius,
with retained successor anchors and arbitrarily small normal vectors. -/
theorem exists_uniform_normal_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ z : M, dist z x < η →
      z ∈ C.anchors ∧ z ∈ (C.normal x).source ∧ ‖C.normal x z‖ < ρ := by
  letI : MetricSpace M := g.toMetricSpace
  let W : Set (M × M) := C.rawLocalFamily.controlledSourceLocus ρ ∩
    Prod.snd ⁻¹' C.anchors
  have hW : IsOpen W :=
    (C.rawLocalFamily.isOpen_controlledSourceLocus ρ).inter
      (C.isOpen_anchors.preimage continuous_snd)
  have hdiag : IsCompact ((fun x : M => (x, x)) '' K) :=
    hK.image (continuous_id.prodMk continuous_id)
  have hsub : (fun x : M => (x, x)) '' K ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨⟨hKC hx, C.anchor_mem_normal_source x (hKC hx)⟩, ?_⟩, hKC hx⟩
    change C.normal x x ∈ ball (0 : E) ρ
    rw [C.normal_anchor x (hKC hx)]
    exact mem_ball_self hρ
  obtain ⟨η, hη, hηW⟩ := hdiag.exists_cthickening_subset_open hW hsub
  refine ⟨η, hη, ?_⟩
  intro x hx z hz
  have hmem : (x, z) ∈ cthickening η ((fun x : M => (x, x)) '' K) := by
    apply mem_cthickening_of_dist_le (x, z) (x, x) η
      ((fun x : M => (x, x)) '' K) ⟨x, hx, rfl⟩
    simpa [Prod.dist_eq] using hz.le
  have hw := hηW hmem
  refine ⟨hw.2, hw.1.1.2, ?_⟩
  simpa [CartanSourceExponential.LocalFamily.controlledSourceLocus,
    FixedChartUniformSourceNormal.Patch.rawLocalFamily, mem_ball, dist_eq_norm] using hw.1.2

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Small velocities share the actual endpoint domain over a compact anchor
set, and their endpoints remain available as new anchors. -/
theorem exists_uniform_endpoint_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ C.anchors := by
  have he : ∀ᶠ v : E in 𝓝 0, ∀ x ∈ K,
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ C.anchors := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hxC := hKC hx
    have hxchart : x ∈ (chartAt E x₀).source := by
      simpa only [extChartAt_source] using hxC.1
    let f : E × M → E × E := fun q => (extChartAt I x₀ q.2, C.T⁻¹ • q.1)
    have hf : ContinuousAt f (0, x) :=
      ((continuousAt_extChartAt' hxC.1).comp continuousAt_snd).prodMk
        (continuousAt_const.smul continuousAt_fst)
    have hf0 : f (0, x) = (extChartAt I x₀ x, 0) := by simp [f]
    have hsrc : f (0, x) ∈ C.P.source := by
      rw [hf0]
      exact C.zero_mem_source _ hxC.2
    have hp : ContinuousAt (fun q => (C.P (f q)).2) (0, x) :=
      ((C.P.continuousAt hsrc).comp hf).snd
    have hp0 : (C.P (f (0, x))).2 = extChartAt I x₀ x := by
      rw [hf0, C.stationary _ hxC.2]
    have htarget : (C.P (f (0, x))).2 ∈ (chartAt E x₀).target := by
      rw [hp0]
      exact (chartAt E x₀).map_source hxchart
    have hc : ContinuousAt (fun q : E × M => C.endpoint q.2 q.1) (0, x) := by
      exact ((chartAt E x₀).continuousAt_symm htarget).comp
        (f := fun q : E × M => (C.P (f q)).2) hp
    have he0 : C.endpoint x (0 : E) = x := C.endpoint_zero x hxC
    have hret : ∀ᶠ q : E × M in 𝓝 (0, x), C.endpoint q.2 q.1 ∈ C.anchors := by
      apply hc.tendsto
      simpa only [he0] using C.isOpen_anchors.mem_nhds hxC
    filter_upwards [hf.tendsto (C.P.open_source.mem_nhds hsrc),
      hp.tendsto ((chartAt E x₀).open_target.mem_nhds htarget), hret] with q hq ht hr
    exact ⟨⟨⟨mem_univ _, hq⟩, ht⟩, hr⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ρ, hρ, fun x hx v hv => hball (by simpa using hv) x hx⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- The fixed host metric is uniformly comparable to the model norm on
every compact retained anchor set. -/
theorem exists_uniform_host_metric_comparison {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ), ∀ x ∈ K, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) v v ∧
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) v v ≤ b * ‖v‖ ^ 2 := by
  let G : M → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x)
  have hG : ContinuousOn G K := by
    intro x hx
    exact ((UniformAnchoredFTransition.chartMetric_contDiffAt_one_of_mem_target
      g x₀ ((extChartAt I x₀).map_source (hKC hx).1)).continuousAt.comp
        (continuousAt_extChartAt' (hKC hx).1)).continuousWithinAt
  have hcompact : IsCompact (K ×ˢ sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  have hcontinuous : ContinuousOn (fun q : M × E => G q.1 q.2 q.2)
      (K ×ˢ sphere (0 : E) 1) :=
    ((hG.comp continuousOn_fst (fun _ hq => hq.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  have hpositive : ∀ q ∈ K ×ˢ sphere (0 : E) 1, 0 < G q.1 q.2 q.2 := by
    intro q hq
    apply CovariantDerivative.chartMetric_posDef g.inner (fun y v hv => g.pos y v hv) x₀
      (isInvertible_mfderivWithin_extChartAt_symm
        ((extChartAt I x₀).map_source (hKC hq.1).1))
    have hn : ‖q.2‖ = 1 := by simpa using hq.2
    intro hz
    simp [hz] at hn
  obtain ⟨a, ha, halower⟩ := hcompact.exists_forall_le' hcontinuous hpositive
  have hbounded : Bornology.IsBounded (G '' K) := (hK.image_of_continuousOn hG).isBounded
  obtain ⟨b, hb, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨a, ha, b, hb, ?_⟩
  intro x hx v
  constructor
  · by_cases hv : v = 0
    · simp [hv]
    have hn := norm_ne_zero_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv
    have hr : ‖v‖ • w = v := by
      simp [w, smul_smul, hn]
    have he : G x v v = ‖v‖ ^ 2 * G x w w := by
      conv_lhs => rw [← hr]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    change a * ‖v‖ ^ 2 ≤ G x v v
    rw [he, mul_comm a]
    exact mul_le_mul_of_nonneg_left (halower (x, w) ⟨hx, hw⟩) (sq_nonneg _)
  · have hbG : ‖G x‖ ≤ b := hbound _ ⟨x, hx, rfl⟩
    change G x v v ≤ b * ‖v‖ ^ 2
    calc
      G x v v ≤ ‖G x v v‖ := Real.le_norm_self _
      _ ≤ ‖G x‖ * ‖v‖ * ‖v‖ := (G x).le_opNorm₂ v v
      _ ≤ b * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The retained frame transports the host metric to the preferred anchor metric. -/
theorem patchFrame_metric {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (hx : x ∈ C.anchors) (u v : E) :
    CartanMap.sourceAnchorChartMetric g x (patchFrame C x u) (patchFrame C x v) =
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) u v := by
  have hframe : (patchFrame C x : E →L[ℝ] E) =
      FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x := by
    unfold patchFrame
    rw [dif_pos hx]
    exact Classical.choose_spec
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx)
  have hy : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈ (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  have ht := GeodesicTransport.chartMetric_chartTransitionDeriv g x₀ x
    ((extChartAt I x₀).map_source hx.1) hy u v
  have hpoint : GeodesicTransport.chartTransition x₀ x (extChartAt I x₀ x) =
      extChartAt I x x := by
    change extChartAt I x ((extChartAt I x₀).symm (extChartAt I x₀ x)) = _
    rw [(extChartAt I x₀).left_inv hx.1]
  rw [hpoint] at ht
  change CartanMap.sourceAnchorChartMetric g x
    ((patchFrame C x : E →L[ℝ] E) u) ((patchFrame C x : E →L[ℝ] E) v) = _
  rw [hframe]
  exact ht

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Framed alignments preserve the two fixed host metrics at the moving anchors. -/
theorem linear_metric {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (x : M) (hx : x ∈ C.anchors) (p : RoundSphere3) (hp : p ∈ D.anchors)
    (L : CartanMap.TangentAlignment g x p) (u v : E) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ (extChartAt I p₀ p)
      (linear (patch C D) ⟨x, p, L⟩ u) (linear (patch C D) ⟨x, p, L⟩ v) =
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) u v := by
  calc
    _ = CartanMap.targetAnchorChartMetric p
        (patchFrame D p (linear (patch C D) ⟨x, p, L⟩ u))
        (patchFrame D p (linear (patch C D) ⟨x, p, L⟩ v)) :=
      (patchFrame_metric D p hp _ _).symm
    _ = CartanMap.targetAnchorChartMetric p
        (L (patchFrame C x u)) (L (patchFrame C x v)) := by simp [linear, patch]
    _ = CartanMap.sourceAnchorChartMetric g x (patchFrame C x u) (patchFrame C x v) :=
      L.map_app _ _
    _ = _ := patchFrame_metric C x hx u v

omit [CompactSpace M] [ConnectedSpace M] in
/-- One operator bound covers all alignments as both retained anchors move
over arbitrary compact sets. -/
theorem exists_uniform_linear_bound {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    ∃ B > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ L : CartanMap.TangentAlignment g x p,
        ‖(linear (patch C D) ⟨x, p, L⟩ : E →L[ℝ] E)‖ ≤ B := by
  obtain ⟨_, _, b, hb, hsource⟩ := exists_uniform_host_metric_comparison C K hK hKC
  obtain ⟨a, ha, _, _, htarget⟩ := exists_uniform_host_metric_comparison D H hH hHD
  refine ⟨Real.sqrt (b / a), Real.sqrt_pos.mpr (div_pos hb ha), ?_⟩
  intro x hx p hp L
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
  intro v hv
  have hlow := (htarget p hp (linear (patch C D) ⟨x, p, L⟩ v)).1
  rw [linear_metric C D x (hKC hx) p (hHD hp) L] at hlow
  have hupp := (hsource x hx v).2
  rw [hv, one_pow, mul_one] at hupp
  have hsquare : ‖linear (patch C D) ⟨x, p, L⟩ v‖ ^ 2 ≤ b / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hroot := Real.sq_sqrt (div_pos hb ha).le
  have hn := norm_nonneg (linear (patch C D) ⟨x, p, L⟩ v)
  have hr := Real.sqrt_nonneg (b / a)
  change ‖linear (patch C D) ⟨x, p, L⟩ v‖ ≤ Real.sqrt (b / a)
  nlinarith

/-- The source and both successor anchors in the requested compact contract
share one positive radius, independently of all tangent alignments. -/
theorem exists_uniform_domain_radius {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
        z ∈ (patch C D).sourceAnchors ∧
        map (patch C D) ⟨x, p, L⟩ z ∈ (patch C D).targetAnchors ∧
        z ∈ (germ (patch C D) ⟨x, p, L⟩).source := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨B, hB, hbound⟩ := exists_uniform_linear_bound C D K H hK hKC hH hHD
  obtain ⟨ρ, hρ, htarget⟩ := exists_uniform_endpoint_radius D H hH hHD
  obtain ⟨η, hη, hsource⟩ := exists_uniform_normal_radius C K hK hKC (div_pos hρ hB)
  refine ⟨η, hη, ?_⟩
  intro x hx p hp L z hz
  obtain ⟨hzC, hzN, hv⟩ := hsource x hx z hz
  have hnorm : ‖linear (patch C D) ⟨x, p, L⟩ (C.normal x z)‖ < ρ := by
    calc
      _ ≤ ‖(linear (patch C D) ⟨x, p, L⟩ : E →L[ℝ] E)‖ * ‖C.normal x z‖ :=
        (linear (patch C D) ⟨x, p, L⟩ : E →L[ℝ] E).le_opNorm _
      _ ≤ B * ‖C.normal x z‖ :=
        mul_le_mul_of_nonneg_right (hbound x hx p hp L) (norm_nonneg _)
      _ < ρ := by simpa only [mul_comm B] using (lt_div_iff₀ hB).mp hv
  obtain ⟨htsrc, htanchor⟩ := htarget p hp _ hnorm
  exact ⟨hzC, htanchor, hzN, mem_univ _, htsrc⟩

/-- The remaining analytic requirement uses the actual supplied normal vector.
It asserts strict endpoint derivatives and their metric pullback on one radius
chosen before the moving anchors and alignments. -/
def UniformDifferentialPullback (Q : Interpretation g) (K : Set M)
    (H : Set RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
      let s : CartanChain.ChainState g := ⟨x, p, L⟩
      let v := Q.sourceNormal x z
      ∃ A B : E ≃L[ℝ] E,
        HasStrictFDerivAt (sourceExp Q x) (A : E →L[ℝ] E) v ∧
        HasStrictFDerivAt (targetExp Q p) (B : E →L[ℝ] E) (linear Q s v) ∧
        ∀ u u' : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost p)
            (targetExp Q p (linear Q s v))
            (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
          CovariantDerivative.chartMetric g.inner (Q.sourceHost x)
            (sourceExp Q x v) u u'

/-- The verified domain estimate and the stated analytic remainder construct
every coordinate field and the actual induced alignment. This is conditional. -/
theorem exists_onCompact_of_uniformDifferentialPullback
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors)
    (hanalytic : UniformDifferentialPullback (patch C D) K H) :
    ∃ η > (0 : ℝ), OnCompact (patch C D) K H η := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨ηd, hηd, hdomain⟩ := exists_uniform_domain_radius C D K H hK hKC hH hHD
  obtain ⟨ηa, hηa, hfields⟩ := hanalytic
  refine ⟨min ηd ηa, lt_min hηd hηa, ?_⟩
  intro x hx p hp L z hz
  obtain ⟨hzC, hzD, hzsource⟩ := hdomain x hx p hp L z (hz.trans_le (min_le_left _ _))
  obtain ⟨A, B, hA, hB, hpull⟩ := hfields x hx p hp L z (hz.trans_le (min_le_right _ _))
  let Q := patch C D
  let s : CartanChain.ChainState g := ⟨x, p, L⟩
  let v : E := Q.sourceNormal x z
  have hzinv : (Q.sourceNormal x).symm v = z := (Q.sourceNormal x).left_inv hzsource.1
  have hzhost : z ∈ (extChartAt I x₀).source := hzC.1
  have hphost : map Q s z ∈ (extChartAt I p₀).source := hzD.1
  have hvsource : v ∈ (sourceExp Q x).source := by
    refine ⟨(Q.sourceNormal x).map_source hzsource.1, ?_⟩
    change (Q.sourceNormal x).symm v ∈ (chartAt E x₀).source
    rw [hzinv]
    simpa only [extChartAt_source] using hzhost
  have hvtarget : linear Q s v ∈ (targetExp Q p).source := by
    refine ⟨hzsource.2.2, ?_⟩
    change map Q s z ∈ (chartAt E p₀).source
    simpa only [extChartAt_source] using hphost
  have hinv := (sourceExp Q x).hasStrictFDerivAt_symm
    ((sourceExp Q x).map_source hvsource)
    (show HasStrictFDerivAt (sourceExp Q x) (A : E →L[ℝ] E)
        ((sourceExp Q x).symm (sourceExp Q x v)) by
      rw [(sourceExp Q x).left_inv hvsource]
      exact hA)
  have hlin := (linear Q s).hasStrictFDerivAt.comp (sourceExp Q x v) hinv
  have hout : HasStrictFDerivAt (targetExp Q p) (B : E →L[ℝ] E)
      (linear Q s ((sourceExp Q x).symm (sourceExp Q x v))) := by
    rw [(sourceExp Q x).left_inv hvsource]
    exact hB
  let w : CoordinateData Q s z := {
    source_anchor_valid := hKC hx
    target_anchor_valid := hHD hp
    source_mem := hzsource
    v := v, A := A, B := B
    source_vector_mem := hvsource
    target_vector_mem := hvtarget
    source_mem_oldChart := hzhost
    target_mem_oldChart := hphost
    source_coordinate := by
      change extChartAt I x₀ z = (chartAt E x₀) ((Q.sourceNormal x).symm v)
      rw [hzinv]
      rfl
    target_coordinate := rfl
    source_exp_derivative := hA
    target_exp_derivative := hB
    cartan_chart_derivative := hout.comp (sourceExp Q x v) hlin
    metric_pullback := hpull }
  obtain ⟨d, _⟩ := CartanSuppliedDifferentialTransfer.data_of_coordinateData Q s z w
  exact ⟨hzC, hzD, hzsource, ⟨d⟩⟩

end FixedChartLocalSuccessorExistence
end Poincare
