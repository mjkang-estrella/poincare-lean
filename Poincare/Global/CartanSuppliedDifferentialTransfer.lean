import Poincare.Global.CartanSuppliedDifferentialSuccessor
import Poincare.Global.DifferentialSuccessorIntervalNaturality

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
namespace CartanSuppliedDifferentialTransfer
variable [T2Space M]
open CartanSuppliedDifferentialSuccessor

private theorem reverse_chartTransitionMFDeriv_comp_forward_eq_id
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source) :
    (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)).comp
      (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) =
      ContinuousLinearMap.id ℝ E := by
  let zT : E := extChartAt I y₀ y₀
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) zT
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hzT : zT ∈ (extChartAt I y₀).target :=
    (extChartAt I y₀).map_source (mem_extChartAt_source y₀)
  have hxT : (extChartAt I y₀).symm zT = y₀ :=
    (extChartAt I y₀).left_inv (mem_extChartAt_source y₀)
  apply ContinuousLinearMap.ext
  intro w
  let Dnew : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I y₀).symm) (range I) zT
  let Cold : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p₀) y₀
  let Iold : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I p₀).symm) (range I) (extChartAt I p₀ y₀)
  let Cnew : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I y₀) y₀
  have holdCLM : Iold.comp Cold = ContinuousLinearMap.id ℝ E := by
    simpa [Iold, Cold] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy)
  have hnewCLM : Cnew.comp Dnew = ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hzT
    rw [hxT] at h
    simpa [Cnew, Dnew] using h
  change Drev (DT w) = w
  dsimp [Drev, DT, GeodesicTransport.chartTransitionMFDeriv]
  have hxT' : (chartAt E y₀).symm zT = y₀ := by
    simpa [extChartAt_coe] using hxT
  have hold' :
      (chartAt E p₀).symm ((chartAt E p₀) y₀) = y₀ :=
    (chartAt E p₀).left_inv (by
      simpa [extChartAt_source] using hy)
  rw [hxT', hold']
  change Cnew (Iold (Cold (Dnew w))) = w
  calc
    Cnew (Iold (Cold (Dnew w))) = Cnew (Dnew w) := by
      have hw := congrArg (fun L : E →L[ℝ] E => L (Dnew w)) holdCLM
      simpa [ContinuousLinearMap.comp_apply] using congrArg Cnew hw
    _ = w := by
      have hw := congrArg (fun L : E →L[ℝ] E => L w) hnewCLM
      simpa [ContinuousLinearMap.comp_apply] using hw

private theorem reverse_chartTransitionMFDeriv_eq_symm
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source)
    (T : E ≃L[ℝ] E)
    (hTco : (T : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) :
    GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀) =
      (T.symm : E →L[ℝ] E) := by
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hcomp : Drev.comp DT = ContinuousLinearMap.id ℝ E := by
    simpa [Drev, DT] using
      reverse_chartTransitionMFDeriv_comp_forward_eq_id p₀ y₀ hy
  apply ContinuousLinearMap.ext
  intro w
  calc
    Drev w = Drev (T (T.symm w)) := by rw [T.apply_symm_apply]
    _ = (Drev.comp DT) (T.symm w) := by
      rw [ContinuousLinearMap.comp_apply]
      have hTco' : (T : E →L[ℝ] E) = DT := by
        simpa [DT] using hTco
      rw [← hTco']
      rfl
    _ = T.symm w := by rw [hcomp]; rfl

omit [T2Space M] in
/-- The supplied host-coordinate map agrees with the manifold map on the host source. -/
private theorem chartMap_apply_host (Q : Interpretation g)
    (s : CartanChain.ChainState g) (y : M)
    (hy : y ∈ (extChartAt I (Q.sourceHost s.anchor)).source) :
    chartMap Q s (extChartAt I (Q.sourceHost s.anchor) y) =
      extChartAt I (Q.targetHost s.target) (map Q s y) := by
  change (chartAt E (Q.targetHost s.target))
    ((Q.targetNormal s.target).symm (linear Q s
      (Q.sourceNormal s.anchor ((chartAt E (Q.sourceHost s.anchor)).symm
        ((chartAt E (Q.sourceHost s.anchor)) y))))) = _
  rw [(chartAt E (Q.sourceHost s.anchor)).left_inv
    (by simpa only [extChartAt_source] using hy)]
  rfl

omit [T2Space M] in
/-- Coordinate pullback constructs the actual reanchored tangent isometry. -/
theorem data_of_coordinateData : ∀ (Q : Interpretation g)
  (s : CartanChain.ChainState g) (z : M) (w : CoordinateData Q s z),
  ∃ d : Data Q s z, d.toCoordinateData = w := by
  intro Q s z w
  let x₀ := Q.sourceHost s.anchor
  let x₁ := z
  let p₀ := Q.targetHost s.target
  let p₁ := map Q s z
  let zM := sourceExp Q s.anchor w.v
  let zT := targetExp Q s.target (linear Q s w.v)
  let A := w.A
  let B := w.B
  have hx₁_old : x₁ ∈ (extChartAt I x₀).source := w.source_mem_oldChart
  have hp₁_old : p₁ ∈ (extChartAt I p₀).source := w.target_mem_oldChart
  have hxcoord : extChartAt I x₀ x₁ = zM := w.source_coordinate
  have hpcoord : extChartAt I p₀ p₁ = zT := w.target_coordinate
  have hpullback := w.metric_pullback
  let zSource : E := extChartAt I x₁ x₁
  have hzSource : zSource ∈ (extChartAt I x₁).target := by
    exact
      (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsourceSymm : (extChartAt I x₁).symm zSource = x₁ := by
    exact
      (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hySource : (extChartAt I x₁).symm zSource ∈ (extChartAt I x₀).source := by
    rw [hsourceSymm]
    exact hx₁_old
  let sourceCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := x₁) (y₀ := x₀) zSource
  have hsourceCLM_inv : sourceCLM.IsInvertible := by
    dsimp [sourceCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hySource).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzSource)
  let sourceEquiv : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible sourceCLM hsourceCLM_inv
  have hsourceEquiv_coe : (sourceEquiv : E →L[ℝ] E) = sourceCLM := by
    simpa [sourceEquiv, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec hsourceCLM_inv
  have hsourceChartPoint :
      GeodesicTransport.chartTransition (n := 3) x₁ x₀ zSource = zM := by
    change extChartAt I x₀ ((extChartAt I x₁).symm zSource) = zM
    rw [hsourceSymm]
    exact hxcoord

  let zTarget : E := extChartAt I p₁ p₁
  have hzTarget : zTarget ∈ (extChartAt I p₁).target := by
    exact
      (extChartAt I p₁).map_source (mem_extChartAt_source p₁)
  have htargetSymm : (extChartAt I p₁).symm zTarget = p₁ := by
    exact
      (extChartAt I p₁).left_inv (mem_extChartAt_source p₁)
  have hyTarget : (extChartAt I p₁).symm zTarget ∈ (extChartAt I p₀).source := by
    rw [htargetSymm]
    exact hp₁_old
  let targetCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := p₁) (y₀ := p₀) zTarget
  have htargetCLM_inv : targetCLM.IsInvertible := by
    dsimp [targetCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hyTarget).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzTarget)
  let targetEquiv : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible targetCLM htargetCLM_inv
  have htargetEquiv_coe : (targetEquiv : E →L[ℝ] E) = targetCLM := by
    simpa [targetEquiv, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec htargetCLM_inv
  have htargetChartPoint :
      GeodesicTransport.chartTransition (n := 3) p₁ p₀ zTarget = zT := by
    change extChartAt I p₀ ((extChartAt I p₁).symm zTarget) = zT
    rw [htargetSymm]
    exact hpcoord

  let oldD : E ≃L[ℝ] E := (A.symm.trans (linear Q s)).trans B
  have holdD :
      (oldD : E →L[ℝ] E) =
        chartDifferential Q s A B := by
    ext u
    rfl
  let induced : E ≃L[ℝ] E :=
    (sourceEquiv.trans oldD).trans targetEquiv.symm
  have halign : ∀ u u' : E,
      CartanMap.targetAnchorBilinForm p₁ (induced u) (induced u') =
        CartanMap.sourceAnchorBilinForm g x₁ u u' := by
    intro u u'
    have htargetTransport :=
      GeodesicTransport.chartMetric_chartTransitionMFDeriv
        (g := roundSphereMetric3) (x₀ := p₁) (y₀ := p₀)
        (z := zTarget) hyTarget (induced u) (induced u')
    have htargetTransport' :
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
            (induced u) (induced u') =
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
            (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) := by
      have h := htargetTransport.symm
      rw [htargetChartPoint] at h
      change
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
            (induced u) (induced u') =
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
            (targetCLM (induced u)) (targetCLM (induced u')) at h
      rw [← htargetEquiv_coe] at h
      simpa [induced, oldD] using h
    have hpull := hpullback (sourceEquiv u) (sourceEquiv u')
    rw [← holdD] at hpull
    have hsourceTransport :=
      GeodesicTransport.chartMetric_chartTransitionMFDeriv
        (g := g) (x₀ := x₁) (y₀ := x₀)
        (z := zSource) hySource u u'
    have hsourceTransport' :
        CovariantDerivative.chartMetric g.inner x₀ zM
            (sourceEquiv u) (sourceEquiv u') =
          CovariantDerivative.chartMetric g.inner x₁ zSource u u' := by
      have h := hsourceTransport
      rw [hsourceChartPoint] at h
      change
        CovariantDerivative.chartMetric g.inner x₀ zM
            (sourceCLM u) (sourceCLM u') =
          CovariantDerivative.chartMetric g.inner x₁ zSource u u' at h
      rw [← hsourceEquiv_coe] at h
      exact h
    calc
      CartanMap.targetAnchorBilinForm p₁ (induced u) (induced u') =
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
            (induced u) (induced u') := rfl
      _ = CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ zT
            (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) :=
        htargetTransport'
      _ = CovariantDerivative.chartMetric g.inner x₀ zM
            (sourceEquiv u) (sourceEquiv u') := hpull
      _ = CovariantDerivative.chartMetric g.inner x₁ zSource u u' :=
        hsourceTransport'
      _ = CartanMap.sourceAnchorBilinForm g x₁ u u' := rfl
  let L : CartanMap.TangentAlignment g x₁ p₁ :=
    { toLinearEquiv := induced.toLinearEquiv, map_app' := halign }
  have hsourceDeriv : HasFDerivAt
      (GeodesicTransport.chartTransition x₁ x₀) sourceCLM zSource :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      x₁ x₀ hzSource hySource
  have hcartan : HasFDerivAt (chartMap Q s) (oldD : E →L[ℝ] E)
      (GeodesicTransport.chartTransition x₁ x₀ zSource) := by
    rw [hsourceChartPoint, holdD]
    exact w.cartan_chart_derivative.hasFDerivAt
  have htargetPoint : chartMap Q s
      (GeodesicTransport.chartTransition x₁ x₀ zSource) = extChartAt I p₀ p₁ := by
    rw [hsourceChartPoint]
    change targetExp Q s.target
      (linear Q s ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor w.v))) = _
    rw [(sourceExp Q s.anchor).left_inv w.source_vector_mem]
    exact hpcoord.symm
  have htargetOld : extChartAt I p₀ p₁ ∈ (extChartAt I p₀).target :=
    (extChartAt I p₀).map_source hp₁_old
  have htargetBack : (extChartAt I p₀).symm (extChartAt I p₀ p₁) ∈
      (extChartAt I p₁).source := by
    rw [(extChartAt I p₀).left_inv hp₁_old]
    exact mem_extChartAt_source p₁
  have houter := GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
    p₀ p₁ htargetOld htargetBack
  rw [reverse_chartTransitionMFDeriv_eq_symm p₀ p₁ hp₁_old targetEquiv
    htargetEquiv_coe] at houter
  rw [← htargetPoint] at houter
  have htotal := houter.comp zSource (hcartan.comp zSource hsourceDeriv)
  have hL : (L.toContinuousLinearEquiv : E →L[ℝ] E) =
      (targetEquiv.symm : E →L[ℝ] E).comp
        ((oldD : E →L[ℝ] E).comp sourceCLM) := by
    rw [← hsourceEquiv_coe]
    rfl
  rw [← hL] at htotal
  have htend : Tendsto (extChartAt I z).symm (𝓝 (extChartAt I z z)) (𝓝 z) := by
    have hc : ContinuousAt ((extChartAt I z).symm : E → M) (extChartAt I z z) :=
      continuousAt_extChartAt_symm z
    have h := hc.tendsto
    rw [(extChartAt I z).left_inv (mem_extChartAt_source z)] at h
    exact h
  have hmaptend : Tendsto (map Q s) (𝓝 z) (𝓝 (map Q s z)) :=
    ((germ Q s).continuousAt w.source_mem).tendsto
  have heq : reanchoredChartMap Q s z =ᶠ[𝓝 (extChartAt I z z)]
      (GeodesicTransport.chartTransition p₀ p₁ ∘ chartMap Q s ∘
        GeodesicTransport.chartTransition x₁ x₀) := by
    filter_upwards [htend ((isOpen_extChartAt_source x₀).mem_nhds hx₁_old),
      htend (hmaptend ((isOpen_extChartAt_source p₀).mem_nhds hp₁_old))] with a ha hb
    change extChartAt I p₁ (map Q s ((extChartAt I z).symm a)) =
      extChartAt I p₁ ((extChartAt I p₀).symm
        (chartMap Q s (extChartAt I x₀ ((extChartAt I z).symm a))))
    rw [chartMap_apply_host Q s _ ha, (extChartAt I p₀).left_inv hb]
  exact ⟨{ toCoordinateData := w
           alignment := L
           hasFDerivAt_reanchoredChartMap := htotal.congr_of_eventuallyEq heq }, rfl⟩

omit [T2Space M] in
/-- Equality of the coordinate germs determines the underlying alignment operator. -/
theorem alignment_clm_eq_of_eventuallyEq :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z),
  reanchoredChartMap Q s z =ᶠ[𝓝 (extChartAt I z z)] reanchoredChartMap R t z →
  (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
    (e.alignment.toContinuousLinearEquiv : E →L[ℝ] E) := by
  intro Q R s t z d e h
  exact d.hasFDerivAt_reanchoredChartMap.fderiv.symm.trans
    (h.fderiv_eq.trans e.hasFDerivAt_reanchoredChartMap.fderiv)

omit [T2Space M] in
/-- The geometric state only depends on its target and the underlying alignment operator. -/
private theorem chainState_eq_of_target_eq_of_clm_eq {x : M} {p q : RoundSphere3}
    (L : CartanMap.TangentAlignment g x p) (K : CartanMap.TangentAlignment g x q)
    (hp : p = q) (hL : (L.toContinuousLinearEquiv : E →L[ℝ] E) =
      (K.toContinuousLinearEquiv : E →L[ℝ] E)) :
    (⟨x, p, L⟩ : CartanChain.ChainState g) = ⟨x, q, K⟩ := by
  subst q
  have h : L = K := by
    apply DFunLike.coe_injective
    funext u
    exact DFunLike.congr_fun hL u
  cases h
  rfl

omit [T2Space M] in
/-- Open agreement of supplied maps identifies their differential successors. -/
theorem successor_eq_of_eqOn_open :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z) (W : Set M),
    IsOpen W → z ∈ W → EqOn (map Q s) (map R t) W → d.successor = e.successor := by
  intro Q R s t z d e W hW hz hEq
  have htarget := hEq hz
  have hmaps : map Q s =ᶠ[𝓝 z] map R t :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hz) hEq
  have htend : Tendsto (extChartAt I z).symm (𝓝 (extChartAt I z z)) (𝓝 z) := by
    have hc : ContinuousAt ((extChartAt I z).symm : E → M) (extChartAt I z z) :=
      continuousAt_extChartAt_symm z
    have h := hc.tendsto
    rw [(extChartAt I z).left_inv (mem_extChartAt_source z)] at h
    exact h
  have hcharts : reanchoredChartMap Q s z =ᶠ[𝓝 (extChartAt I z z)]
      reanchoredChartMap R t z := by
    filter_upwards [hmaps.comp_tendsto htend] with a ha
    dsimp only [Function.comp_def] at ha
    unfold reanchoredChartMap
    rw [htarget, ha]
  exact chainState_eq_of_target_eq_of_clm_eq d.alignment e.alignment htarget
    (alignment_clm_eq_of_eventuallyEq Q R s t z d e hcharts)

omit [T2Space M] in
/-- The supplied successor is independent of every analytic witness. -/
theorem successor_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d e : Data Q s z), d.successor = e.successor := by
  intro Q s z d e
  exact successor_eq_of_eqOn_open Q Q s s z d e univ isOpen_univ (mem_univ z)
    (fun _ _ => rfl)

omit [T2Space M] in
/-- The generic supplied endpoint cancels its extra host chart locally. -/
private theorem generic_sourceExp_comparison (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (v : E)
    (hv : v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x).source)
    (hc : GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x v ∈
      (chartAt E x).target) :
    v ∈ (sourceExp (generic g) x).source ∧
      (sourceExp (generic g) x : E → E) =ᶠ[𝓝 v]
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x : E → E) := by
  constructor
  · exact ⟨⟨hv, hc⟩, (chartAt E x).map_target hc⟩
  · have htend := ((GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x).continuousAt hv).tendsto
    filter_upwards [htend ((chartAt E x).open_target.mem_nhds hc)] with a ha
    exact (chartAt E x).right_inv ha

omit [T2Space M] in
/-- The supplied chart derivative follows from the endpoint derivatives and their local inverse. -/
private theorem chartMap_hasStrictFDerivAt (Q : Interpretation g)
    (s : CartanChain.ChainState g) (v : E) (A B : E ≃L[ℝ] E)
    (hv : v ∈ (sourceExp Q s.anchor).source)
    (hA : HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E) v)
    (hB : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E) (linear Q s v)) :
    HasStrictFDerivAt (chartMap Q s) (chartDifferential Q s A B)
      (sourceExp Q s.anchor v) := by
  have hinv := (sourceExp Q s.anchor).hasStrictFDerivAt_symm
    ((sourceExp Q s.anchor).map_source hv)
    (show HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E)
      ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor v)) by
      rw [(sourceExp Q s.anchor).left_inv hv]
      exact hA)
  have hlin := (linear Q s).hasStrictFDerivAt.comp (sourceExp Q s.anchor v) hinv
  have hout : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E)
      (linear Q s ((sourceExp Q s.anchor).symm (sourceExp Q s.anchor v))) := by
    rw [(sourceExp Q s.anchor).left_inv hv]
    exact hB
  exact hout.comp (sourceExp Q s.anchor v) hlin

omit [T2Space M] in
/-- Generic supplied and old data have the same actual derivative and successor. -/
private theorem generic_successor_eq (s : CartanChain.ChainState g) (z : M)
    (e : Data (generic g) s z) (d : DifferentialInducedSuccessor.Data s z) :
    e.successor = d.successor := by
  have hcharts : reanchoredChartMap (generic g) s z =
      DifferentialInducedSuccessor.reanchoredChartMap s z := by
    funext a
    change extChartAt I (map (generic g) s z)
      (map (generic g) s ((extChartAt I z).symm a)) =
      extChartAt I (s.map z) (s.map ((extChartAt I z).symm a))
    rw [generic_map_eq]
  have hd : HasFDerivAt (reanchoredChartMap (generic g) s z)
      (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) (extChartAt I z z) := by
    rw [hcharts]
    exact d.hasFDerivAt_reanchoredChartMap
  exact chainState_eq_of_target_eq_of_clm_eq e.alignment d.alignment
    (congrFun (generic_map_eq s) z) (e.hasFDerivAt_reanchoredChartMap.unique hd)

omit [T2Space M] in
/-- Old generic data admits a supplied presentation with the same vector and successor. -/
theorem ofGeneric : ∀ (s : CartanChain.ChainState g) (z : M)
    (d : DifferentialInducedSuccessor.Data s z),
    ∃ e : Data (generic g) s z, e.successor = d.successor ∧ e.v = d.v := by
  intro s z d
  have hsc : z ∈ (chartAt E s.anchor).source := by
    simpa only [extChartAt_source] using d.source_mem_oldChart
  have htc : s.map z ∈ (chartAt E s.target).source := by
    simpa only [extChartAt_source] using d.target_mem_oldChart
  have hsp : (chartAt E s.anchor) z =
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) s.anchor d.v := by
    simpa only [extChartAt_coe] using d.source_coordinate
  have htp : (chartAt E s.target) (s.map z) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target (s.alignment d.v) := by
    simpa only [extChartAt_coe] using d.target_coordinate
  have hs := generic_sourceExp_comparison g s.anchor d.v d.source_vector_mem
    (hsp ▸ (chartAt E s.anchor).map_source hsc)
  have ht := generic_sourceExp_comparison roundSphereMetric3 s.target (s.alignment d.v)
    d.target_vector_mem (htp ▸ (chartAt E s.target).map_source htc)
  have hse := hs.2.eq_of_nhds
  have hte : targetExp (generic g) s.target (linear (generic g) s d.v) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target (s.alignment d.v) := ht.2.eq_of_nhds
  have hA := d.source_exp_derivative.congr_of_eventuallyEq hs.2.symm
  have hB : HasStrictFDerivAt (targetExp (generic g) s.target)
      (d.B : E →L[ℝ] E) (linear (generic g) s d.v) :=
    d.target_exp_derivative.congr_of_eventuallyEq ht.2.symm
  have hnormal : (generic g).sourceNormal s.anchor z = d.v := by
    change (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).symm ((chartAt E s.anchor) z) = d.v
    rw [hsp]
    exact (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).left_inv d.source_vector_mem
  have hsource : z ∈ (germ (generic g) s).source := by
    refine ⟨⟨hsc, ?_⟩, ?_⟩
    · change (chartAt E s.anchor) z ∈
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) s.anchor).target
      rw [hsp]
      exact (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor).map_source d.source_vector_mem
    · change (generic g).sourceNormal s.anchor z ∈
        ((linear (generic g) s).toHomeomorph.toOpenPartialHomeomorph.trans
          ((generic g).targetNormal s.target).symm).source
      rw [hnormal]
      exact ⟨mem_univ _, ht.1.1⟩
  let w : CoordinateData (generic g) s z :=
    { source_anchor_valid := mem_univ _
      target_anchor_valid := mem_univ _
      source_mem := hsource
      v := d.v
      A := d.A
      B := d.B
      source_vector_mem := hs.1
      target_vector_mem := ht.1
      source_mem_oldChart := d.source_mem_oldChart
      target_mem_oldChart := by
        change map (generic g) s z ∈ (extChartAt I s.target).source
        rw [generic_map_eq]
        exact d.target_mem_oldChart
      source_coordinate := d.source_coordinate.trans hse.symm
      target_coordinate := by
        change extChartAt I s.target (map (generic g) s z) = _
        rw [generic_map_eq, hte]
        exact d.target_coordinate
      source_exp_derivative := hA
      target_exp_derivative := hB
      cartan_chart_derivative := chartMap_hasStrictFDerivAt
        (generic g) s d.v d.A d.B hs.1 hA hB
      metric_pullback := by
        intro u u'
        change CovariantDerivative.chartMetric roundSphereMetric3.inner s.target
          (targetExp (generic g) s.target (linear (generic g) s d.v))
          (chartDifferential (generic g) s d.A d.B u)
          (chartDifferential (generic g) s d.A d.B u') =
          CovariantDerivative.chartMetric g.inner s.anchor
            (sourceExp (generic g) s.anchor d.v) u u'
        rw [hse, hte]
        exact d.metric_pullback u u' }
  obtain ⟨e, he⟩ := data_of_coordinateData (generic g) s z w
  exact ⟨e, generic_successor_eq s z e d, congrArg CoordinateData.v he⟩

end CartanSuppliedDifferentialTransfer
end Poincare
