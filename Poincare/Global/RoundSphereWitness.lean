import Poincare.Global.ChartCurvatureBridge6

/-!
# Round sphere constant-curvature witness

This module assembles the chart curvature computation for the stereographic
round sphere with the global curvature transport bridge.
-/

noncomputable section

open Bundle Filter FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- Chart curvature is germ-local in the Christoffel field. -/
theorem chartCurvatureOf_congr_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Γ Γ' : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : Γ =ᶠ[𝓝 z] Γ') (u v w : E) :
    chartCurvatureOf Γ z u v w = chartCurvatureOf Γ' z u v w := by
  unfold chartCurvatureOf
  have hf : fderiv ℝ Γ z = fderiv ℝ Γ' z := hΓ.fderiv_eq
  have hz : Γ z = Γ' z := hΓ.self_of_nhds
  rw [hf, hz]

/--
Near the anchor, the transported round-sphere Christoffel field has the same
chart curvature as the explicit stereographic sphere Christoffel field.
-/
theorem roundSphereMetric3_chartCurvatureOf_chartChristoffelField_eq_sphereChristoffel
    (x₀ : RoundSphere3) (u w a : RoundSphereModel3) :
    chartCurvatureOf
        (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀)
        (extChartAt (𝓡 3) x₀ x₀) u w a =
      chartCurvatureOf (sphereChristoffel (E := RoundSphereModel3))
        (extChartAt (𝓡 3) x₀ x₀) u w a := by
  refine chartCurvatureOf_congr_of_eventuallyEq ?_ u w a
  let oneLocus : Set RoundSphereModel3 :=
    {z | GeodesicTransport.cutoff (n := 3) x₀ z = 1}
  have hone_mem : oneLocus ∈ 𝓝 (extChartAt (𝓡 3) x₀ x₀) := by
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x₀)
  rcases mem_nhds_iff.mp hone_mem with ⟨s, hs, hsopen, hzs⟩
  filter_upwards [hsopen.mem_nhds hzs] with z hz
  have hχ : (fun y : RoundSphereModel3 =>
        GeodesicTransport.cutoff (n := 3) x₀ y) =ᶠ[𝓝 z]
      fun _ => (1 : ℝ) := by
    exact mem_nhds_iff.mpr ⟨s, hs, hsopen, hz⟩
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro q
  exact
    roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
      x₀ hχ p q

/--
Lowering the transported global curvature at the anchor agrees with lowering
the chart Christoffel curvature by the transported chart metric.
-/
theorem roundSphereMetric3_inner_chartTransported_curvature_eq_chartMetric
    (x₀ : RoundSphere3) (u w a b : TangentSpace (𝓡 3) x₀) :
    roundSphereMetric3.inner x₀
        (CovariantDerivative.curvatureOp roundSphereMetric3.leviCivita
          (extend RoundSphereModel3 u) (extend RoundSphereModel3 w)
          (extend RoundSphereModel3 a) x₀) b =
      CovariantDerivative.chartMetric roundSphereMetric3.inner x₀
        (extChartAt (𝓡 3) x₀ x₀)
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀)
          (extChartAt (𝓡 3) x₀ x₀) u w a)
        b := by
  let z₀ : RoundSphereModel3 := extChartAt (𝓡 3) x₀ x₀
  let R : Π y : RoundSphere3, TangentSpace (𝓡 3) y :=
    CovariantDerivative.curvatureOp roundSphereMetric3.leviCivita
      (extend RoundSphereModel3 u) (extend RoundSphereModel3 w)
      (extend RoundSphereModel3 a)
  have htarget : z₀ ∈ (extChartAt (𝓡 3) x₀).target := by
    simp [z₀]
  have hb :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend RoundSphereModel3 b) z₀ = b := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (x := x₀) (y := x₀) (mem_extChartAt_source (I := 𝓡 3) x₀) b)
  have hcurv :
      chartCurvatureOf
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀)
          z₀ u w a =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀ := by
    simpa [z₀, R] using
      (ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp
        (g := roundSphereMetric3) (x₀ := x₀) u w a)
  have hlower :
      CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 b) z₀) =
        roundSphereMetric3.inner x₀ (R x₀) b := by
    have h :=
      CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
        (g := roundSphereMetric3.inner) (x₀ := x₀) (Y := R)
        (Z := extend RoundSphereModel3 b) (hz := htarget)
    have hsymm : (extChartAt (𝓡 3) x₀).symm z₀ = x₀ := by
      simp [z₀]
    rw [hsymm] at h
    simpa [z₀, R] using h
  calc
    roundSphereMetric3.inner x₀ (R x₀) b =
        CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ R z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 b) z₀) := hlower.symm
    _ = CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀
          (chartCurvatureOf
            (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀)
            z₀ u w a)
          b := by rw [← hcurv, hb]

/-- The chart metric at the anchor is the conformal stereographic metric. -/
theorem roundSphereMetric3_chartMetric_anchor_eq_conformal
    (x₀ : RoundSphere3) (p q : TangentSpace (𝓡 3) x₀) :
    roundSphereMetric3.inner x₀ p q =
      conformalChartMetricForm
        (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ)
        (extChartAt (𝓡 3) x₀ x₀) p q := by
  let z₀ : RoundSphereModel3 := extChartAt (𝓡 3) x₀ x₀
  have htarget : z₀ ∈ (extChartAt (𝓡 3) x₀).target := by
    simp [z₀]
  have hp :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend RoundSphereModel3 p) z₀ = p := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (x := x₀) (y := x₀) (mem_extChartAt_source (I := 𝓡 3) x₀) p)
  have hq :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (extend RoundSphereModel3 q) z₀ = q := by
    simpa [z₀] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (x := x₀) (y := x₀) (mem_extChartAt_source (I := 𝓡 3) x₀) q)
  have hlower :
      CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 p) z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 q) z₀) =
        roundSphereMetric3.inner x₀ p q := by
    have h :=
      CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection
        (g := roundSphereMetric3.inner) (x₀ := x₀)
        (Y := extend RoundSphereModel3 p) (Z := extend RoundSphereModel3 q)
        (hz := htarget)
    have hsymm : (extChartAt (𝓡 3) x₀).symm z₀ = x₀ := by
      simp [z₀]
    rw [hsymm] at h
    simpa [z₀] using h
  calc
    roundSphereMetric3.inner x₀ p q =
        CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 p) z₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (extend RoundSphereModel3 q) z₀) := hlower.symm
    _ = CovariantDerivative.chartMetric roundSphereMetric3.inner x₀ z₀ p q := by
          rw [hp, hq]
    _ = conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z₀ p q := by
          rw [roundSphereMetric3_chartMetric_eq]
          rfl

/--
At the anchor, the global Kulkarni-Nomizu tensor of the round metric is the
chart Kulkarni-Nomizu tensor of the stereographic conformal chart metric.
-/
theorem roundSphereMetric3_tensorKulkarniNomizuAt_eq_chart
    (x₀ : RoundSphere3) (u w a b : TangentSpace (𝓡 3) x₀) :
    ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
        (n := 3) (M := RoundSphere3) x₀
        (fun p q ↦ roundSphereMetric3.inner x₀ p q)
        (fun p q ↦ roundSphereMetric3.inner x₀ p q) u w a b =
      chartTensorKulkarniNomizu
        (conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ)
          (extChartAt (𝓡 3) x₀ x₀))
        (conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ)
          (extChartAt (𝓡 3) x₀ x₀))
        u w a b := by
  unfold ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
    chartTensorKulkarniNomizu
  simp only [roundSphereMetric3_chartMetric_anchor_eq_conformal]

/-- The bundled round metric on `S³` has constant sectional curvature `1`. -/
theorem roundSphereMetric3_hasConstantSectionalCurvature_one :
    HasConstantSectionalCurvature3 roundSphereMetric3 1 := by
  intro x u w a b
  let z₀ : RoundSphereModel3 := extChartAt (𝓡 3) x x
  have hΓ :=
    roundSphereMetric3_chartCurvatureOf_chartChristoffelField_eq_sphereChristoffel
      x u w a
  have hlower :=
    roundSphereMetric3_inner_chartTransported_curvature_eq_chartMetric x u w a b
  have hchartMetric :
      CovariantDerivative.chartMetric roundSphereMetric3.inner x z₀
          (chartCurvatureOf (sphereChristoffel (E := RoundSphereModel3))
            z₀ u w a) b =
        conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z₀
          (chartCurvatureOf (sphereChristoffel (E := RoundSphereModel3))
            z₀ u w a) b := by
    rw [roundSphereMetric3_chartMetric_eq]
    rfl
  calc
    roundSphereMetric3.inner x
        (CovariantDerivative.curvatureOp roundSphereMetric3.leviCivita
          (extend RoundSphereModel3 u) (extend RoundSphereModel3 w)
          (extend RoundSphereModel3 a) x) b =
        CovariantDerivative.chartMetric roundSphereMetric3.inner x z₀
          (chartCurvatureOf
            (GeodesicTransport.chartChristoffelField roundSphereMetric3 x)
            z₀ u w a) b := by
          simpa [z₀] using hlower
    _ = CovariantDerivative.chartMetric roundSphereMetric3.inner x z₀
          (chartCurvatureOf (sphereChristoffel (E := RoundSphereModel3))
            z₀ u w a) b := by
          rw [hΓ]
    _ = conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z₀
          (chartCurvatureOf (sphereChristoffel (E := RoundSphereModel3))
            z₀ u w a) b := hchartMetric
    _ = -(1 / 2 : ℝ) *
          chartTensorKulkarniNomizu
            (conformalChartMetricForm
              (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z₀)
            (conformalChartMetricForm
              (stereoInvFunAuxConformalFactor : RoundSphereModel3 → ℝ) z₀)
            u w a b := by
          exact conformalChartMetric_chartCurvatureOf_sphereChristoffel z₀ u w a b
    _ = -(1 / 2 : ℝ) *
          ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
            (n := 3) (M := RoundSphere3) x
            (fun p q ↦ roundSphereMetric3.inner x p q)
            (fun p q ↦ roundSphereMetric3.inner x p q) u w a b := by
          rw [roundSphereMetric3_tensorKulkarniNomizuAt_eq_chart]

end Poincare
