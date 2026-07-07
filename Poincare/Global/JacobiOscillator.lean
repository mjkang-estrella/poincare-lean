import Poincare.Global.ChartCurvatureBridgeZoneClose
import Poincare.Global.GeodesicLengthFinal

/-!
# Constant-curvature Jacobi oscillator on a cutoff-one interval

This module assembles the arbitrary-point constant-curvature chart curvature
identity with the existing Jacobi bookkeeping.  The main non-vacuous payload is
the raised vector contraction in the cutoff-one zone and its covariant Jacobi
second-derivative form.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

private theorem two_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

private theorem two_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
  rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

omit [T2Space M] in
/-- The chart Christoffel field is symmetric in its two vector slots as a germ. -/
theorem chartChristoffelField_eventually_symm
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z u v : E3) :
    (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) u v) =ᶠ[𝓝 z]
      fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) v u := by
  let G : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀
  let b : Π _ : E3, LinearMap.BilinForm ℝ E3 :=
    CovariantDerivative.chartBilin (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀
  let hb : ∀ z, (b z).Nondegenerate :=
    CovariantDerivative.chartBilin_nondegenerate
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3))
      (GeodesicTransport.backgroundMetric_pos (n := 3)) g.inner
      (fun y u hu => g.inner_pos y (v := u) hu) x₀
      (GeodesicTransport.cutoff_nonneg (n := 3) x₀)
      (GeodesicTransport.cutoff_le_one (n := 3) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := 3) x₀)
  have hg2 :
      ContMDiff I3 ((I3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E3 →L[ℝ] E3 →L[ℝ] ℝ)
              (fun y : M => TangentSpace I3 y →L[ℝ] TangentSpace I3 y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le two_le_top
  have hblend : ContDiff ℝ 2 G := by
    dsimp [G]
    exact CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀
      two_add_one_le_top (GeodesicTransport.cutoff_contDiff (n := 3) x₀)
      (GeodesicTransport.cutoff_tsupport (n := 3) x₀) hg2
  have hGd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ G y :=
    Filter.Eventually.of_forall fun y => (hblend.differentiable (by norm_num)) y
  have hGsymm : ∀ (y p q : E3), G y p q = G y q p := by
    intro y p q
    dsimp [G]
    exact CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3))
      (GeodesicTransport.backgroundMetric_symm (n := 3)) g.inner
      (fun y v w => g.inner_symm y v w) x₀ y p q
  change
    (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        E3 →L[ℝ] E3 →L[ℝ] E3) u v) =ᶠ[𝓝 z]
      fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        E3 →L[ℝ] E3 →L[ℝ] E3) v u
  exact ChartCurvatureBridge.eventually_christoffelOneForm_symm
    (G := G) (b := b) (hb := hb) (z := z) hGd hGsymm u v

omit [T2Space M] in
/-- Pointwise symmetry of the chart Christoffel field. -/
theorem chartChristoffelField_symm
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z u v : E3) :
    (GeodesicTransport.chartChristoffelField g x₀ z) u v =
      (GeodesicTransport.chartChristoffelField g x₀ z) v u :=
  (chartChristoffelField_eventually_symm (g := g) (x₀ := x₀) z u v).eq_of_nhds

omit [T2Space M] in
/-- Derivative-slot symmetry needed by the covariant Jacobi second identity. -/
theorem chartChristoffelField_fderiv_symm
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z v J : E3) :
    (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) z) v) v) J =
      (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) z) v) J) v := by
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 :=
    GeodesicTransport.chartChristoffelField g x₀
  have hΓd : DifferentiableAt ℝ Γ z :=
    (GeodesicTransport.chartChristoffelField_contDiffAt_base
      (g := g) (x₀ := x₀) z).differentiableAt (by norm_num)
  have hΓv : DifferentiableAt ℝ (fun y ↦ Γ y v) z :=
    hΓd.clm_apply (differentiableAt_const v)
  have hΓJ : DifferentiableAt ℝ (fun y ↦ Γ y J) z :=
    hΓd.clm_apply (differentiableAt_const J)
  have hleft₁ : ((fderiv ℝ Γ z) v) v =
      fderiv ℝ (fun y ↦ Γ y v) z v :=
    ChartCurvatureBridge.fderiv_clm_family_apply hΓd v v
  have hleft₂ : (fderiv ℝ (fun y ↦ Γ y v) z v) J =
      fderiv ℝ (fun y ↦ Γ y v J) z v :=
    ChartCurvatureBridge.fderiv_clm_family_apply hΓv v J
  have hright₁ : ((fderiv ℝ Γ z) v) J =
      fderiv ℝ (fun y ↦ Γ y J) z v :=
    ChartCurvatureBridge.fderiv_clm_family_apply hΓd v J
  have hright₂ : (fderiv ℝ (fun y ↦ Γ y J) z v) v =
      fderiv ℝ (fun y ↦ Γ y J v) z v :=
    ChartCurvatureBridge.fderiv_clm_family_apply hΓJ v v
  have hgerm :
      (fun y ↦ Γ y v J) =ᶠ[𝓝 z] fun y ↦ Γ y J v :=
    chartChristoffelField_eventually_symm (g := g) (x₀ := x₀) z v J
  have hder :
      fderiv ℝ (fun y ↦ Γ y v J) z v =
        fderiv ℝ (fun y ↦ Γ y J v) z v := by
    exact congrArg (fun L : E3 →L[ℝ] E3 => L v)
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hgerm)
  calc
    (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) z) v) v) J =
        (fderiv ℝ (fun y ↦ Γ y v) z v) J := by
          simpa [Γ] using congrArg (fun L : E3 →L[ℝ] E3 => L J) hleft₁
    _ = fderiv ℝ (fun y ↦ Γ y v J) z v := hleft₂
    _ = fderiv ℝ (fun y ↦ Γ y J v) z v := hder
    _ = (fderiv ℝ (fun y ↦ Γ y J) z v) v := hright₂.symm
    _ = (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) z) v) J) v := by
          simpa [Γ] using congrArg (fun L : E3 →L[ℝ] E3 => L v) hright₁.symm

/--
Lowered constant-curvature-one contraction in the cutoff-one zone: for a unit
transverse pair, lowering `R(v,J)v` by the transported chart metric gives the
same covector as lowering `-J`.
-/
theorem chartCurvatureOf_chartChristoffelField_unit_orthogonal_lowered_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J : E3)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ z v v = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0)
    (b : E3) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀) z v J v) b =
      -CovariantDerivative.chartMetric g.inner x₀ z J b := by
  have hzone :=
    ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone
      (g := g) hcurv (x₀ := x₀) (z := z) hz hχone v J v b
  have hcontraction :=
    chartTensorKulkarniNomizu_unit_orthogonal_contraction
      (G := fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
      (v := v) (J := J) (a := b) hunit horth
  exact hzone.trans hcontraction

/--
Vector form of the cutoff-one constant-curvature contraction:
`R(v,J)v = -J` for unit speed and transverse `J`.
-/
theorem chartCurvatureOf_chartChristoffelField_unit_orthogonal_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J : E3)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ z v v = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z v J v = -J := by
  let B : LinearMap.BilinForm ℝ E3 :=
    CovariantDerivative.chartBilin
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀ z
  have hB_nondeg : B.Nondegenerate :=
    CovariantDerivative.chartBilin_nondegenerate
      (GeodesicTransport.cutoff (n := 3) x₀)
      (GeodesicTransport.backgroundMetric (n := 3))
      (GeodesicTransport.backgroundMetric_pos (n := 3)) g.inner
      (fun y u hu => g.inner_pos y (v := u) hu) x₀
      (GeodesicTransport.cutoff_nonneg (n := 3) x₀)
      (GeodesicTransport.cutoff_le_one (n := 3) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := 3) x₀) z
  apply (LinearEquiv.injective (LinearMap.BilinForm.toDual B hB_nondeg))
  ext b
  have hχz : GeodesicTransport.cutoff (n := 3) x₀ z = 1 := hχone.self_of_nhds
  have hlow :=
    chartCurvatureOf_chartChristoffelField_unit_orthogonal_lowered_zone
      (g := g) hcurv (x₀ := x₀) (z := z) hz hχone
      (v := v) (J := J) hunit horth b
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def]
  change
    CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀ z
        (chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z v J v) b =
      CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀ z (-J) b
  rw [GeodesicTransport.blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) hχz]
  simpa using hlow

/--
Covariant coordinate Jacobi oscillator at a cutoff-one chart point.  The
coordinate covariant second derivative of a unit transverse Jacobi variation is
`-J`.
-/
theorem coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J K : E3)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ z v v = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0) :
    coordinateCovariantJacobiSecond
        (GeodesicTransport.chartChristoffelField g x₀) z v J K = -J := by
  rw [coordinateCovariantJacobiSecond_eq_chartCurvatureOf
    (Γ := GeodesicTransport.chartChristoffelField g x₀)
    (z := z) (v := v) (J := J) (K := K)
    (chartChristoffelField_symm (g := g) (x₀ := x₀) z)
    (chartChristoffelField_fderiv_symm (g := g) (x₀ := x₀) z v J)]
  exact chartCurvatureOf_chartChristoffelField_unit_orthogonal_zone
    (g := g) hcurv (x₀ := x₀) (z := z) hz hχone
    (v := v) (J := J) hunit horth

/--
Pointwise interval form of the covariant Jacobi oscillator for a chart
geodesic/linearized state.
-/
theorem coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t : ℝ}
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0) :
    coordinateCovariantJacobiSecond
        (GeodesicTransport.chartChristoffelField g x₀)
        (γ t).1 (γ t).2 (Ψ t).1 (Ψ t).2 = -(Ψ t).1 := by
  exact coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_zone
    (g := g) hcurv (x₀ := x₀) (z := (γ t).1) htarget hχone
    (v := (γ t).2) (J := (Ψ t).1) (K := (Ψ t).2) hunit horth

/--
Sine formula for the position component of a first-order harmonic Jacobi state
on a Picard-Lindelöf interval.
-/
theorem jacobi_position_eq_sin_smul_on_Icc
    {tmin tmax : ℝ} (w : E3) (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E3 × E3 => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩ ((0 : E3), w) a r L K)
    {Ψ : ℝ → E3 × E3}
    (hΨ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ t)) (Icc tmin tmax) t)
    (hΨmem : ∀ t ∈ Icc tmin tmax, Ψ t ∈ closedBall ((0 : E3), w) a)
    (hsinmem : ∀ t ∈ Icc tmin tmax, jacobiSinState w t ∈ closedBall ((0 : E3), w) a)
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    (Ψ t).1 = Real.sin t • w := by
  have heq :=
    jacobiSinState_uniqueOn_Icc
      (w := w) (tmin := tmin) (tmax := tmax) hzero
      (hpl := hpl) (Ψ := Ψ) hΨ hΨmem hsinmem hΨ0
  have ht_eq := heq ht
  exact congrArg Prod.fst ht_eq

namespace GeodesicTransport

omit [T2Space M] in
/--
Orthogonality propagation converted from the blended geodesic metric to the
transported chart metric at a cutoff-one time.
-/
theorem chart_initialVelocity_integrated_transverse_gauss_orthogonal_chartMetric
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {α : E3 × E3 → ℝ → E3 × E3} {z₀ v w : E3} {Ψ : ℝ → E3 × E3}
    {a b t : ℝ}
    (hbase : ∀ τ ∈ Ioo a b,
      HasDerivAt (α (z₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (z₀, v) τ)) τ)
    (hΨ : ∀ τ ∈ Ioo a b,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α (z₀, v)) τ (Ψ τ)) τ)
    (hflow : ∀ τ ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => α (z₀, v + s • w) τ) (Ψ τ) 0)
    (hspeed_const : ∀ τ ∈ Ioo a b,
      (fun s : ℝ =>
        chartGeodesicMetric g x₀
          (α (z₀, v + s • w) τ).1
          (α (z₀, v + s • w) τ).2
          (α (z₀, v + s • w) τ).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        chartGeodesicMetric g x₀ z₀ (v + s • w) (v + s • w)))
    (hGd_base : ∀ τ ∈ Ioo a b,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (α (z₀, v) τ).1)
    (hGd_initial : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z₀)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (h0 : (0 : ℝ) ∈ Ioo a b)
    (horth : chartGeodesicMetric g x₀ z₀ v w = 0)
    (hcut : cutoff (n := 3) x₀ (α (z₀, v) t).1 = 1)
    (ht : t ∈ Ioo a b) :
    CovariantDerivative.chartMetric g.inner x₀
        (α (z₀, v) t).1 (Ψ t).1 (α (z₀, v) t).2 = 0 := by
  have hpair :=
    chart_initialVelocity_integrated_transverse_gauss_orthogonal
      (g := g) (x₀ := x₀) (α := α) (z₀ := z₀)
      (v := v) (w := w) (Ψ := Ψ) (a := a) (b := b) (t := t)
      hbase hΨ hflow hspeed_const hGd_base hGd_initial
      hα0 hΨ0 h0 horth ht
  rw [← blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) hcut]
  exact hpair

end GeodesicTransport

end Poincare
