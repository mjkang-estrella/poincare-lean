import Poincare.Global.SourcePackage
import Poincare.Global.TargetPackage
import Poincare.Global.SpeedPackage

/-!
# Speed-generic Jacobi package layer

This module adds additive speed-parameterized variants of the unit-speed
Jacobi norm package.  The geometric oscillator is `D²J = -(speed ^ 2) • J`;
the scalar norm system is pinned to the corresponding
`sin (speed * t) / speed` solution.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1000000

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

section SpeedOscillator

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Speed-squared version of the Kulkarni-Nomizu contraction used by the Jacobi
oscillator: for a transverse vector, the curvature contraction lowers to
`-(speedSq • J)`.
-/
theorem chartTensorKulkarniNomizu_orthogonal_contraction_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v J a : E) (speedSq : ℝ)
    (hvv : G v v = speedSq) (hJv : G J v = 0) :
    -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : E => G p q) (fun p q : E => G p q) v J v a =
      G (-(speedSq • J)) a := by
  simp [chartTensorKulkarniNomizu, hvv, hJv, map_smul, smul_eq_mul]
  ring

/--
Lowered constant-curvature-one contraction in the cutoff-one zone at arbitrary
speed squared.
-/
theorem chartCurvatureOf_chartChristoffelField_speed_orthogonal_lowered_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J : E3) (speedSq : ℝ)
    (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speedSq)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0)
    (b : E3) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀) z v J v) b =
      CovariantDerivative.chartMetric g.inner x₀ z (-(speedSq • J)) b := by
  have hzone :=
    ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone
      (g := g) hcurv (x₀ := x₀) (z := z) hz hχone v J v b
  have hcontraction :=
    chartTensorKulkarniNomizu_orthogonal_contraction_smul
      (G := CovariantDerivative.chartMetric g.inner x₀ z)
      (v := v) (J := J) (a := b) (speedSq := speedSq) hspeed horth
  exact hzone.trans hcontraction

/--
Vector form of the cutoff-one constant-curvature contraction at arbitrary
speed squared: `R(v,J)v = -(speedSq • J)` for transverse `J`.
-/
theorem chartCurvatureOf_chartChristoffelField_speed_orthogonal_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J : E3) (speedSq : ℝ)
    (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speedSq)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z v J v =
      -(speedSq • J) := by
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
    chartCurvatureOf_chartChristoffelField_speed_orthogonal_lowered_zone
      (g := g) hcurv (x₀ := x₀) (z := z) hz hχone
      (v := v) (J := J) (speedSq := speedSq) hspeed horth b
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def]
  change
    CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀ z
        (chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z v J v) b =
      CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := 3) x₀)
        (GeodesicTransport.backgroundMetric (n := 3)) g.inner x₀ z
        (-(speedSq • J)) b
  rw [GeodesicTransport.blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) hχz]
  simpa using hlow

/--
Covariant coordinate Jacobi oscillator at a cutoff-one chart point with
arbitrary speed squared.
-/
theorem coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_zone
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (v J K : E3) (speedSq : ℝ)
    (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speedSq)
    (horth : CovariantDerivative.chartMetric g.inner x₀ z J v = 0) :
    coordinateCovariantJacobiSecond
        (GeodesicTransport.chartChristoffelField g x₀) z v J K =
      -(speedSq • J) := by
  rw [coordinateCovariantJacobiSecond_eq_chartCurvatureOf
    (Γ := GeodesicTransport.chartChristoffelField g x₀)
    (z := z) (v := v) (J := J) (K := K)
    (chartChristoffelField_symm (g := g) (x₀ := x₀) z)
    (chartChristoffelField_fderiv_symm (g := g) (x₀ := x₀) z v J)]
  exact chartCurvatureOf_chartChristoffelField_speed_orthogonal_zone
    (g := g) hcurv (x₀ := x₀) (z := z) hz hχone
    (v := v) (J := J) (speedSq := speedSq) hspeed horth

/--
Pointwise interval form of the speed-squared covariant Jacobi oscillator for a
chart geodesic/linearized state.
-/
theorem coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_at_state
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t speed : ℝ}
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hspeed :
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 =
        speed ^ 2)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0) :
    coordinateCovariantJacobiSecond
        (GeodesicTransport.chartChristoffelField g x₀)
        (γ t).1 (γ t).2 (Ψ t).1 (Ψ t).2 =
      -(speed ^ 2 • (Ψ t).1) := by
  exact coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_zone
    (g := g) hcurv (x₀ := x₀) (z := (γ t).1) htarget hχone
    (v := (γ t).2) (J := (Ψ t).1) (K := (Ψ t).2)
    (speedSq := speed ^ 2) hspeed horth

end SpeedOscillator

namespace JacobiNormSystem

section SpeedNormSystem

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

open GeodesicTransport

omit [T2Space M] in
/-- The second scalar equation under `D²J = -(speed ^ 2) J`. -/
theorem normB_hasDerivAt_of_speed_oscillator
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z J D : ℝ → E} {t speed : ℝ} {zdot : E}
    (hz : HasDerivAt z zdot t)
    (hJ : HasDerivAt J
      (D t - (chartChristoffelField g x₀ (z t)) zdot (J t)) t)
    (hD : HasDerivAt D
      ((-(speed ^ 2 • J t)) -
        (chartChristoffelField g x₀ (z t)) zdot (D t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt (normB g x₀ z J D)
      (normC g x₀ z D t - speed ^ 2 * normA g x₀ z J t) t := by
  have h :=
    chart_metric_pairing_hasDerivAt_covariant
      (g := g) (x₀ := x₀) (zcurve := z) (X := J) (Y := D)
      (t := t) (zdot := zdot) (Xcov := D t) (Ycov := -(speed ^ 2 • J t))
      hz hJ hD hGd
  have h' :
      HasDerivAt (normB g x₀ z J D)
        (chartGeodesicMetric g x₀ (z t) (D t) (D t) +
          chartGeodesicMetric g x₀ (z t) (J t) (-(speed ^ 2 • J t))) t := by
    simpa [normB] using h
  convert h' using 1
  dsimp [normA, normC]
  simp only [map_neg, map_smul, smul_eq_mul]
  ring

omit [T2Space M] in
/-- The third scalar equation under `D²J = -(speed ^ 2) J`. -/
theorem normC_hasDerivAt_of_speed_oscillator
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z J D : ℝ → E} {t speed : ℝ} {zdot : E}
    (hz : HasDerivAt z zdot t)
    (hD : HasDerivAt D
      ((-(speed ^ 2 • J t)) -
        (chartChristoffelField g x₀ (z t)) zdot (D t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt (normC g x₀ z D)
      (-2 * speed ^ 2 * normB g x₀ z J D t) t := by
  have h :=
    chart_metric_pairing_hasDerivAt_covariant
      (g := g) (x₀ := x₀) (zcurve := z) (X := D) (Y := D)
      (t := t) (zdot := zdot)
      (Xcov := -(speed ^ 2 • J t)) (Ycov := -(speed ^ 2 • J t))
      hz hD hD hGd
  have h' :
      HasDerivAt (normC g x₀ z D)
        (chartGeodesicMetric g x₀ (z t) (-(speed ^ 2 • J t)) (D t) +
          chartGeodesicMetric g x₀ (z t) (D t) (-(speed ^ 2 • J t))) t := by
    simpa [normC] using h
  convert h' using 1
  dsimp [normB]
  simp only [map_neg, map_smul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [chartGeodesicMetric_symm (g := g) (x₀ := x₀) (z t) (D t) (J t)]
  ring_nf

/-- The scalar multiplier in `|J(t)|²` for `J'' = -(speed ^ 2)J`. -/
def speedPinnedScale (speed t : ℝ) : ℝ :=
  Real.sin (speed * t) ^ 2 * (speed ^ 2)⁻¹

/-- Speed-generic pinned model `a(t) = sin²(speed t) / speed² * q`. -/
def speedPinnedA (speed q t : ℝ) : ℝ :=
  speedPinnedScale speed t * q

/-- Speed-generic pinned model `b(t) = sin(speed t) cos(speed t) / speed * q`. -/
def speedPinnedB (speed q t : ℝ) : ℝ :=
  (Real.sin (speed * t) * Real.cos (speed * t)) * (speed⁻¹ * q)

/-- Speed-generic pinned model `c(t) = cos²(speed t) * q`. -/
def speedPinnedC (_speed q t : ℝ) : ℝ :=
  Real.cos (_speed * t) ^ 2 * q

@[simp]
theorem speedPinnedA_zero (speed q : ℝ) : speedPinnedA speed q 0 = 0 := by
  simp [speedPinnedA, speedPinnedScale]

@[simp]
theorem speedPinnedB_zero (speed q : ℝ) : speedPinnedB speed q 0 = 0 := by
  simp [speedPinnedB]

@[simp]
theorem speedPinnedC_zero (speed q : ℝ) : speedPinnedC speed q 0 = q := by
  simp [speedPinnedC]

private theorem speed_mul_arg_hasDerivAt (speed t : ℝ) :
    HasDerivAt (fun τ : ℝ => speed * τ) speed t := by
  simpa [mul_comm] using (hasDerivAt_const_mul (x := t) speed)

/-- Pinning check for the speed-generic `a` scalar. -/
theorem speedPinnedA_hasDerivAt {speed : ℝ} (hspeed : speed ≠ 0) (q t : ℝ) :
    HasDerivAt (speedPinnedA speed q) (2 * speedPinnedB speed q t) t := by
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin (speed * τ))
      (Real.cos (speed * t) * speed) t :=
    (Real.hasDerivAt_sin (speed * t)).comp t (speed_mul_arg_hasDerivAt speed t)
  have hprod := (hsin.mul hsin).mul_const ((speed ^ 2)⁻¹ * q)
  convert hprod using 1
  · ext y
    simp [speedPinnedA, speedPinnedScale, pow_two, mul_assoc]
  · dsimp [speedPinnedB]
    field_simp [hspeed]
    ring

/-- Pinning check for the speed-generic `b` scalar. -/
theorem speedPinnedB_hasDerivAt {speed : ℝ} (hspeed : speed ≠ 0) (q t : ℝ) :
    HasDerivAt (speedPinnedB speed q)
      (speedPinnedC speed q t - speed ^ 2 * speedPinnedA speed q t) t := by
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin (speed * τ))
      (Real.cos (speed * t) * speed) t :=
    (Real.hasDerivAt_sin (speed * t)).comp t (speed_mul_arg_hasDerivAt speed t)
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos (speed * τ))
      (-Real.sin (speed * t) * speed) t :=
    (Real.hasDerivAt_cos (speed * t)).comp t (speed_mul_arg_hasDerivAt speed t)
  have hprod := (hsin.mul hcos).mul_const (speed⁻¹ * q)
  convert hprod using 1
  dsimp [speedPinnedA, speedPinnedScale, speedPinnedC]
  field_simp [hspeed]
  ring

/-- Pinning check for the speed-generic `c` scalar. -/
theorem speedPinnedC_hasDerivAt {speed : ℝ} (hspeed : speed ≠ 0) (q t : ℝ) :
    HasDerivAt (speedPinnedC speed q) (-2 * speed ^ 2 * speedPinnedB speed q t) t := by
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos (speed * τ))
      (-Real.sin (speed * t) * speed) t :=
    (Real.hasDerivAt_cos (speed * t)).comp t (speed_mul_arg_hasDerivAt speed t)
  have hprod := (hcos.mul hcos).mul_const q
  convert hprod using 1
  · ext y
    simp [speedPinnedC, pow_two]
  · dsimp [speedPinnedB]
    field_simp [hspeed]
    ring

end SpeedNormSystem

end JacobiNormSystem

namespace JacobiNormClose

section SpeedClose

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
The chart-linearized state feeds the speed-generic Jacobi norm system after
the covariant correction `D = K + Γ(z)(z',J)`.
-/
theorem chart_linearized_state_feeds_speed_norm_system_at
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t speed : ℝ}
    (hγ : HasDerivAt γ
      (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hΨ : HasDerivAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) γ t (Ψ t)) t)
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed :
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 =
        speed ^ 2)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ t).1) :
    let z : ℝ → E3 := fun τ => (γ τ).1
    let J : ℝ → E3 := fun τ => (Ψ τ).1
    let D : ℝ → E3 :=
      fun τ => (Ψ τ).2 +
        (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1
    HasDerivAt (JacobiNormSystem.normA g x₀ z J)
        (2 * JacobiNormSystem.normB g x₀ z J D t) t ∧
      HasDerivAt (JacobiNormSystem.normB g x₀ z J D)
        (JacobiNormSystem.normC g x₀ z D t -
          speed ^ 2 * JacobiNormSystem.normA g x₀ z J t) t ∧
      HasDerivAt (JacobiNormSystem.normC g x₀ z D)
        (-2 * speed ^ 2 * JacobiNormSystem.normB g x₀ z J D t) t := by
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := chartChristoffelField g x₀
  let z : ℝ → E3 := fun τ => (γ τ).1
  let V : ℝ → E3 := fun τ => (γ τ).2
  let J : ℝ → E3 := fun τ => (Ψ τ).1
  let K : ℝ → E3 := fun τ => (Ψ τ).2
  let D : ℝ → E3 := fun τ => K τ + Γ (z τ) (V τ) (J τ)
  have hz : HasDerivAt z (V t) t := by
    simpa [z, V, Γ] using
      geodesic_position_hasDerivAt
        (Γ := Γ) (γ := γ) (t := t) hγ
  have hV : HasDerivAt V (-(Γ (z t)) (V t) (V t)) t := by
    simpa [z, V, Γ] using
      geodesic_velocity_hasDerivAt
        (Γ := Γ) (γ := γ) (t := t) hγ
  have hJcoord : HasDerivAt J (K t) t := by
    simpa [J, K, Γ] using
      chart_linearized_fst_hasDerivAt
        (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ) hΨ
  have hΓd : DifferentiableAt ℝ Γ (z t) := by
    simpa [Γ, z] using
      (chartChristoffelField_contDiffAt_base (g := g) (x₀ := x₀) (z := (γ t).1)
        |>.differentiableAt (by norm_num))
  have hlinearized_eq :
      linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t) =
        coordinateJacobiFlowOperator Γ (γ t) (Ψ t) := by
    have hoperator :
        linearizedGeodesicFlowOperator Γ (γ t) =
          coordinateJacobiFlowOperator Γ (γ t) := by
      simpa [Γ, z] using
        linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator
          (Γ := Γ) (base := γ t) hΓd
    simp [linearizedGeodesicFlowFieldAlong, hoperator]
  have hKcoord :
      HasDerivAt K
        (coordinateJacobiAcceleration Γ (z t, V t) (J t, K t)) t := by
    have hsnd := hΨ.hasFDerivAt.snd.hasDerivAt
    have hsnd_eq :
        (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t)).2 =
          coordinateJacobiAcceleration Γ (z t, V t) (J t, K t) := by
      rw [hlinearized_eq]
      simp [z, V, J, K]
    have hsnd' :
        HasDerivAt K
          (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t)).2 t := by
      simpa [K, Γ] using hsnd
    convert hsnd' using 1
    exact hsnd_eq.symm
  have hΓpath :
      HasDerivAt (fun τ : ℝ => Γ (z τ)) ((fderiv ℝ Γ (z t)) (V t)) t := by
    have hcomp :
        HasDerivAt (Γ ∘ z) ((fderiv ℝ Γ (z t)) (V t)) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E3)
        (f := z) (f' := V t) (x := t)
        (l := Γ) (l' := fderiv ℝ Γ (z t))
        hΓd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hΓV :
      HasDerivAt (fun τ : ℝ => Γ (z τ) (V τ))
        (((fderiv ℝ Γ (z t)) (V t)) (V t) +
          Γ (z t) (-(Γ (z t)) (V t) (V t))) t := by
    simpa using hΓpath.clm_apply hV
  have hΓVJ :
      HasDerivAt (fun τ : ℝ => Γ (z τ) (V τ) (J τ))
        ((((fderiv ℝ Γ (z t)) (V t)) (V t) +
            Γ (z t) (-(Γ (z t)) (V t) (V t))) (J t) +
          Γ (z t) (V t) (K t)) t := by
    simpa using hΓV.clm_apply hJcoord
  have hDraw :
      HasDerivAt D
        (coordinateJacobiAcceleration Γ (z t, V t) (J t, K t) +
          ((((fderiv ℝ Γ (z t)) (V t)) (V t) +
              Γ (z t) (-(Γ (z t)) (V t) (V t))) (J t) +
            Γ (z t) (V t) (K t))) t := by
    simpa [D] using hKcoord.add hΓVJ
  have hDcov :
      HasDerivAt D
        (coordinateCovariantJacobiSecond Γ (z t) (V t) (J t) (K t) -
          Γ (z t) (V t) (D t)) t := by
    convert hDraw using 1
    simp [D, coordinateCovariantJacobiSecond, map_add, map_neg]
    abel
  have hosc :
      coordinateCovariantJacobiSecond Γ (z t) (V t) (J t) (K t) =
        -(speed ^ 2 • J t) := by
    simpa [Γ, z, V, J, K] using
      coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_at_state
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := t)
        (speed := speed) htarget hχone hspeed horth
  have hD :
      HasDerivAt D ((-(speed ^ 2 • J t)) - Γ (z t) (V t) (D t)) t := by
    simpa [hosc] using hDcov
  have hJ :
      HasDerivAt J (D t - Γ (z t) (V t) (J t)) t := by
    convert hJcoord using 1
    simp [D]
  have hA :
      HasDerivAt (JacobiNormSystem.normA g x₀ z J)
        (2 * JacobiNormSystem.normB g x₀ z J D t) t :=
    JacobiNormSystem.normA_hasDerivAt
      (g := g) (x₀ := x₀) (z := z) (J := J) (D := D) (t := t)
      (zdot := V t) hz hJ (by simpa [z] using hGd)
  have hB :
      HasDerivAt (JacobiNormSystem.normB g x₀ z J D)
        (JacobiNormSystem.normC g x₀ z D t -
          speed ^ 2 * JacobiNormSystem.normA g x₀ z J t) t :=
    JacobiNormSystem.normB_hasDerivAt_of_speed_oscillator
      (g := g) (x₀ := x₀) (z := z) (J := J) (D := D) (t := t)
      (speed := speed) (zdot := V t) hz hJ hD (by simpa [z] using hGd)
  have hC :
      HasDerivAt (JacobiNormSystem.normC g x₀ z D)
        (-2 * speed ^ 2 * JacobiNormSystem.normB g x₀ z J D t) t :=
    JacobiNormSystem.normC_hasDerivAt_of_speed_oscillator
      (g := g) (x₀ := x₀) (z := z) (J := J) (D := D) (t := t)
      (speed := speed) (zdot := V t) hz hD (by simpa [z] using hGd)
  exact ⟨hA, hB, hC⟩

end SpeedClose

end JacobiNormClose

namespace JacobiIntegrated

/--
The speed-generic closed Jacobi norm system integrates to the corresponding
`sin (speed * t)` pinned solution on the Picard-Lindelöf interval.
-/
theorem closed_speed_norm_system_eq_pinned_on_Icc
    {tmin tmax speed q : ℝ} (hspeed : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    {a b c : ℝ → ℝ}
    (ha : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt a (2 * b s) (Icc tmin tmax) s)
    (hb : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt b (c s - speed ^ 2 * a s) (Icc tmin tmax) s)
    (hc : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt c (-2 * speed ^ 2 * b s) (Icc tmin tmax) s)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (a s, b s, c s) ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed q s,
        JacobiNormSystem.speedPinnedB speed q s,
        JacobiNormSystem.speedPinnedC speed q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    a t = JacobiNormSystem.speedPinnedA speed q t ∧
      b t = JacobiNormSystem.speedPinnedB speed q t ∧
      c t = JacobiNormSystem.speedPinnedC speed q t := by
  let state : ℝ → ℝ × ℝ × ℝ := fun s => (a s, b s, c s)
  let pinned : ℝ → ℝ × ℝ × ℝ := fun s =>
    (JacobiNormSystem.speedPinnedA speed q s,
      JacobiNormSystem.speedPinnedB speed q s,
      JacobiNormSystem.speedPinnedC speed q s)
  have hstate : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt state (Aop (state s)) (Icc tmin tmax) s := by
    intro s hs
    have hprod := (ha s hs).prodMk ((hb s hs).prodMk (hc s hs))
    simpa [state, hAop] using hprod
  have hpinned : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt pinned (Aop (pinned s)) (Icc tmin tmax) s := by
    intro s _hs
    have hA : HasDerivWithinAt (JacobiNormSystem.speedPinnedA speed q)
        (2 * JacobiNormSystem.speedPinnedB speed q s) (Icc tmin tmax) s :=
      (JacobiNormSystem.speedPinnedA_hasDerivAt hspeed q s).hasDerivWithinAt
    have hB : HasDerivWithinAt (JacobiNormSystem.speedPinnedB speed q)
        (JacobiNormSystem.speedPinnedC speed q s -
          speed ^ 2 * JacobiNormSystem.speedPinnedA speed q s)
        (Icc tmin tmax) s :=
      (JacobiNormSystem.speedPinnedB_hasDerivAt hspeed q s).hasDerivWithinAt
    have hC : HasDerivWithinAt (JacobiNormSystem.speedPinnedC speed q)
        (-2 * speed ^ 2 * JacobiNormSystem.speedPinnedB speed q s)
        (Icc tmin tmax) s :=
      (JacobiNormSystem.speedPinnedC_hasDerivAt hspeed q s).hasDerivWithinAt
    have hprod := hA.prodMk (hB.prodMk hC)
    simpa [pinned, hAop] using hprod
  have hstatemem : ∀ s ∈ Icc tmin tmax,
      state s ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [state] using hmem s hs
  have hpinnedmem' : ∀ s ∈ Icc tmin tmax,
      pinned s ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [pinned] using hpinnedmem s hs
  have hinit : state 0 = pinned 0 := by
    simp [state, pinned, ha0, hb0, hc0]
  have heq : EqOn state pinned (Icc tmin tmax) :=
    linearODE_solution_uniqueOn_Icc
      (A := fun _ : ℝ => Aop)
      (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : ℝ), (0 : ℝ), q))
      hpl hstate hstatemem hpinned hpinnedmem' hinit
  have htstate := heq ht
  constructor
  · exact congrArg Prod.fst htstate
  constructor
  · exact congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) htstate
  · exact congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) htstate

end JacobiIntegrated

namespace CartanIsometryTheorem

section SpeedAssembly

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Interval assembly of the actual corrected Jacobi scalars at arbitrary constant
speed.
-/
theorem actual_jacobi_norms_eq_speed_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3}
    {tmin tmax speed q : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        speed ^ 2)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed q s,
        JacobiNormSystem.speedPinnedB speed q s,
        JacobiNormSystem.speedPinnedC speed q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA g x₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t = JacobiNormSystem.speedPinnedA speed q t ∧
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) t =
        JacobiNormSystem.speedPinnedB speed q t ∧
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) t =
        JacobiNormSystem.speedPinnedC speed q t := by
  let z : ℝ → E3 := fun τ => (γ τ).1
  let J : ℝ → E3 := fun τ => (Ψ τ).1
  let D : ℝ → E3 :=
    fun τ => (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1
  let a : ℝ → ℝ := JacobiNormSystem.normA g x₀ z J
  let b : ℝ → ℝ := JacobiNormSystem.normB g x₀ z J D
  let c : ℝ → ℝ := JacobiNormSystem.normC g x₀ z D
  have ha : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt a (2 * b s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_speed_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (speed := speed)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hspeed s hs) (horth s hs) (hGd s hs)
    simpa [a, b, z, J, D] using hfeed.1.hasDerivWithinAt
  have hb : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt b (c s - speed ^ 2 * a s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_speed_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (speed := speed)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hspeed s hs) (horth s hs) (hGd s hs)
    simpa [a, b, c, z, J, D] using hfeed.2.1.hasDerivWithinAt
  have hc : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt c (-2 * speed ^ 2 * b s) (Icc tmin tmax) s := by
    intro s hs
    have hfeed :=
      JacobiNormClose.chart_linearized_state_feeds_speed_norm_system_at
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := s)
        (speed := speed)
        (hγ s hs) (hΨ s hs) (htarget s hs) (hχone s hs)
        (hspeed s hs) (horth s hs) (hGd s hs)
    simpa [b, c, z, J, D] using hfeed.2.2.hasDerivWithinAt
  have hmem' : ∀ s ∈ Icc tmin tmax,
      (a s, b s, c s) ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [a, b, c, z, J, D] using hmem s hs
  have ha0' : a 0 = 0 := by
    simpa [a, z, J] using ha0
  have hb0' : b 0 = 0 := by
    simpa [b, z, J, D] using hb0
  have hc0' : c 0 = q := by
    simpa [c, z, D] using hc0
  have hpinned :=
    JacobiIntegrated.closed_speed_norm_system_eq_pinned_on_Icc
      (speed := speed) (tmin := tmin) (tmax := tmax) (q := q) hspeed_ne hzero Aop
      (hpl := hpl) hAop
      (a := a) (b := b) (c := c)
      ha hb hc hmem' hpinnedmem ha0' hb0' hc0' ht
  simpa [a, b, c, z, J, D] using hpinned

end SpeedAssembly

end CartanIsometryTheorem

namespace CascadePinned

section ScalarPinned

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/-- Polarized cutoff-one endpoint pairing with an arbitrary scalar factor. -/
theorem actual_jacobi_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ Ψw Ψw' Ψadd : ℝ → E3 × E3}
    {w w' : E3} {tmin tmax S : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀) (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E3), w + w') a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨw' : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw'
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψw' s))
        (Icc tmin tmax) s)
    (hΨadd : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψadd s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ s ∈ Icc tmin tmax,
      Ψadd s ∈ closedBall ((0 : E3), w + w') a)
    (hmem_sum : ∀ s ∈ Icc tmin tmax,
      Ψw s + Ψw' s ∈ closedBall ((0 : E3), w + w') a)
    (hΨw0 : Ψw 0 = ((0 : E3), w))
    (hΨw'0 : Ψw' 0 = ((0 : E3), w'))
    (hΨadd0 : Ψadd 0 = ((0 : E3), w + w'))
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    (hquad_w :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w)
    (hquad_w' :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw' τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w')
    (hquad_add :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψadd τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w')) :
    chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw' t).1 =
      S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w' := by
  let A : ℝ → (E3 × E3) →L[ℝ] (E3 × E3) :=
    fun s => linearizedGeodesicFlowOperator
      (chartChristoffelField g x₀) (γ s)
  have hder_add : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd (A s (Ψadd s)) (Icc tmin tmax) s := by
    intro s hs
    simpa [A, linearizedGeodesicFlowFieldAlong] using hΨadd s hs
  have hder_sum : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => Ψw τ + Ψw' τ)
        (A s ((fun τ : ℝ => Ψw τ + Ψw' τ) s)) (Icc tmin tmax) s := by
    intro s hs
    have hder := (hΨw s hs).add (hΨw' s hs)
    simpa [A, linearizedGeodesicFlowFieldAlong] using hder
  have hinitial :
      Ψadd (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
        (fun τ : ℝ => Ψw τ + Ψw' τ)
          (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
    change Ψadd 0 = Ψw 0 + Ψw' 0
    rw [hΨadd0, hΨw0, hΨw'0]
    simp
  have hEqOn :
      EqOn Ψadd (fun τ : ℝ => Ψw τ + Ψw' τ) (Icc tmin tmax) :=
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : E3), w + w')) (a := a) (r := r) (L := L) (K := K)
      hpl hder_add hmem_add hder_sum hmem_sum hinitial
  have hJadd : (Ψadd t).1 = (Ψw t).1 + (Ψw' t).1 := by
    have hstate := hEqOn ht
    exact congrArg Prod.fst hstate
  have hww :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w := by
    simpa [JacobiNormSystem.normA] using hquad_w
  have hww' :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw' t).1 (Ψw' t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w' := by
    simpa [JacobiNormSystem.normA] using hquad_w'
  have hadd :
      chartGeodesicMetric g x₀ (γ t).1 (Ψadd t).1 (Ψadd t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w') := by
    simpa [JacobiNormSystem.normA] using hquad_add
  exact
    JacobiNormSystem.polarize_endpoint_pairing_of_quadratic
      (B := chartGeodesicMetric g x₀ (γ t).1)
      (A := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀))
      (S := S)
      (fun u v => chartGeodesicMetric_symm (g := g) (x₀ := x₀) (γ t).1 u v)
      (fun u v => chartGeodesicMetric_symm
        (g := g) (x₀ := x₀) (extChartAt I3 x₀ x₀) u v)
      (w := w) (w' := w') (Jw := (Ψw t).1) (Jw' := (Ψw' t).1)
      (Jadd := (Ψadd t).1) hJadd hww hww' hadd

/-- Endpoint pinned formula for a rescaled hosted family with scalar factor `S`. -/
theorem hosted_rescaled_endpoint_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax S : ℝ}
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) a r L K)
    (hΨder : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) a)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) a)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hcutT : cutoff (n := 3) x₀ (γ T).1 = 1)
    (hendpoint :
      (γ T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (hquad : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        S * CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  intro w w'
  have hΨadd0 :
      Ψ (w + w') 0 = ((0 : E3), T⁻¹ • w + T⁻¹ • w') := by
    rw [hΨ0 (w + w')]
    simp [smul_add]
  have hPairBlended :
      chartGeodesicMetric g x₀ (γ T).1 (Ψ w T).1 (Ψ w' T).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w') :=
    actual_jacobi_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ)
      (Ψw := Ψ w) (Ψw' := Ψ w') (Ψadd := Ψ (w + w'))
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (tmin := tmin) (tmax := tmax) (S := S) hzero
      (a := a) (r := r) (L := L) (K := K)
      (hpl := by simpa [smul_add] using hpl w w')
      (hΨw := hΨder w) (hΨw' := hΨder w') (hΨadd := hΨder (w + w'))
      (hmem_add := by simpa [smul_add] using hmem_add w w')
      (hmem_sum := by simpa [smul_add] using hmem_sum w w')
      (hΨw0 := hΨ0 w) (hΨw'0 := hΨ0 w') (hΨadd0 := hΨadd0)
      (ht := hT) (hquad_w := hquad w) (hquad_w' := hquad w')
      (hquad_add := by simpa [smul_add] using hquad (w + w'))
  have hPairChart :
      CovariantDerivative.chartMetric g.inner x₀ (γ T).1
          (Ψ w T).1 (Ψ w' T).1 =
        S * CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
    chartMetric_pairing_eq_pinned_of_blended_pairing
      (g := g) (x₀ := x₀) (z := (γ T).1)
      (J := (Ψ w T).1) (J' := (Ψ w' T).1)
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := S) hcutT hPairBlended
  simpa [hendpoint] using hPairChart

end ScalarPinned

end CascadePinned

namespace SourcePackage

section SpeedSource

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/-- Source cutoff-one Jacobi norm theorem at arbitrary constant speed. -/
theorem source_normA_eq_speed_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3}
    {tmin tmax speed q : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed q s,
        JacobiNormSystem.speedPinnedB speed q s,
        JacobiNormSystem.speedPinnedC speed q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA g x₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t =
      JacobiNormSystem.speedPinnedA speed q t := by
  exact
    (CartanIsometryTheorem.actual_jacobi_norms_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (tmin := tmin) (tmax := tmax) (speed := speed) (q := q)
      hspeed_ne hzero Aop
      (hpl := hpl) hAop hγ hΨ htarget hχone hspeed horth hGd
      hmem hpinnedmem ha0 hb0 hc0 ht).1

/-- Family-level source quadratic package at arbitrary constant speed. -/
theorem source_hosted_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w) := by
  intro w
  exact
    source_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax) (speed := speed)
      (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hspeed_ne hzero Aop (hpl w) hAop hγ (hΨ w) htarget hχone hspeed
      (horth w) hGd (hmem w) (hpinnedmem w) (ha0 w) (hb0 w) (hc0 w) hT

/-- Speed-generic source endpoint formula for the hosted rescaled source cascade. -/
theorem source_hosted_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have hcutT : cutoff (n := 3) x₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ w : E3,
        JacobiNormSystem.normA g x₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ w τ).1) T =
          JacobiNormSystem.speedPinnedScale speed T *
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w) :=
    source_hosted_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      hspeed_ne hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  exact
    CascadePinned.hosted_rescaled_endpoint_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax)
      (S := JacobiNormSystem.speedPinnedScale speed T)
      hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT hcutT
      hendpoint hquad

/--
Transverse-only source quadratic package at arbitrary constant speed.

The older family theorem asks for endpoint orthogonality for every input
direction.  The norm-system proof only uses that hypothesis for the specific
input under consideration, so this variant restricts it to directions
orthogonal to the endpoint radial vector in the anchor chart metric.
-/
theorem source_hosted_transverse_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨ : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E3, CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w) := by
  intro w hw
  exact
    source_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax) (speed := speed)
      (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hspeed_ne hzero Aop (hpl w) hAop hγ (hΨ w) htarget hχone hspeed
      (horth w hw) hGd (hmem w) (hpinnedmem w) (ha0 w) (hb0 w) (hc0 w) hT

/--
Speed-generic source endpoint formula for transverse hosted inputs.

This is the non-all-direction replacement for the endpoint feed: the conclusion
is only for pairs of inputs orthogonal to the radial endpoint vector in the
source anchor chart metric.
-/
theorem source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  intro w w' hw hw'
  have hcutT : cutoff (n := 3) x₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ z : E3, CartanMap.sourceAnchorChartMetric g x₀ v z = 0 →
        JacobiNormSystem.normA g x₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ z τ).1) T =
          JacobiNormSystem.speedPinnedScale speed T *
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • z) (T⁻¹ • z) :=
    source_hosted_transverse_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hwadd : CartanMap.sourceAnchorChartMetric g x₀ v (w + w') = 0 := by
    simp [hw, hw']
  have hΨadd0 :
      Ψ (w + w') 0 = ((0 : E3), T⁻¹ • w + T⁻¹ • w') := by
    rw [hΨ0 (w + w')]
    simp [smul_add]
  have hPairBlended :
      chartGeodesicMetric g x₀ (γ T).1 (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w') :=
    CascadePinned.actual_jacobi_pairing_eq_scalar_of_quadratic_and_linearized_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ)
      (Ψw := Ψ w) (Ψw' := Ψ w') (Ψadd := Ψ (w + w'))
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (tmin := tmin) (tmax := tmax)
      (S := JacobiNormSystem.speedPinnedScale speed T) hzero
      (a := aLin) (r := rLin) (L := LipLin) (K := KLin)
      (hpl := by simpa [smul_add] using hplLinear w w')
      (hΨw := hΨderWithin w) (hΨw' := hΨderWithin w')
      (hΨadd := hΨderWithin (w + w'))
      (hmem_add := by simpa [smul_add] using hmem_add w w')
      (hmem_sum := by simpa [smul_add] using hmem_sum w w')
      (hΨw0 := hΨ0 w) (hΨw'0 := hΨ0 w') (hΨadd0 := hΨadd0)
      (ht := hT) (hquad_w := hquad w hw) (hquad_w' := hquad w' hw')
      (hquad_add := by simpa [smul_add] using hquad (w + w') hwadd)
  have hPairChart :
      CovariantDerivative.chartMetric g.inner x₀ (γ T).1
          (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
    CascadePinned.chartMetric_pairing_eq_pinned_of_blended_pairing
      (g := g) (x₀ := x₀) (z := (γ T).1)
      (J := (Ψ w T).1) (J' := (Ψ w' T).1)
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := JacobiNormSystem.speedPinnedScale speed T) hcutT hPairBlended
  simpa [hendpoint] using hPairChart

end SpeedSource

end SourcePackage

namespace TargetPackage

section SpeedTarget

open GeodesicTransport

/-- Target cutoff-one Jacobi norm theorem at arbitrary constant speed. -/
theorem target_normA_eq_speed_pinned_on_cutoff_one_Icc
    (p₀ : RoundSphere3) {γ Ψ : ℝ → E3 × E3}
    {tmin tmax speed q : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed q s,
        JacobiNormSystem.speedPinnedB speed q s,
        JacobiNormSystem.speedPinnedC speed q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 :
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1) 0 = 0)
    (hb0 :
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) 0 = 0)
    (hc0 :
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ τ).1) 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    JacobiNormSystem.normA roundSphereMetric3 p₀
        (fun τ : ℝ => (γ τ).1)
        (fun τ : ℝ => (Ψ τ).1) t =
      JacobiNormSystem.speedPinnedA speed q t := by
  exact
    (CartanIsometryTheorem.actual_jacobi_norms_eq_speed_pinned_on_cutoff_one_Icc
      (g := roundSphereMetric3)
      roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ)
      (tmin := tmin) (tmax := tmax) (speed := speed) (q := q)
      hspeed_ne hzero Aop
      (hpl := hpl) hAop hγ hΨ htarget hχone hspeed horth hGd
      hmem hpinnedmem ha0 hb0 hc0 ht).1

/-- Family-level target quadratic package at arbitrary constant speed. -/
theorem target_hosted_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨ : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) T =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w) :=
  SourcePackage.source_hosted_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
    (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
    (x₀ := p₀) (γ := γ) (Ψ := Ψ) hspeed_ne hzero hT Aop hpl hAop
    hγ hΨ htarget hχone hspeed horth hGd hmem hpinnedmem ha0 hb0 hc0

/-- Speed-generic target endpoint formula for the hosted rescaled target cascade. -/
theorem target_hosted_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField roundSphereMetric3 p₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
          (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have h :=
    SourcePackage.source_hosted_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
      (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT
      hendpoint Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed horth hGd
      hmemNorm hpinnedmem ha0 hb0 hc0
  intro w w'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using h w w'

/--
Speed-generic target endpoint formula for transverse hosted inputs.

This mirrors the source transverse variant, with transversality measured by the
round-sphere anchor chart metric.
-/
theorem target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField roundSphereMetric3 p₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have horthSource : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0 := by
    intro w hw
    exact horth w (by
      simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw)
  have hsource :=
    SourcePackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
      (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT
      hendpoint Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horthSource hGd hmemNorm hpinnedmem ha0 hb0 hc0
  intro w w' hw hw'
  have hws : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw
  have hw's : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w' = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using hsource w w' hws hw's

end SpeedTarget

end TargetPackage

namespace SpeedGeneric

section Feed

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Convert a source hosted-curve speed-value statement, as supplied by
`SpeedPackage`, into the constant `speed ^ 2` hypothesis consumed by the
speed-generic Jacobi package.
-/
theorem source_speed_hypothesis_of_hostedSourceSpeed_sq
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (δ : ℝ) (v : E3)
    {γ : ℝ → E3 × E3} {tmin tmax : ℝ}
    (hspeedValue : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        CartanMap.sourceAnchorChartMetric g x₀
          (CartanHomogeneity.workingVelocity δ v)
          (CartanHomogeneity.workingVelocity δ v)) :
    ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀ (γ s).1 (γ s).2 (γ s).2 =
        CartanScaleGeneric.hostedSourceSpeed g x₀ δ v ^ 2 := by
  intro s hs
  exact (hspeedValue s hs).trans
    (SpeedPackage.hostedSourceSpeed_sq g x₀ δ v).symm

/--
Target analogue of `source_speed_hypothesis_of_hostedSourceSpeed_sq` for an
aligned hosted working velocity.
-/
theorem target_speed_hypothesis_of_hostedTargetSpeed_sq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E3)
    {γ : ℝ → E3 × E3} {tmin tmax : ℝ}
    (hspeedValue : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (γ s).1 (γ s).2 (γ s).2 =
        CartanMap.targetAnchorChartMetric p₀
          (L (CartanHomogeneity.workingVelocity δ v))
          (L (CartanHomogeneity.workingVelocity δ v))) :
    ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (γ s).1 (γ s).2 (γ s).2 =
        CartanScaleGeneric.hostedTargetSpeed L δ v ^ 2 := by
  intro s hs
  exact (hspeedValue s hs).trans
    (SpeedPackage.hostedTargetSpeed_sq L δ v).symm

/-- Algebraic unscaling for the speed-generic rescaled sine factor. -/
theorem speed_rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
    {speed T : ℝ} (hspeed : speed ≠ 0) (hT : T ≠ 0) :
    (JacobiNormSystem.speedPinnedScale speed T) * (T⁻¹ * T⁻¹) =
      Real.sin (SourcePackage.normalizedRescaledAngle (speed * T)) ^ 2 := by
  have hspeedT : speed * T ≠ 0 := mul_ne_zero hspeed hT
  calc
    (JacobiNormSystem.speedPinnedScale speed T) * (T⁻¹ * T⁻¹) =
        Real.sin (speed * T) ^ 2 * ((speed * T)⁻¹ * (speed * T)⁻¹) := by
          dsimp [JacobiNormSystem.speedPinnedScale]
          field_simp [hspeed, hT]
    _ = Real.sin (SourcePackage.normalizedRescaledAngle (speed * T)) ^ 2 :=
        SourcePackage.rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle hspeedT

/--
Feed speed-generic rescaled source and target pinned formulas through the
existing endpoint-pairing bridge after bilinear unscaling.
-/
theorem hosted_endpoint_pairing_feed_of_common_speed_rescaled_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    (hspeed : speed ≠ 0) (hT : T ≠ 0)
    (hSourceRescaled :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 := by
  let θ : ℝ := SourcePackage.normalizedRescaledAngle (speed * T)
  have hScale :
      JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) =
        Real.sin θ ^ 2 := by
    simpa [θ] using
      speed_rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
        (speed := speed) (T := T) hspeed hT
  refine
    EqualityChain.hosted_endpoint_pairing_feed_of_sin_sq_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt)
      (Ts := T) (Tt := T) (θs := θ) (θt := θ)
      rfl ?_ ?_
  · intro a a'
    calc
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a') :=
          hSourceRescaled a a'
      _ = JacobiNormSystem.speedPinnedScale speed T *
          ((T⁻¹ * T⁻¹) * CartanMap.sourceAnchorChartMetric g x₀ a a') := by
          rw [UnscaledFeed.sourceAnchorChartMetric_inv_smul_inv_smul]
      _ = Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a' := by
          rw [← hScale]
          ring
  · intro a a'
    calc
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • L a) (T⁻¹ • L a') :=
          hTargetRescaled (L a) (L a')
      _ = JacobiNormSystem.speedPinnedScale speed T *
          ((T⁻¹ * T⁻¹) * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) := by
          rw [UnscaledFeed.targetAnchorChartMetric_inv_smul_inv_smul]
      _ = Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') := by
          rw [← hScale]
          ring

/--
Local-isometry consumer with common-time source and target speed-generic
rescaled endpoint feeds.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_common_speed_rescaled_anchor_pairings
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {A B : E3 ≃L[ℝ] E3}
    {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (Ψt (c • w) T).1 = c • (Ψt w T).1}
    (hA :
      (A : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls)
    (hB :
      (B : E3 →L[ℝ] E3) =
        linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult)
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E3 →L[ℝ] E3) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E3 →L[ℝ] E3) (L v))
    (u u' : E3) (hspeed : speed ≠ 0) (hT : T ≠ 0)
    (hSourceRescaled :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψs a T).1 (Ψs a' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a'))
    (hTargetRescaled :
      ∀ w w' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (Ψt w T).1 (Ψt w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (CartanLocalIsometry.cartanChartDifferential L A B u)
          (CartanLocalIsometry.cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := by
  let θ : ℝ := SourcePackage.normalizedRescaledAngle (speed * T)
  have hScale :
      JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) =
        Real.sin θ ^ 2 := by
    simpa [θ] using
      speed_rescaled_sin_sq_factor_eq_sin_sq_normalizedRescaledAngle
        (speed := speed) (T := T) hspeed hT
  refine
    EqualityChain.cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pairings
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (A := A) (B := B) (Ψs := Ψs) (Ψt := Ψt)
      (Ts := T) (Tt := T) (θs := θ) (θt := θ)
      hA hB hvsrc hsourceDeriv htargetDeriv u u' rfl ?_ ?_
  · intro a a'
    calc
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψs a T).1 (Ψs a' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • a) (T⁻¹ • a') :=
          hSourceRescaled a a'
      _ = JacobiNormSystem.speedPinnedScale speed T *
          ((T⁻¹ * T⁻¹) * CartanMap.sourceAnchorChartMetric g x₀ a a') := by
          rw [UnscaledFeed.sourceAnchorChartMetric_inv_smul_inv_smul]
      _ = Real.sin θ ^ 2 * CartanMap.sourceAnchorChartMetric g x₀ a a' := by
          rw [← hScale]
          ring
  · intro a a'
    calc
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (Ψt (L a) T).1 (Ψt (L a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • L a) (T⁻¹ • L a') :=
          hTargetRescaled (L a) (L a')
      _ = JacobiNormSystem.speedPinnedScale speed T *
          ((T⁻¹ * T⁻¹) * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')) := by
          rw [UnscaledFeed.targetAnchorChartMetric_inv_smul_inv_smul]
      _ = Real.sin θ ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a') := by
          rw [← hScale]
          ring

end Feed

end SpeedGeneric

end Poincare
