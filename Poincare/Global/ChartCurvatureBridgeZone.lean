import Poincare.Global.JacobiInstantiate
import Poincare.Global.GeodesicDependence

/-!
# Chart curvature bridge on a cutoff-one chart zone

This module moves the curvature bridge away from the anchor chart point in the
parts that are currently available without adding new trust:

* the model-side packaging
  `chartCurvatureOf (chartChristoffelField g x₀) z = curvatureOp
  (chartLeviCivita g x₀) ... z` is proved at an arbitrary model point `z`;
* lowering the inverse-chart transport of the manifold curvature by the chart
  metric gives the constant-curvature-one Kulkarni-Nomizu identity at any
  chart-target point `z`.

The final theorem records the exact remaining glue: identifying the model
chart-Levi-Civita curvature on constant model fields at `z` with the transported
manifold curvature on the inverse-chart tangent vectors at
`(extChartAt I x₀).symm z`.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ChartCurvatureBridgeZone

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "F" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The tangent map of the inverse `x₀` chart at a model point `z`. -/
noncomputable def chartInverseTangent (x₀ : M) (z : F) :
    F →L[ℝ] TM ((extChartAt I x₀).symm z) :=
  mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I) z

/--
The `ChartCurvatureBridge2` model-side packaging at an arbitrary model point
`z`, rather than only at `extChartAt I x₀ x₀`.

This is the purely chart-level half of the zone bridge.  It does not use the
cutoff-one hypothesis; the cutoff-one input is needed for the remaining
model/manifold curvature transport.
-/
theorem chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature_at
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z : F) (u v w : F) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z u v w =
      CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) w)
        z := by
  let G : F → F →L[ℝ] F →L[ℝ] ℝ :=
    CovariantDerivative.blendedChartMetric (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
  let b : Π _ : F, LinearMap.BilinForm ℝ F :=
    CovariantDerivative.chartBilin (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
  let hb : ∀ z, (b z).Nondegenerate :=
    CovariantDerivative.chartBilin_nondegenerate
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_pos (n := n)) g.inner
      (fun y u hu => g.inner_pos y (v := u) hu) x₀
      (GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (GeodesicTransport.cutoff_le_one (n := n) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
  have hΓ : DifferentiableAt ℝ (GeodesicTransport.chartChristoffelField g x₀) z :=
    (GeodesicTransport.chartChristoffelField_contDiffAt_base
      (g := g) (x₀ := x₀) z).differentiableAt (by norm_num)
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend : ContDiff ℝ 2 G := by
    dsimp [G]
    exact CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
      htwo_add_one_le_top (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀) hg2
  have hGd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ G y :=
    Filter.Eventually.of_forall fun y => (hblend.differentiable (by norm_num)) y
  have hGz : DifferentiableAt ℝ G z := hGd.self_of_nhds
  have hGsymm : ∀ (y p q : F), G y p q = G y q p := by
    intro y p q
    dsimp [G]
    exact CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_symm (n := n)) g.inner
      (fun y v w => g.inner_symm y v w) x₀ y p q
  have hvw :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) v w) =ᶠ[𝓝 z]
        fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w v := by
    change
      (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        F →L[ℝ] F →L[ℝ] F) v w) =ᶠ[𝓝 z]
        fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
          F →L[ℝ] F →L[ℝ] F) w v
    exact ChartCurvatureBridge.eventually_christoffelOneForm_symm
      (G := G) (b := b) (hb := hb) (z := z) hGd hGsymm v w
  have huw :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) u w) =ᶠ[𝓝 z]
        fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w u := by
    change
      (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        F →L[ℝ] F →L[ℝ] F) u w) =ᶠ[𝓝 z]
        fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
          F →L[ℝ] F →L[ℝ] F) w u
    exact ChartCurvatureBridge.eventually_christoffelOneForm_symm
      (G := G) (b := b) (hb := hb) (z := z) hGd hGsymm u w
  have hW : FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
        F (x := z) w = (fun _ : F => w) := by
    simpa using (CovariantDerivative.extend_model_space' (x := z)
      (w := (w : TangentSpace 𝓘(ℝ, F) z)))
  have hcurv :
      CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) w) z =
        (fderiv ℝ (fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) v w)
            z) u
          + CovariantDerivative.christoffelAt G z (b z) (hb z) u
            (CovariantDerivative.christoffelAt G z (b z) (hb z) v w)
          - ((fderiv ℝ
              (fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) u w) z) v
          + CovariantDerivative.christoffelAt G z (b z) (hb z) v
            (CovariantDerivative.christoffelAt G z (b z) (hb z) u w)) := by
    change
      CovariantDerivative.curvatureOp
          (CovariantDerivative.modelLeviCivita G b hb)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z) w) z = _
    rw [hW]
    rw [CovariantDerivative.curvatureOp_modelLeviCivita_extend
      (G := G) (b := b) (hb := hb)
      (X := fun _ : F => w) (x := z) (v := u) (w := v)]
    simp
  rw [ChartCurvatureBridge.chartCurvatureOf_eq_fderiv_apply_swapped_of_eventually_symm
    (Γ := GeodesicTransport.chartChristoffelField g x₀) hΓ u v w hvw huw]
  rw [hcurv]
  have hfv :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w v) =
        fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) v w := by
    funext y
    change (CovariantDerivative.christoffelOneForm G b hb y :
      F →L[ℝ] F →L[ℝ] F) w v =
        CovariantDerivative.christoffelAt G y (b y) (hb y) v w
    rfl
  have hfu :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w u) =
        fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) u w := by
    funext y
    change (CovariantDerivative.christoffelOneForm G b hb y :
      F →L[ℝ] F →L[ℝ] F) w u =
        CovariantDerivative.christoffelAt G y (b y) (hb y) u w
    rfl
  have hzuv : (GeodesicTransport.chartChristoffelField g x₀ z) u
      ((GeodesicTransport.chartChristoffelField g x₀ z) w v) =
      CovariantDerivative.christoffelAt G z (b z) (hb z) u
        (CovariantDerivative.christoffelAt G z (b z) (hb z) v w) := by
    change (CovariantDerivative.christoffelOneForm G b hb z :
      F →L[ℝ] F →L[ℝ] F) u
        ((CovariantDerivative.christoffelOneForm G b hb z :
          F →L[ℝ] F →L[ℝ] F) w v) =
      CovariantDerivative.christoffelAt G z (b z) (hb z) u
        (CovariantDerivative.christoffelAt G z (b z) (hb z) v w)
    exact CovariantDerivative.christoffelAt_symm G (b z) (hb z) hGz hGsymm
      (CovariantDerivative.christoffelAt G z (b z) (hb z) v w) u
  have hzvu : (GeodesicTransport.chartChristoffelField g x₀ z) v
      ((GeodesicTransport.chartChristoffelField g x₀ z) w u) =
      CovariantDerivative.christoffelAt G z (b z) (hb z) v
        (CovariantDerivative.christoffelAt G z (b z) (hb z) u w) := by
    change (CovariantDerivative.christoffelOneForm G b hb z :
      F →L[ℝ] F →L[ℝ] F) v
        ((CovariantDerivative.christoffelOneForm G b hb z :
          F →L[ℝ] F →L[ℝ] F) w u) =
      CovariantDerivative.christoffelAt G z (b z) (hb z) v
        (CovariantDerivative.christoffelAt G z (b z) (hb z) u w)
    exact CovariantDerivative.christoffelAt_symm G (b z) (hb z) hGz hGsymm
      (CovariantDerivative.christoffelAt G z (b z) (hb z) u w) v
  rw [hfv, hfu, hzuv, hzvu]
  abel

section DimensionThree

variable {M3 : Type u}
variable [TopologicalSpace M3] [T2Space M3]
variable [ChartedSpace (ClosedSmoothModel 3) M3]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M3]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3
local notation "TM3" => (TangentSpace I3 : M3 → Type _)

/--
At a chart point `z`, the manifold Kulkarni-Nomizu tensor on inverse-chart
tangent vectors is the chart Kulkarni-Nomizu tensor of the transported chart
metric.
-/
theorem tensorKulkarniNomizuAt_eq_chartMetric_zone
    (g : ClosedSmoothRiemannianMetric 3 M3) (x₀ : M3) (z : E3)
    (u w a b : E3) :
    ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
        (n := 3) (M := M3) ((extChartAt I3 x₀).symm z)
        (fun p q ↦ g.inner ((extChartAt I3 x₀).symm z) p q)
        (fun p q ↦ g.inner ((extChartAt I3 x₀).symm z) p q)
        (chartInverseTangent (n := 3) x₀ z u)
        (chartInverseTangent (n := 3) x₀ z w)
        (chartInverseTangent (n := 3) x₀ z a)
        (chartInverseTangent (n := 3) x₀ z b) =
      chartTensorKulkarniNomizu
        (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
        (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
        u w a b := by
  unfold ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
    chartTensorKulkarniNomizu chartInverseTangent
  simp [CovariantDerivative.chartMetric_apply]
  ring_nf
  rfl

/--
Lowering the inverse-chart transport of the manifold curvature field by the
chart metric recovers the manifold curvature lowered by `g` at
`(extChartAt I3 x₀).symm z`.
-/
theorem chartMetric_chartTransported_curvatureOp_eq_inner_curvature_zone
    (g : ClosedSmoothRiemannianMetric 3 M3) (x₀ : M3) {z : E3}
    (hz : z ∈ (extChartAt I3 x₀).target) (u w a b : E3) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (chartInverseTangent (n := 3) x₀ z u))
            (extend E3 (chartInverseTangent (n := 3) x₀ z w))
            (extend E3 (chartInverseTangent (n := 3) x₀ z a))) z) b =
      g.inner ((extChartAt I3 x₀).symm z)
        (CovariantDerivative.curvatureOp g.leviCivita
          (extend E3 (chartInverseTangent (n := 3) x₀ z u))
          (extend E3 (chartInverseTangent (n := 3) x₀ z w))
          (extend E3 (chartInverseTangent (n := 3) x₀ z a))
          ((extChartAt I3 x₀).symm z))
        (chartInverseTangent (n := 3) x₀ z b) := by
  let y : M3 := (extChartAt I3 x₀).symm z
  let D : E3 →L[ℝ] TM3 y := chartInverseTangent (n := 3) x₀ z
  let R : Π y : M3, TM3 y :=
    CovariantDerivative.curvatureOp g.leviCivita
      (extend E3 (D u)) (extend E3 (D w)) (extend E3 (D a))
  have hD : D.IsInvertible := by
    simpa [D, chartInverseTangent, y] using
      (isInvertible_mfderivWithin_extChartAt_symm (x := x₀) hz)
  have hR : D (D.inverse (R y)) = R y :=
    (hD.inverse_apply_eq.mp rfl).symm
  rw [CovariantDerivative.chartMetric_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  change g.inner y (D (D.inverse (R y))) (D b) = g.inner y (R y) (D b)
  rw [hR]

/--
The constant-curvature-one identity at a chart-target point for the transported
manifold curvature field.  This is the lowered form needed after the remaining
zone curvature bridge identifies `chartCurvatureOf` with this transported
field.
-/
theorem chartMetric_chartTransported_curvatureOp_constantCurvature_one_zone
    (g : ClosedSmoothRiemannianMetric 3 M3)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M3) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (u w a b : E3) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (chartInverseTangent (n := 3) x₀ z u))
            (extend E3 (chartInverseTangent (n := 3) x₀ z w))
            (extend E3 (chartInverseTangent (n := 3) x₀ z a))) z) b =
      -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          u w a b := by
  let y : M3 := (extChartAt I3 x₀).symm z
  let D : E3 →L[ℝ] TM3 y := chartInverseTangent (n := 3) x₀ z
  calc
    CovariantDerivative.chartMetric g.inner x₀ z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (chartInverseTangent (n := 3) x₀ z u))
            (extend E3 (chartInverseTangent (n := 3) x₀ z w))
            (extend E3 (chartInverseTangent (n := 3) x₀ z a))) z) b =
        g.inner y
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (D u)) (extend E3 (D w)) (extend E3 (D a)) y)
          (D b) := by
            simpa [D, y] using
              chartMetric_chartTransported_curvatureOp_eq_inner_curvature_zone
                (g := g) (x₀ := x₀) (z := z) hz u w a b
    _ = -(1 / 2 : ℝ) *
        ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt
          (n := 3) (M := M3) y
          (fun p q ↦ g.inner y p q)
          (fun p q ↦ g.inner y p q) (D u) (D w) (D a) (D b) := by
          simpa [D, y] using hcurv y (D u) (D w) (D a) (D b)
    _ = -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          u w a b := by
          rw [tensorKulkarniNomizuAt_eq_chartMetric_zone
            (g := g) (x₀ := x₀) (z := z) u w a b]

/--
Final glue formulation: once the zone curvature bridge identifies the chart
curvature with the transported manifold curvature on inverse-chart tangent
vectors, the chart-level constant-curvature-one identity follows at `z`.
-/
theorem chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone_of_bridge
    (g : ClosedSmoothRiemannianMetric 3 M3)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M3) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (u w a b : E3)
    (hbridge :
      chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z u w a =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (CovariantDerivative.curvatureOp g.leviCivita
            (extend E3 (chartInverseTangent (n := 3) x₀ z u))
            (extend E3 (chartInverseTangent (n := 3) x₀ z w))
            (extend E3 (chartInverseTangent (n := 3) x₀ z a))) z) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀) z u w a) b =
      -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          u w a b := by
  rw [hbridge]
  exact chartMetric_chartTransported_curvatureOp_constantCurvature_one_zone
    (g := g) hcurv (x₀ := x₀) (z := z) hz u w a b

end DimensionThree

end ChartCurvatureBridgeZone
end Poincare
