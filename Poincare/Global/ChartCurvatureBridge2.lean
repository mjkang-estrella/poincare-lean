import Poincare.Global.ChartCurvatureBridge

/-!
# Chart curvature bridge packaging

This module closes the packaging step from the plain chart Christoffel field to
the model chart Levi-Civita curvature.  The Christoffel field
`GeodesicTransport.chartChristoffelField g x₀` is already an ordinary family
`F → F →L[ℝ] F →L[ℝ] F`; the theorem below identifies its `chartCurvatureOf`
with `curvatureOp` of `GeodesicTransport.chartLeviCivita` on canonical model
extensions anchored at the chart center.

The remaining manifold pushforward, from `g.leviCivita` on manifold
`extend` fields through the chart identification to this model curvature, is
recorded in the worker report.
-/

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge2

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

/--
Packaging bridge for the plain chart Christoffel field.

The vector arguments `u v w : F` are model coordinates at the anchor
`extChartAt I x₀ x₀`.  The right-hand side uses the tangent-bundle
interpretation of `FiberBundle.extend` explicitly:
`TangentSpace 𝓘(ℝ, F) z = F` for the model chart, but the annotation keeps
Lean from choosing the trivial bundle extension instead.
-/
theorem chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (u v w : F) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀)
        (extChartAt I x₀ x₀) u v w =
      CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := extChartAt I x₀ x₀) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := extChartAt I x₀ x₀) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := extChartAt I x₀ x₀) w)
        (extChartAt I x₀ x₀) := by
  let z₀ : F := extChartAt I x₀ x₀
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
  have hΓ : DifferentiableAt ℝ (GeodesicTransport.chartChristoffelField g x₀) z₀ := by
    dsimp [z₀]
    exact (GeodesicTransport.chartChristoffelField_contDiffAt g x₀).differentiableAt
      (by norm_num)
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
  have hGd : ∀ᶠ y in 𝓝 z₀, DifferentiableAt ℝ G y :=
    Filter.Eventually.of_forall fun y => (hblend.differentiable (by norm_num)) y
  have hGz : DifferentiableAt ℝ G z₀ := hGd.self_of_nhds
  have hGsymm : ∀ (y p q : F), G y p q = G y q p := by
    intro y p q
    dsimp [G]
    exact CovariantDerivative.blendedChartMetric_symm
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_symm (n := n)) g.inner
      (fun y v w => g.inner_symm y v w) x₀ y p q
  have hvw :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) v w) =ᶠ[𝓝 z₀]
        fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w v := by
    change
      (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        F →L[ℝ] F →L[ℝ] F) v w) =ᶠ[𝓝 z₀]
        fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
          F →L[ℝ] F →L[ℝ] F) w v
    exact ChartCurvatureBridge.eventually_christoffelOneForm_symm
      (G := G) (b := b) (hb := hb) (z := z₀) hGd hGsymm v w
  have huw :
      (fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) u w) =ᶠ[𝓝 z₀]
        fun y ↦ (GeodesicTransport.chartChristoffelField g x₀ y) w u := by
    change
      (fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
        F →L[ℝ] F →L[ℝ] F) u w) =ᶠ[𝓝 z₀]
        fun y ↦ (CovariantDerivative.christoffelOneForm G b hb y :
          F →L[ℝ] F →L[ℝ] F) w u
    exact ChartCurvatureBridge.eventually_christoffelOneForm_symm
      (G := G) (b := b) (hb := hb) (z := z₀) hGd hGsymm u w
  have hW : FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
        F (x := z₀) w = (fun _ : F => w) := by
    simpa using (CovariantDerivative.extend_model_space' (x := z₀)
      (w := (w : TangentSpace 𝓘(ℝ, F) z₀)))
  have hcurv :
      CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) w) z₀ =
        (fderiv ℝ (fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) v w)
            z₀) u
          + CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u
            (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v w)
          - ((fderiv ℝ
              (fun y ↦ CovariantDerivative.christoffelAt G y (b y) (hb y) u w) z₀) v
          + CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v
            (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u w)) := by
    change
      CovariantDerivative.curvatureOp
          (CovariantDerivative.modelLeviCivita G b hb)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) u)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) v)
        (FiberBundle.extend (E := fun x : F => TangentSpace 𝓘(ℝ, F) x)
          F (x := z₀) w) z₀ = _
    rw [hW]
    rw [CovariantDerivative.curvatureOp_modelLeviCivita_extend
      (G := G) (b := b) (hb := hb)
      (X := fun _ : F => w) (x := z₀) (v := u) (w := v)]
    simp
  rw [show extChartAt I x₀ x₀ = z₀ from rfl]
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
  have hzuv : (GeodesicTransport.chartChristoffelField g x₀ z₀) u
      ((GeodesicTransport.chartChristoffelField g x₀ z₀) w v) =
      CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u
        (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v w) := by
    change (CovariantDerivative.christoffelOneForm G b hb z₀ :
      F →L[ℝ] F →L[ℝ] F) u
        ((CovariantDerivative.christoffelOneForm G b hb z₀ :
          F →L[ℝ] F →L[ℝ] F) w v) =
      CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u
        (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v w)
    exact CovariantDerivative.christoffelAt_symm G (b z₀) (hb z₀) hGz hGsymm
      (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v w) u
  have hzvu : (GeodesicTransport.chartChristoffelField g x₀ z₀) v
      ((GeodesicTransport.chartChristoffelField g x₀ z₀) w u) =
      CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v
        (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u w) := by
    change (CovariantDerivative.christoffelOneForm G b hb z₀ :
      F →L[ℝ] F →L[ℝ] F) v
        ((CovariantDerivative.christoffelOneForm G b hb z₀ :
          F →L[ℝ] F →L[ℝ] F) w u) =
      CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) v
        (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u w)
    exact CovariantDerivative.christoffelAt_symm G (b z₀) (hb z₀) hGz hGsymm
      (CovariantDerivative.christoffelAt G z₀ (b z₀) (hb z₀) u w) v
  rw [hfv, hfu, hzuv, hzvu]
  abel

end ChartCurvatureBridge2

end Poincare
