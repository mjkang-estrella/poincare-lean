import Poincare.Global.ChartCurvatureBridge5
import Poincare.Global.RoundSphereCurvature

/-!
# Chart curvature bridge, curvature assembly

This module assembles the final curvature-level transport step after
`ChartCurvatureBridge5`.  The main theorem keeps the statement from
`harness/reports/M5-bridge-5_blocked.md`; the only spelling adaptation is that
the theorem lives in the namespace `Poincare.ChartCurvatureBridge6`.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge6

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

/--
At the anchor, transporting a closed Levi-Civita application through the chart
agrees with applying the model chart Levi-Civita connection to the transported
field and transported direction.
-/
theorem chartTransportedLeviCivitaSection_closed_hom_apply_anchor
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M}
    {σ X : Π y : M, TM y} (hσ : MDiffAtTangentField σ x₀) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σ y (X y))
        (extChartAt I x₀ x₀) =
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
        (extChartAt I x₀ x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
          (extChartAt I x₀ x₀)) := by
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
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend :
      ContDiff ℝ 2
        (CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀) :=
    CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
      htwo_add_one_le_top (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀) hg2
  have hclosed :
      CovariantDerivative.chartTransportedLeviCivitaHom
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n))
          (GeodesicTransport.backgroundMetric_pos (n := n))
          g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (GeodesicTransport.cutoff_nonneg (n := n) x₀)
          (GeodesicTransport.cutoff_le_one (n := n) x₀)
          (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
          σ x₀ =
        g.leviCivita σ x₀ := by
    simpa [ClosedSmoothRiemannianMetric.leviCivita] using
      LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
        g (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n)) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        (hblend.differentiable (by norm_num))
        (GeodesicTransport.backgroundMetric_symm (n := n))
        (mem_extChartAt_source x₀)
        (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x₀)
        hσ
  have htransport :=
    ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_apply_chart
      (g := g) (x₀ := x₀) (y := x₀) (mem_extChartAt_source x₀) σ X
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σ y (X y))
          (extChartAt I x₀ x₀) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M =>
            CovariantDerivative.chartTransportedLeviCivitaHom
              (GeodesicTransport.cutoff (n := n) x₀)
              (GeodesicTransport.backgroundMetric (n := n))
              (GeodesicTransport.backgroundMetric_pos (n := n))
              g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
              (GeodesicTransport.cutoff_nonneg (n := n) x₀)
              (GeodesicTransport.cutoff_le_one (n := n) x₀)
              (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
              σ y (X y))
          (extChartAt I x₀ x₀) := by
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x₀)
        (σ := fun y : M => g.leviCivita σ y (X y))
        (y := x₀) (mem_extChartAt_source x₀)]
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x₀)
        (σ := fun y : M =>
          CovariantDerivative.chartTransportedLeviCivitaHom
            (GeodesicTransport.cutoff (n := n) x₀)
            (GeodesicTransport.backgroundMetric (n := n))
            (GeodesicTransport.backgroundMetric_pos (n := n))
            g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
            (GeodesicTransport.cutoff_nonneg (n := n) x₀)
            (GeodesicTransport.cutoff_le_one (n := n) x₀)
            (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
            σ y (X y))
        (y := x₀) (mem_extChartAt_source x₀)]
    rw [hclosed]
  exact hleft.trans htransport

/--
Closed inner Levi-Civita derivatives of canonical extensions transport to the
corresponding model-side inner derivatives near the anchor.
-/
theorem chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (a w : TM x₀) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M =>
          g.leviCivita (FiberBundle.extend F a) y (FiberBundle.extend F w y))
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    (fun z : F =>
      (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) a)
        z
        (FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) w z)) := by
  have hhom :=
    ChartCurvatureBridge3.chartTransportedLeviCivitaHom_extend_eventuallyEq_closed
      (g := g) (x₀ := x₀) a
  have hfield :
      (fun y : M =>
        CovariantDerivative.chartTransportedLeviCivitaHom
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n))
          (GeodesicTransport.backgroundMetric_pos (n := n))
          g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (GeodesicTransport.cutoff_nonneg (n := n) x₀)
          (GeodesicTransport.cutoff_le_one (n := n) x₀)
          (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
          (FiberBundle.extend F a) y (FiberBundle.extend F w y))
        =ᶠ[𝓝 x₀]
      (fun y : M =>
        g.leviCivita (FiberBundle.extend F a) y (FiberBundle.extend F w y)) := by
    filter_upwards [hhom] with y hy
    rw [Bundle.TotalSpace.mk_inj] at hy
    rw [hy]
  have hsection :=
    ChartCurvatureBridge5.chartTransportedLeviCivitaSection_congr_of_eventuallyEq
      (x₀ := x₀) hfield.symm
  exact hsection.trans
    (ChartCurvatureBridge4.chartTransportedLeviCivitaSection_inner_extend_eventuallyEq
      (g := g) (x₀ := x₀) a w)

/--
Model-side chart curvature on canonical model extensions equals the
inverse-chart transport of the manifold-side closed curvature on canonical
manifold extensions.
-/
theorem chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (u w a : TM x₀) :
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) u)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) w)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) a)
        (extChartAt I x₀ x₀)
      =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita
        (FiberBundle.extend F u)
        (FiberBundle.extend F w)
        (FiberBundle.extend F a))
      (extChartAt I x₀ x₀) := by
  let z₀ : F := extChartAt I x₀ x₀
  let U : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z₀) u
  let W : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z₀) w
  let A : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z₀) a
  let UM : Π y : M, TM y := FiberBundle.extend F u
  let WM : Π y : M, TM y := FiberBundle.extend F w
  let AM : Π y : M, TM y := FiberBundle.extend F a
  let σw : Π y : M, TM y := fun y => g.leviCivita AM y (WM y)
  let σu : Π y : M, TM y := fun y => g.leviCivita AM y (UM y)
  let τw : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    fun z => (GeodesicTransport.chartLeviCivita g x₀) A z (W z)
  let τu : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    fun z => (GeodesicTransport.chartLeviCivita g x₀) A z (U z)
  have hUM : MDiffAtTangentField UM x₀ := by
    simpa [UM, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F u)
  have hWM : MDiffAtTangentField WM x₀ := by
    simpa [WM, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F w)
  have hσw : MDiffAtTangentField σw x₀ := by
    simpa [σw, AM, WM, MDiffAtTangentField] using
      (CovariantDerivative.derivRegularAt_extend g.leviCivita a
        (by simpa [MDiffAtTangentField] using hWM))
  have hσu : MDiffAtTangentField σu x₀ := by
    simpa [σu, AM, UM, MDiffAtTangentField] using
      (CovariantDerivative.derivRegularAt_extend g.leviCivita a
        (by simpa [MDiffAtTangentField] using hUM))
  have hsecw :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw
        =ᶠ[𝓝 z₀] τw := by
    simpa [z₀, σw, τw, AM, WM, A, W] using
      (chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq
        (g := g) (x₀ := x₀) a w)
  have hsecu :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu
        =ᶠ[𝓝 z₀] τu := by
    simpa [z₀, σu, τu, AM, UM, A, U] using
      (chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq
        (g := g) (x₀ := x₀) a u)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hσw_chart :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z₀ := by
    simpa [z₀, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := x₀) (mem_extChartAt_source x₀)
        (by simpa [MDiffAtTangentField] using hσw)
  have hσu_chart :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z₀ := by
    simpa [z₀, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := x₀) (mem_extChartAt_source x₀)
        (by simpa [MDiffAtTangentField] using hσu)
  have hτw :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, τw z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z₀ := by
    refine MDifferentiableAt.congr_of_eventuallyEq hσw_chart ?_
    filter_upwards [hsecw] with z hz
    rw [hz]
  have hτu :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, τu z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z₀ := by
    refine MDifferentiableAt.congr_of_eventuallyEq hσu_chart ?_
    filter_upwards [hsecu] with z hz
    rw [hz]
  have hcovw :
      (GeodesicTransport.chartLeviCivita g x₀) τw z₀ =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw) z₀ := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hτw hσw_chart Filter.univ_mem
    exact hsecw.symm
  have hcovu :
      (GeodesicTransport.chartLeviCivita g x₀) τu z₀ =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu) z₀ := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hτu hσu_chart Filter.univ_mem
    exact hsecu.symm
  have hU_at : U z₀ = u := by
    have hUconst :
        U = fun _ : F => u := by
      simpa [U, z₀] using
        (CovariantDerivative.extend_model_space'
          (x := z₀) (w := (u : TangentSpace (𝓘(ℝ, F)) z₀)))
    rw [hUconst]
  have hW_at : W z₀ = w := by
    have hWconst :
        W = fun _ : F => w := by
      simpa [W, z₀] using
        (CovariantDerivative.extend_model_space'
          (x := z₀) (w := (w : TangentSpace (𝓘(ℝ, F)) z₀)))
    rw [hWconst]
  have hUM_at :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ UM z₀ = u := by
    simpa [z₀, UM] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀) (y := x₀)
        (mem_extChartAt_source x₀) u)
  have hWM_at :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ WM z₀ = w := by
    simpa [z₀, WM] using
      (chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀) (y := x₀)
        (mem_extChartAt_source x₀) w)
  have hterm1 :
      (GeodesicTransport.chartLeviCivita g x₀) τw z₀ (U z₀) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σw y (UM y)) z₀ := by
    calc
      (GeodesicTransport.chartLeviCivita g x₀) τw z₀ (U z₀)
          =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw)
          z₀ (U z₀) := by rw [hcovw]
      _ =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw)
          z₀ (CovariantDerivative.chartTransportedLeviCivitaSection x₀ UM z₀) := by
            rw [hU_at, hUM_at]
      _ =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σw y (UM y)) z₀ := by
            exact (chartTransportedLeviCivitaSection_closed_hom_apply_anchor
              (g := g) (x₀ := x₀) (σ := σw) (X := UM) hσw).symm
  have hterm2 :
      (GeodesicTransport.chartLeviCivita g x₀) τu z₀ (W z₀) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σu y (WM y)) z₀ := by
    calc
      (GeodesicTransport.chartLeviCivita g x₀) τu z₀ (W z₀)
          =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu)
          z₀ (W z₀) := by rw [hcovu]
      _ =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu)
          z₀ (CovariantDerivative.chartTransportedLeviCivitaSection x₀ WM z₀) := by
            rw [hW_at, hWM_at]
      _ =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σu y (WM y)) z₀ := by
            exact (chartTransportedLeviCivitaSection_closed_hom_apply_anchor
              (g := g) (x₀ := x₀) (σ := σu) (X := WM) hσu).symm
  have hbr_model : VectorField.mlieBracket 𝓘(ℝ, F) U W z₀ = 0 := by
    have hUconst :
        U = fun _ : F => u := by
      simpa [U, z₀] using
        (CovariantDerivative.extend_model_space'
          (x := z₀) (w := (u : TangentSpace (𝓘(ℝ, F)) z₀)))
    have hWconst :
        W = fun _ : F => w := by
      simpa [W, z₀] using
        (CovariantDerivative.extend_model_space'
          (x := z₀) (w := (w : TangentSpace (𝓘(ℝ, F)) z₀)))
    rw [hUconst, hWconst, mlieBracket_vectorSpace_eq]
    simp [VectorField.lieBracket]
    rfl
  have hbr_manifold :
      VectorField.mlieBracket I UM WM x₀ = 0 := by
    simpa [UM, WM] using
      (mlieBracket_extend_extend_eventually_eq_zero
        (n := n) (M := M) (x := x₀) u w).self_of_nhds
  have hterm3 :
      (GeodesicTransport.chartLeviCivita g x₀) A z₀
          (VectorField.mlieBracket 𝓘(ℝ, F) U W z₀) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M =>
            g.leviCivita AM y (VectorField.mlieBracket I UM WM y)) z₀ := by
    rw [hbr_model]
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀)
      (σ := fun y : M =>
        g.leviCivita AM y (VectorField.mlieBracket I UM WM y))
      (y := x₀)
      (mem_extChartAt_source x₀)]
    simpa [hbr_manifold] using
      (map_zero (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) x₀)).symm
  have hRHS :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita UM WM AM) z₀ =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σw y (UM y)) z₀
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σu y (WM y)) z₀
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M =>
          g.leviCivita AM y (VectorField.mlieBracket I UM WM y)) z₀ := by
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply]
    simp only [CovariantDerivative.curvatureOp]
    let D :=
      (mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I) z₀).inverse
    let y : M := (extChartAt I x₀).symm z₀
    let t₁ : TM y := (g.leviCivita σw y) (UM y)
    let t₂ : TM y := (g.leviCivita σu y) (WM y)
    let t₃ : TM y := (g.leviCivita AM y) (VectorField.mlieBracket I UM WM y)
    change D (t₁ - t₂ - t₃) = D t₁ - D t₂ - D t₃
    rw [map_sub, map_sub]
  rw [show extChartAt I x₀ x₀ = z₀ from rfl]
  change
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
      U W A z₀ =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita UM WM AM) z₀
  rw [hRHS]
  rw [CovariantDerivative.curvatureOp_apply]
  change
    (GeodesicTransport.chartLeviCivita g x₀) τw z₀ (U z₀)
      - (GeodesicTransport.chartLeviCivita g x₀) τu z₀ (W z₀)
      - (GeodesicTransport.chartLeviCivita g x₀) A z₀
          (VectorField.mlieBracket 𝓘(ℝ, F) U W z₀) =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σw y (UM y)) z₀
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σu y (WM y)) z₀
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M =>
          g.leviCivita AM y (VectorField.mlieBracket I UM WM y)) z₀
  rw [hterm1, hterm2, hterm3]

/--
Full chart-curvature bridge obtained by composing
`ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`
with `chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp`.
-/
theorem chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (u w a : TM x₀) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀)
        (extChartAt I x₀ x₀) u w a =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita
          (FiberBundle.extend F u)
          (FiberBundle.extend F w)
          (FiberBundle.extend F a))
        (extChartAt I x₀ x₀) := by
  rw [ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature
    (g := g) (x₀ := x₀) u w a]
  exact chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp
    (g := g) (x₀ := x₀) u w a

end ChartCurvatureBridge6

end Poincare
