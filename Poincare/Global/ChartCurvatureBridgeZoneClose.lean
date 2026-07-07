import Poincare.Global.ChartCurvatureBridgeZone

/-!
# Closing the cutoff-one chart curvature bridge

This module closes the remaining field-choice gap from
`ChartCurvatureBridgeZone`: at a cutoff-one chart point, curvature evaluated on
the chart-constant model fields agrees with the transported closed-manifold
curvature evaluated on the canonical `extend` fields based at the source point.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ChartCurvatureBridgeZoneClose

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

private theorem two_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

private theorem two_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
  rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

private theorem one_add_one_add_one_le_top :
    (1 : ℕ∞ω) + 1 + 1 ≤ (∞ : ℕ∞ω) := by
  rw [show (1 : ℕ∞ω) + 1 + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

private theorem three_add_one_le_top : (3 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
  rw [show (3 : ℕ∞ω) + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
    show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- The blended chart metric for a closed smooth metric is differentiable. -/
private theorem blendedChartMetric_differentiable
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    Differentiable ℝ
      (CovariantDerivative.blendedChartMetric
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀) := by
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le two_le_top
  exact
    (CovariantDerivative.contDiff_blendedChartMetric
      (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀
      two_add_one_le_top
      (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀) hg2).differentiable
        (by norm_num)

/--
At any source point whose chart image lies in a cutoff-one germ, the transported
chart Levi-Civita hom agrees pointwise with the closed Levi-Civita connection.
-/
theorem chartTransportedLeviCivitaHom_eq_closed_of_cutoff_eventuallyEq_one_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    {σ : Π y : M, TM y} (hσ : MDiffAtTangentField σ y) :
    CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        σ y =
      g.leviCivita σ y := by
  simpa [ClosedSmoothRiemannianMetric.leviCivita] using
    LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
      g (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_pos (n := n)) x₀
      (GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (GeodesicTransport.cutoff_le_one (n := n) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
      (blendedChartMetric_differentiable (n := n) (M := M) g x₀)
      (GeodesicTransport.backgroundMetric_symm (n := n))
      hy hχone hσ

/--
Pointwise naturality of the closed Levi-Civita derivative through the anchor
chart at an arbitrary cutoff-one source point.
-/
theorem chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (σ X : Π y : M, TM y) (hσ : MDiffAtTangentField σ y) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun y : M => g.leviCivita σ y (X y))
        (extChartAt I x₀ y) =
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
        (extChartAt I x₀ y)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
          (extChartAt I x₀ y)) := by
  have hclosed :=
    chartTransportedLeviCivitaHom_eq_closed_of_cutoff_eventuallyEq_one_at
      (g := g) (x₀ := x₀) (y := y) hy hχone hσ
  have htransport :=
    ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_apply_chart
      (g := g) (x₀ := x₀) (y := y) hy σ X
  have hleft :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun y : M => g.leviCivita σ y (X y))
          (extChartAt I x₀ y) =
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
          (extChartAt I x₀ y) := by
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x₀)
        (σ := fun y : M => g.leviCivita σ y (X y))
        (y := y) hy]
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
        (y := y) hy]
    rw [hclosed]
  exact hleft.trans htransport

/--
Source-point version of the chart hom naturality germ.  It is the same
transport statement as `ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_eventuallyEq`,
but centered at an arbitrary source point of the anchor chart.
-/
theorem chartTransportedLeviCivitaSection_hom_eventuallyEq_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (σ X : Π y : M, TM y) :
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
      =ᶠ[𝓝 (extChartAt I x₀ y)]
    (fun z : F =>
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ) z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X z)) := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds
      ((extChartAt I x₀).map_source hy)] with z hz
  have hyz : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hz_eq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hpoint :=
    ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_apply_chart
      (g := g) (x₀ := x₀) (y := (extChartAt I x₀).symm z) hyz σ X
  rw [hz_eq] at hpoint
  simpa using hpoint

/--
On a cutoff-one germ, the transported chart hom applied to a canonical
extension agrees near the source point with the closed Levi-Civita connection.
-/
theorem chartTransportedLeviCivitaHom_extend_apply_eventuallyEq_closed_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (a w : TM y) :
    (fun q : M =>
      CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        (FiberBundle.extend F a) q (FiberBundle.extend F w q))
      =ᶠ[𝓝 y]
    (fun q : M =>
      g.leviCivita (FiberBundle.extend F a) q (FiberBundle.extend F w q)) := by
  obtain ⟨s, hs, hdiff⟩ :=
    FiberBundle.exists_mdifferentiableOn_extend I F a
  rcases mem_nhds_iff.mp hs with ⟨t, hts, htopen, hyt⟩
  have hsource : (extChartAt I x₀).source ∈ 𝓝 y :=
    extChartAt_source_mem_nhds' hy
  have hχnear :
      ∀ᶠ q in 𝓝 y,
        ∀ᶠ z' in 𝓝 (extChartAt I x₀ q),
          GeodesicTransport.cutoff (n := n) x₀ z' = 1 :=
    (continuousAt_extChartAt' hy).eventually
      (eventually_eventually_nhds.2 hχone)
  filter_upwards [hsource, hχnear, htopen.mem_nhds hyt] with q hqsource hqχ hqt
  have hsq : s ∈ 𝓝 q := mem_nhds_iff.mpr ⟨t, hts, htopen, hqt⟩
  have hσq : MDiffAtTangentField (FiberBundle.extend F a) q :=
    (hdiff q (hts hqt)).mdifferentiableAt hsq
  have hclosed :=
    chartTransportedLeviCivitaHom_eq_closed_of_cutoff_eventuallyEq_one_at
      (g := g) (x₀ := x₀) (y := q) hqsource hqχ hσq
  rw [hclosed]

/--
The closed inner derivative of canonical extensions transports to the model
inner derivative near any cutoff-one chart point.
-/
theorem chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (a w : TM y) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M =>
          g.leviCivita (FiberBundle.extend F a) q (FiberBundle.extend F w q))
      =ᶠ[𝓝 (extChartAt I x₀ y)]
    (fun z : F =>
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F a)) z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F w) z)) := by
  let σH : Π q : M, TM q :=
    fun q : M =>
      CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        (FiberBundle.extend F a) q (FiberBundle.extend F w q)
  have hclosed :
      σH =ᶠ[𝓝 y]
        (fun q : M =>
          g.leviCivita (FiberBundle.extend F a) q (FiberBundle.extend F w q)) := by
    simpa [σH] using
      chartTransportedLeviCivitaHom_extend_apply_eventuallyEq_closed_at
        (g := g) (x₀ := x₀) (y := y) hy hχone a w
  have hsection :=
    ChartCurvatureBridge5.chartTransportedLeviCivitaSection_congr_of_eventuallyEq_at
      (x₀ := x₀) (y := y) hy hclosed.symm
  have hhom :=
    chartTransportedLeviCivitaSection_hom_eventuallyEq_at
      (g := g) (x₀ := x₀) (y := y) hy
      (FiberBundle.extend F a) (FiberBundle.extend F w)
  exact hsection.trans hhom

/--
Curvature of transported canonical extensions in the chart connection is the
inverse-chart transport of the closed-manifold curvature on those extensions,
at any cutoff-one source point.
-/
theorem chartLeviCivita_curvatureOp_chartTransported_extend_eq_chartTransported_curvatureOp_at
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (u w a : TM y) :
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F u))
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F w))
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F a))
        (extChartAt I x₀ y)
      =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita
        (FiberBundle.extend F u)
        (FiberBundle.extend F w)
        (FiberBundle.extend F a))
      (extChartAt I x₀ y) := by
  let z : F := extChartAt I x₀ y
  let U : Π q : M, TM q := FiberBundle.extend F u
  let W : Π q : M, TM q := FiberBundle.extend F w
  let A : Π q : M, TM q := FiberBundle.extend F a
  let Uc : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ U
  let Wc : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ W
  let Ac : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ A
  let σw : Π q : M, TM q := fun q => g.leviCivita A q (W q)
  let σu : Π q : M, TM q := fun q => g.leviCivita A q (U q)
  let B : Π q : M, TM q := VectorField.mlieBracket I U W
  let τw : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    fun z => (GeodesicTransport.chartLeviCivita g x₀) Ac z (Wc z)
  let τu : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    fun z => (GeodesicTransport.chartLeviCivita g x₀) Ac z (Uc z)
  have hU : MDiffAtTangentField U y := by
    simpa [U, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F u)
  have hW : MDiffAtTangentField W y := by
    simpa [W, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F w)
  have hA : MDiffAtTangentField A y := by
    simpa [A, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F a)
  have hσw : MDiffAtTangentField σw y := by
    simpa [σw, A, W, MDiffAtTangentField] using
      (CovariantDerivative.derivRegularAt_extend g.leviCivita a
        (by simpa [MDiffAtTangentField] using hW))
  have hσu : MDiffAtTangentField σu y := by
    simpa [σu, A, U, MDiffAtTangentField] using
      (CovariantDerivative.derivRegularAt_extend g.leviCivita a
        (by simpa [MDiffAtTangentField] using hU))
  have hsecw :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw
        =ᶠ[𝓝 z] τw := by
    simpa [z, σw, τw, A, W, Ac, Wc] using
      chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq_at
        (g := g) (x₀ := x₀) (y := y) hy hχone a w
  have hsecu :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu
        =ᶠ[𝓝 z] τu := by
    simpa [z, σu, τu, A, U, Ac, Uc] using
      chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq_at
        (g := g) (x₀ := x₀) (y := y) hy hχone a u
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hσw_chart :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    simpa [z, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := y) hy
        (by simpa [MDiffAtTangentField] using hσw)
  have hσu_chart :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    simpa [z, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := y) hy
        (by simpa [MDiffAtTangentField] using hσu)
  have hτw :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, τw z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    refine MDifferentiableAt.congr_of_eventuallyEq hσw_chart ?_
    filter_upwards [hsecw] with z hz
    rw [hz]
  have hτu :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, τu z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    refine MDifferentiableAt.congr_of_eventuallyEq hσu_chart ?_
    filter_upwards [hsecu] with z hz
    rw [hz]
  have hcovw :
      (GeodesicTransport.chartLeviCivita g x₀) τw z =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw) z := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hτw hσw_chart Filter.univ_mem
    exact hsecw.symm
  have hcovu :
      (GeodesicTransport.chartLeviCivita g x₀) τu z =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu) z := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hτu hσu_chart Filter.univ_mem
    exact hsecu.symm
  have hterm1 :
      (GeodesicTransport.chartLeviCivita g x₀) τw z (Uc z) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun q : M => g.leviCivita σw q (U q)) z := by
    calc
      (GeodesicTransport.chartLeviCivita g x₀) τw z (Uc z)
          =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σw)
          z (Uc z) := by rw [hcovw]
      _ =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun q : M => g.leviCivita σw q (U q)) z := by
            exact
              (chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
                (g := g) (x₀ := x₀) (y := y) hy hχone
                (σ := σw) (X := U) hσw).symm
  have hterm2 :
      (GeodesicTransport.chartLeviCivita g x₀) τu z (Wc z) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun q : M => g.leviCivita σu q (W q)) z := by
    calc
      (GeodesicTransport.chartLeviCivita g x₀) τu z (Wc z)
          =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σu)
          z (Wc z) := by rw [hcovu]
      _ =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun q : M => g.leviCivita σu q (W q)) z := by
            exact
              (chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
                (g := g) (x₀ := x₀) (y := y) hy hχone
                (σ := σu) (X := W) hσu).symm
  have hbr :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀ B z =
        VectorField.mlieBracket 𝓘(ℝ, F) Uc Wc z := by
    simpa [z, B, U, W, Uc, Wc] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mlieBracket_apply_chart
        x₀ (X := U) (Y := W) hy
        (by simpa [MDiffAtTangentField] using hU)
        (by simpa [MDiffAtTangentField] using hW)
  have hterm3 :
      (GeodesicTransport.chartLeviCivita g x₀) Ac z
          (VectorField.mlieBracket 𝓘(ℝ, F) Uc Wc z) =
        CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (fun q : M => g.leviCivita A q (B q)) z := by
    rw [← hbr]
    exact
      (chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
        (g := g) (x₀ := x₀) (y := y) hy hχone
        (σ := A) (X := B) hA).symm
  have hRHS :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita U W A) z =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita σw q (U q)) z
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita σu q (W q)) z
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita A q (B q)) z := by
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀)
      (σ := CovariantDerivative.curvatureOp g.leviCivita U W A)
      (y := y) hy]
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀)
      (σ := fun q : M => g.leviCivita σw q (U q))
      (y := y) hy]
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀)
      (σ := fun q : M => g.leviCivita σu q (W q))
      (y := y) hy]
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀)
      (σ := fun q : M => g.leviCivita A q (B q))
      (y := y) hy]
    simp only [CovariantDerivative.curvatureOp]
    let D := mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y
    let t₁ : TM y := g.leviCivita σw y (U y)
    let t₂ : TM y := g.leviCivita σu y (W y)
    let t₃ : TM y := g.leviCivita A y (B y)
    change D (t₁ - t₂ - t₃) = D t₁ - D t₂ - D t₃
    rw [map_sub, map_sub]
  rw [show extChartAt I x₀ y = z from rfl]
  change
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
      Uc Wc Ac z =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita U W A) z
  rw [hRHS]
  rw [CovariantDerivative.curvatureOp_apply]
  change
    (GeodesicTransport.chartLeviCivita g x₀) τw z (Uc z)
      - (GeodesicTransport.chartLeviCivita g x₀) τu z (Wc z)
      - (GeodesicTransport.chartLeviCivita g x₀) Ac z
          (VectorField.mlieBracket 𝓘(ℝ, F) Uc Wc z) =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita σw q (U q)) z
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita σu q (W q)) z
      - CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (fun q : M => g.leviCivita A q (B q)) z
  rw [hterm1, hterm2, hterm3]

/--
Field-choice naturality at a cutoff-one chart point: model curvature on
chart-constant fields agrees with transported closed curvature on the
canonical `extend` fields based at the source point `(extChartAt I x₀).symm z`.
-/
theorem chartLeviCivita_curvatureOp_const_eq_chartTransported_curvatureOp_zone
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt I x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (u w a : F) :
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) u)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) w)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) a)
        z
      =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita
        (FiberBundle.extend F
          (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z u))
        (FiberBundle.extend F
          (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z w))
        (FiberBundle.extend F
          (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z a)))
      z := by
  let y : M := (extChartAt I x₀).symm z
  let D : F →L[ℝ] TM y :=
    ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z
  let U₀ : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z) u
  let W₀ : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z) w
  let A₀ : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    FiberBundle.extend
      (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
      F (x := z) a
  let U : Π q : M, TM q := FiberBundle.extend F (D u)
  let W : Π q : M, TM q := FiberBundle.extend F (D w)
  let A : Π q : M, TM q := FiberBundle.extend F (D a)
  let Uc : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ U
  let Wc : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ W
  let Ac : Π z : F, TangentSpace (𝓘(ℝ, F)) z :=
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ A
  have hy : y ∈ (extChartAt I x₀).source := by
    simpa [y] using (extChartAt I x₀).map_target hz
  have hz_eq : extChartAt I x₀ y = z := by
    simpa [y] using (extChartAt I x₀).right_inv hz
  have hχoney :
      ∀ᶠ z' in 𝓝 (extChartAt I x₀ y),
        GeodesicTransport.cutoff (n := n) x₀ z' = 1 := by
    rw [hz_eq]
    exact hχone
  have hround :
      (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y).comp D =
        ContinuousLinearMap.id ℝ F := by
    change (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y).comp
        (mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm)
          (Set.range I) z) =
      ContinuousLinearMap.id ℝ F
    rw [← hz_eq]
    simpa using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        («I» := I) (x := x₀) hy
  have hU₀z : U₀ z = u := by
    have hconst :
        U₀ = fun _ : F => u := by
      simpa [U₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (u : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
  have hW₀z : W₀ z = w := by
    have hconst :
        W₀ = fun _ : F => w := by
      simpa [W₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (w : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
  have hA₀z : A₀ z = a := by
    have hconst :
        A₀ = fun _ : F => a := by
      simpa [A₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (a : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
  have hUcz : Uc z = u := by
    rw [← hz_eq]
    change CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (FiberBundle.extend F (D u)) (extChartAt I x₀ y) = u
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀) (σ := FiberBundle.extend F (D u))
      (y := y) hy]
    have hUy : FiberBundle.extend F (D u) y = D u := by
      simp [extend_apply_self]
    rw [hUy]
    have happ := congrArg (fun L : F →L[ℝ] F => L u) hround
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hWcz : Wc z = w := by
    rw [← hz_eq]
    change CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (FiberBundle.extend F (D w)) (extChartAt I x₀ y) = w
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀) (σ := FiberBundle.extend F (D w))
      (y := y) hy]
    have hWy : FiberBundle.extend F (D w) y = D w := by
      simp [extend_apply_self]
    rw [hWy]
    have happ := congrArg (fun L : F →L[ℝ] F => L w) hround
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hAcz : Ac z = a := by
    rw [← hz_eq]
    change CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (FiberBundle.extend F (D a)) (extChartAt I x₀ y) = a
    rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x₀) (σ := FiberBundle.extend F (D a))
      (y := y) hy]
    have hAy : FiberBundle.extend F (D a) y = D a := by
      simp [extend_apply_self]
    rw [hAy]
    have happ := congrArg (fun L : F →L[ℝ] F => L a) hround
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hU₀diff : MDiffAtTangentField U₀ z := by
    have hconst :
        U₀ = fun _ : F => u := by
      simpa [U₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (u : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
    have h :=
      FiberBundle.mdifferentiableAt_extend (𝓘(ℝ, F)) F
        (x := z)
        (show TangentSpace (𝓘(ℝ, F)) z from (show F from u))
    rw [CovariantDerivative.extend_model_space'
      (x := z)
      (w := (show TangentSpace (𝓘(ℝ, F)) z from (show F from u)))] at h
    exact h
  have hW₀diff : MDiffAtTangentField W₀ z := by
    have hconst :
        W₀ = fun _ : F => w := by
      simpa [W₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (w : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
    have h :=
      FiberBundle.mdifferentiableAt_extend (𝓘(ℝ, F)) F
        (x := z)
        (show TangentSpace (𝓘(ℝ, F)) z from (show F from w))
    rw [CovariantDerivative.extend_model_space'
      (x := z)
      (w := (show TangentSpace (𝓘(ℝ, F)) z from (show F from w)))] at h
    exact h
  have hUdiff : MDiffAtTangentField U y := by
    simpa [U, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F (D u))
  have hWdiff : MDiffAtTangentField W y := by
    simpa [W, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend I F (D w))
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hUcdiff : MDiffAtTangentField Uc z := by
    rw [← hz_eq]
    simpa [Uc, U, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := y) hy
        (by simpa [MDiffAtTangentField] using hUdiff)
  have hWcdiff : MDiffAtTangentField Wc z := by
    rw [← hz_eq]
    simpa [Wc, W, MDiffAtTangentField] using
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := y) hy
        (by simpa [MDiffAtTangentField] using hWdiff)
  have hA₀two :
      ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2
        (fun q : F =>
          (⟨q, A₀ q⟩ :
            TotalSpace F (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    have hconst :
        A₀ = fun _ : F => a := by
      simpa [A₀] using
        (CovariantDerivative.extend_model_space'
          (x := z) (w := (a : TangentSpace (𝓘(ℝ, F)) z)))
    rw [hconst]
    have h :=
      FiberBundle.contMDiffAt_extend' (k := 2) (𝓘(ℝ, F)) F
        (x := z)
        (show TangentSpace (𝓘(ℝ, F)) z from (show F from a))
    rw [CovariantDerivative.extend_model_space'
      (x := z)
      (w := (show TangentSpace (𝓘(ℝ, F)) z from (show F from a)))] at h
    exact h
  have hAtwo : ContMDiffAt I ((I).prod 𝓘(ℝ, F)) 2 (T% A) y := by
    simpa [A] using
      (FiberBundle.contMDiffAt_extend' (k := 2) I F (D a))
  have hActwo :
      ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2
        (fun q : F =>
          (⟨q, Ac q⟩ :
            TotalSpace F (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    rw [← hz_eq]
    simpa [Ac, A] using
      CovariantDerivative.chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
        («I» := I) x₀ hy hAtwo two_add_one_le_top
  let covC := GeodesicTransport.chartLeviCivita g x₀
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le two_le_top
  have hgChart1 :
      ContMDiff I ((I).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ))
        ((1 : ℕ∞ω) + 1)
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using hg2
  haveI hcovCdiff : CovariantDerivative.ContMDiffCovariantDerivative covC 1 := by
    change CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.chartLeviCivita
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu)
        x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)) 1
    exact CovariantDerivative.chartLeviCivita_contMDiff
      (χ := GeodesicTransport.cutoff (n := n) x₀)
      (G₀ := GeodesicTransport.backgroundMetric (n := n))
      (hG₀pos := GeodesicTransport.backgroundMetric_pos (n := n))
      (g := g.inner)
      (hgpos := fun y u hu => g.inner_pos y (v := u) hu)
      (x₀ := x₀)
      (hχ0 := GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (hχ1 := GeodesicTransport.cutoff_le_one (n := n) x₀)
      (hsupp := GeodesicTransport.cutoff_support_invertible (n := n) x₀)
      (k := 1)
      one_add_one_add_one_le_top
      (GeodesicTransport.cutoff_contDiff (n := n) x₀)
      (GeodesicTransport.cutoff_tsupport (n := n) x₀)
      hgChart1
  have hregA₀ : CovariantDerivative.DerivRegularAt covC A₀ z := by
    simpa [covC, A₀] using
      (CovariantDerivative.derivRegularAt_extend
        (cov := GeodesicTransport.chartLeviCivita g x₀)
        (x := z) (w := (a : TangentSpace (𝓘(ℝ, F)) z)))
  have hfst :
      CovariantDerivative.curvatureOp covC U₀ W₀ A₀ z =
        CovariantDerivative.curvatureOp covC Uc W₀ A₀ z :=
    curvatureOp_congr_fst_of_value_eq
      (cov := covC) (x := z) (X := U₀) (X' := Uc) (Y := W₀) (Z := A₀)
      hregA₀ hU₀diff hUcdiff hW₀diff (by rw [hU₀z, hUcz])
  have hsnd :
      CovariantDerivative.curvatureOp covC Uc W₀ A₀ z =
        CovariantDerivative.curvatureOp covC Uc Wc A₀ z :=
    curvatureOp_congr_snd_of_value_eq
      (cov := covC) (x := z) (X := Uc) (Y := W₀) (Y' := Wc) (Z := A₀)
      hregA₀ hUcdiff hW₀diff hWcdiff (by rw [hW₀z, hWcz])
  have hthird :
      CovariantDerivative.curvatureOp covC Uc Wc A₀ z =
        CovariantDerivative.curvatureOp covC Uc Wc Ac z :=
    CovariantDerivative.curvatureOp_congr_of_value_eq
      (cov := covC) (x := z) (X := Uc) (Y := Wc) (Z := A₀) (Z' := Ac)
      hA₀two hActwo (by rw [hA₀z, hAcz])
      (by simpa [MDiffAtTangentField] using hUcdiff)
      (by simpa [MDiffAtTangentField] using hWcdiff)
  have htransport :=
    chartLeviCivita_curvatureOp_chartTransported_extend_eq_chartTransported_curvatureOp_at
      (g := g) (x₀ := x₀) (y := y) hy hχoney (D u) (D w) (D a)
  calc
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) u)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) w)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := z) a)
        z =
      CovariantDerivative.curvatureOp covC U₀ W₀ A₀ z := by rfl
    _ = CovariantDerivative.curvatureOp covC Uc W₀ A₀ z := hfst
    _ = CovariantDerivative.curvatureOp covC Uc Wc A₀ z := hsnd
    _ = CovariantDerivative.curvatureOp covC Uc Wc Ac z := hthird
    _ =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita U W A) z := by
          have htransport_z := htransport
          rw [hz_eq] at htransport_z
          simpa [covC, U, W, A, Uc, Wc, Ac] using htransport_z
    _ =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z u))
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z w))
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z a))) z := by
          rfl

/-- The unconditional cutoff-one zone bridge, with no remaining bridge
hypothesis. -/
theorem chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp_zone
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt I x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := n) x₀ z' = 1)
    (u w a : F) :
    chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z u w a =
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (CovariantDerivative.curvatureOp g.leviCivita
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z u))
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z w))
          (FiberBundle.extend F
            (ChartCurvatureBridgeZone.chartInverseTangent (n := n) x₀ z a))) z := by
  rw [ChartCurvatureBridgeZone.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature_at
    (g := g) (x₀ := x₀) (z := z) u w a]
  exact chartLeviCivita_curvatureOp_const_eq_chartTransported_curvatureOp_zone
    (g := g) (x₀ := x₀) hz hχone u w a

section DimensionThree

variable {M3 : Type u}
variable [TopologicalSpace M3] [T2Space M3]
variable [ChartedSpace (ClosedSmoothModel 3) M3]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M3]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

/--
Cutoff-one zone Kulkarni-Nomizu identity for constant-curvature-one metrics,
with the rigid-5 bridge hypothesis discharged by field-choice naturality.
-/
theorem chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone
    (g : ClosedSmoothRiemannianMetric 3 M3)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M3) {z : E3} (hz : z ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (u w a b : E3) :
    CovariantDerivative.chartMetric g.inner x₀ z
        (chartCurvatureOf
          (GeodesicTransport.chartChristoffelField g x₀) z u w a) b =
      -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          (fun p q : E3 => CovariantDerivative.chartMetric g.inner x₀ z p q)
          u w a b := by
  exact
    ChartCurvatureBridgeZone.chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone_of_bridge
      (g := g) hcurv (x₀ := x₀) (z := z) hz u w a b
      (chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp_zone
        (g := g) (x₀ := x₀) hz hχone u w a)

end DimensionThree

end ChartCurvatureBridgeZoneClose
end Poincare
