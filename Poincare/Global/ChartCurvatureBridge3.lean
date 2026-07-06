import Poincare.Global.ChartCurvatureBridge2
import Poincare.Global.ScalarVariation

/-!
# Chart curvature bridge, final transport frontier

This module records theorem-bearing pieces for the last chart-curvature
transport step.  The bridge through `ChartCurvatureBridge2` is already
model-side; the remaining work is to transport iterated Levi-Civita
applications through the anchor chart.

The first lemma below packages the basic germ fact needed for both inner
covariant-derivative fields: canonical manifold extensions become constant
model fields under the inverse-chart transport at the anchor.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge3

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "F" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-
Near the anchor image, inverse-chart transport sends the canonical manifold
extension of `p` to the constant model tangent field `p`.

This is the germ form of
`chartTransportedLeviCivitaSection_extend_apply_chart`; the open chart target
turns the pointwise chart statement into an eventual equality on model space.
-/
omit [T2Space M] in
theorem chartTransportedLeviCivitaSection_extend_eventuallyEq_const
    {x₀ : M} (p : TM x₀) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
        (FiberBundle.extend F p)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    (fun _ : F => p) := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds
      (mem_extChartAt_target x₀)] with z hz
  have hy : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hz_eq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hval :=
    chartTransportedLeviCivitaSection_extend_apply_chart
      (x := x₀) (y := (extChartAt I x₀).symm z) hy p
  rw [hz_eq] at hval
  simpa using hval

/--
For a canonical extension, the transported chart hom agrees near the anchor
with the closed Levi-Civita connection.

This is the local-differentiability specialization of
`chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one`; it avoids the
global smoothness hypothesis in `GeodesicTransport.chartLeviCivita_eventuallyEq_closed`,
which canonical `extend` fields do not provide globally.
-/
theorem chartTransportedLeviCivitaHom_extend_eventuallyEq_closed
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (p : TM x₀) :
    (fun y : M =>
      (⟨y,
        CovariantDerivative.chartTransportedLeviCivitaHom
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n))
          (GeodesicTransport.backgroundMetric_pos (n := n))
          g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (GeodesicTransport.cutoff_nonneg (n := n) x₀)
          (GeodesicTransport.cutoff_le_one (n := n) x₀)
          (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
          (FiberBundle.extend F p) y⟩ :
        TotalSpace (F →L[ℝ] F) (fun y : M => TM y →L[ℝ] TM y)))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      (⟨y, g.leviCivita (FiberBundle.extend F p) y⟩ :
        TotalSpace (F →L[ℝ] F) (fun y : M => TM y →L[ℝ] TM y))) := by
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
  have hbl :
      Differentiable ℝ
        (CovariantDerivative.blendedChartMetric
          (GeodesicTransport.cutoff (n := n) x₀)
          (GeodesicTransport.backgroundMetric (n := n)) g.inner x₀) :=
    hblend.differentiable (by norm_num)
  let oneLocus : Set F :=
    {z | ∀ᶠ z' in 𝓝 z, GeodesicTransport.cutoff (n := n) x₀ z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ 𝓝 (extChartAt I x₀ x₀) :=
    hopen.mem_nhds (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x₀)
  have hcont : ContinuousAt (fun y : M => extChartAt I x₀ y) x₀ := by
    simpa only using (continuousAt_extChartAt x₀)
  have hone_pre : (extChartAt I x₀) ⁻¹' oneLocus ∈ 𝓝 x₀ :=
    hcont.preimage_mem_nhds hone_mem
  have hsource : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
    extChartAt_source_mem_nhds x₀
  obtain ⟨s, hs, hdiff⟩ :=
    FiberBundle.exists_mdifferentiableOn_extend I F p
  rcases mem_nhds_iff.mp hs with ⟨t, hts, htopen, hxt⟩
  filter_upwards [hsource, hone_pre, htopen.mem_nhds hxt] with y hy hyloc hyt
  have hsy : s ∈ 𝓝 y := mem_nhds_iff.mpr ⟨t, hts, htopen, hyt⟩
  have hσy : MDiffAtTangentField (FiberBundle.extend F p) y :=
    (hdiff y (hts hyt)).mdifferentiableAt hsy
  have hclosed :=
    LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
      g (GeodesicTransport.cutoff (n := n) x₀)
      (GeodesicTransport.backgroundMetric (n := n))
      (GeodesicTransport.backgroundMetric_pos (n := n)) x₀
      (GeodesicTransport.cutoff_nonneg (n := n) x₀)
      (GeodesicTransport.cutoff_le_one (n := n) x₀)
      (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
      hbl (GeodesicTransport.backgroundMetric_symm (n := n)) hy hyloc hσy
  simpa [ClosedSmoothRiemannianMetric.leviCivita] using hclosed

end ChartCurvatureBridge3

end Poincare
