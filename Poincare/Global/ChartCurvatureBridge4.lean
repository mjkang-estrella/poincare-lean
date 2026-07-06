import Poincare.Global.ChartCurvatureBridge3
import Poincare.Global.RoundSphereCurvature

/-!
# Chart curvature bridge, inner-field naturality

This module continues the chart-curvature bridge by proving the missing germ
for the inner covariant-derivative field.  The remaining curvature-level
assembly is recorded in the worker report in this task.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge4

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
Pointwise form of inner-field naturality in the anchor chart.

After reading the manifold-side transported inner derivative through the
anchor chart, one obtains the chart Levi-Civita derivative of the transported
field in the transported direction.
-/
theorem chartTransportedLeviCivitaSection_inner_apply_chart
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source) (a w : TM x₀) :
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
            (FiberBundle.extend F a) y (FiberBundle.extend F w y))
        (extChartAt I x₀ y) =
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F a))
        (extChartAt I x₀ y)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F w) (extChartAt I x₀ y)) := by
  have hsec :=
    CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
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
          (FiberBundle.extend F a) y (FiberBundle.extend F w y))
      (y := y) hy
  rw [hsec]
  change (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y)
      (CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        (FiberBundle.extend F a) y (FiberBundle.extend F w y)) =
    _
  rw [CovariantDerivative.chartTransportedLeviCivitaHom_apply
    (χ := GeodesicTransport.cutoff (n := n) x₀)
    (G₀ := GeodesicTransport.backgroundMetric (n := n))
    (hG₀pos := GeodesicTransport.backgroundMetric_pos (n := n))
    (g := g.inner) (hgpos := fun y u hu => g.inner_pos y (v := u) hu)
    (x₀ := x₀)
    (hχ0 := GeodesicTransport.cutoff_nonneg (n := n) x₀)
    (hχ1 := GeodesicTransport.cutoff_le_one (n := n) x₀)
    (hsupp := GeodesicTransport.cutoff_support_invertible (n := n) x₀)
    (σ := FiberBundle.extend F a) hy (FiberBundle.extend F w y)]
  unfold CovariantDerivative.chartTransportedLeviCivitaValueAt
    CovariantDerivative.chartTransportedLeviCivitaModelValue
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
    («I» := I) (x₀ := x₀) (σ := FiberBundle.extend F w) (y := y) hy]
  have hround :
      (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y).comp
        (mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm)
          (Set.range I) (extChartAt I x₀ y)) =
        ContinuousLinearMap.id ℝ F := by
    simpa using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        («I» := I) (x := x₀) hy
  have happ := congrArg
    (fun L : F →L[ℝ] F =>
      L
        ((GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (FiberBundle.extend F a))
          (extChartAt I x₀ y)
          (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y
            (FiberBundle.extend F w y)))) hround
  simpa [ContinuousLinearMap.comp_apply] using happ

/--
The inverse-chart transport of the manifold-side inner derivative field is
germ-equal to the model-side chart Levi-Civita derivative of the corresponding
canonical model extensions.
-/
theorem chartTransportedLeviCivitaSection_inner_extend_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (a w : TM x₀) :
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
            (FiberBundle.extend F a) y (FiberBundle.extend F w y))
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    (fun z : F =>
      (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) a)
        z
        (FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) w z)) := by
  obtain ⟨s, hs, hdiff⟩ :=
    FiberBundle.exists_mdifferentiableOn_extend I F a
  rcases mem_nhds_iff.mp hs with ⟨t, hts, htopen, hxt⟩
  have hpre :
      ((extChartAt I x₀).symm) ⁻¹' t ∈ 𝓝 (extChartAt I x₀ x₀) :=
    extChartAt_preimage_mem_nhds («I» := I) (x := x₀)
      (htopen.mem_nhds hxt)
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds
      (mem_extChartAt_target x₀), hpre] with z hz hzt
  have hy : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hz_eq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hpoint :=
    chartTransportedLeviCivitaSection_inner_apply_chart
      (g := g) (x₀ := x₀) (y := (extChartAt I x₀).symm z) hy a w
  rw [hz_eq] at hpoint
  have ha :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F a) z = a := by
    have h :=
      chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀)
        (y := (extChartAt I x₀).symm z) hy a
    rw [hz_eq] at h
    exact h
  have hw :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F w) z = w := by
    have h :=
      chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀)
        (y := (extChartAt I x₀).symm z) hy w
    rw [hz_eq] at h
    exact h
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hσc_diff :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            CovariantDerivative.chartTransportedLeviCivitaSection x₀
              (FiberBundle.extend F a) z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    have h :=
      CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
        («I» := I) (x₀ := x₀) (y := (extChartAt I x₀).symm z) hy
        ((hdiff ((extChartAt I x₀).symm z) (hts hzt)).mdifferentiableAt
          (mem_nhds_iff.mpr ⟨t, hts, htopen, hzt⟩))
    rw [hz_eq] at h
    exact h
  have hmodel_a_diff :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z,
            FiberBundle.extend
              (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
              F (x := extChartAt I x₀ x₀) a z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _))) z := by
    rw [CovariantDerivative.extend_model_space'
      (x := extChartAt I x₀ x₀)
      (w := (a : TangentSpace (𝓘(ℝ, F)) (extChartAt I x₀ x₀)))]
    have h :=
      FiberBundle.mdifferentiableAt_extend (𝓘(ℝ, F)) F
        (x := z)
        (show TangentSpace (𝓘(ℝ, F)) z from (show F from a))
    rw [CovariantDerivative.extend_model_space'
      (x := z)
      (w := (show TangentSpace (𝓘(ℝ, F)) z from (show F from a)))] at h
    exact h
  have hmodel_a :
      FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) a =
        fun _ : F => a := by
    simpa using
      (CovariantDerivative.extend_model_space'
        (x := extChartAt I x₀ x₀)
        (w := (a : TangentSpace (𝓘(ℝ, F)) (extChartAt I x₀ x₀))))
  have hmodel_w :
      FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) w =
        fun _ : F => w := by
    simpa using
      (CovariantDerivative.extend_model_space'
        (x := extChartAt I x₀ x₀)
        (w := (w : TangentSpace (𝓘(ℝ, F)) (extChartAt I x₀ x₀))))
  have hsection_a_local :
      CovariantDerivative.chartTransportedLeviCivitaSection x₀
          (FiberBundle.extend F a)
        =ᶠ[𝓝 z]
      FiberBundle.extend (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
        F (x := extChartAt I x₀ x₀) a := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hz] with z' hz'
    have hy' : (extChartAt I x₀).symm z' ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hz'
    have hz'_eq : extChartAt I x₀ ((extChartAt I x₀).symm z') = z' :=
      (extChartAt I x₀).right_inv hz'
    have hval :=
      chartTransportedLeviCivitaSection_extend_apply_chart
        (n := n) (M := M) (x := x₀)
        (y := (extChartAt I x₀).symm z') hy' a
    rw [hz'_eq] at hval
    rw [hmodel_a]
    exact hval
  have hcov_a :
      (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀
            (FiberBundle.extend F a)) z =
        (GeodesicTransport.chartLeviCivita g x₀)
          (FiberBundle.extend
            (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
            F (x := extChartAt I x₀ x₀) a) z := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hσc_diff hmodel_a_diff Filter.univ_mem
    exact hsection_a_local
  rw [hpoint, hcov_a, hw, hmodel_w]

end ChartCurvatureBridge4

end Poincare
