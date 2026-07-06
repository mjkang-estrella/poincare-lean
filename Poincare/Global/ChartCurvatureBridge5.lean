import Poincare.Global.ChartCurvatureBridge4

/-!
# Chart curvature bridge, outer transport glue

This module contains the outer chart-transport/locality glue left after
`ChartCurvatureBridge4`.  The lemmas below are intentionally phrased for
arbitrary local tangent fields: the canonical-`extend` curvature assembly is
then a specialization of these transport identities.
-/

noncomputable section

open Bundle Filter Set FiberBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

namespace ChartCurvatureBridge5

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
Inverse-chart transport is germ-local in the transported manifold field.
-/
theorem chartTransportedLeviCivitaSection_congr_of_eventuallyEq
    {x₀ : M} {σ τ : Π y : M, TM y}
    (hστ : σ =ᶠ[𝓝 x₀] τ) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ := by
  have hleft :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hστ' :
      σ =ᶠ[𝓝 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))] τ := by
    simpa [hleft] using hστ
  have hpre :=
    (continuousAt_extChartAt_symm x₀).eventually hστ'
  filter_upwards [hpre] with z hz
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  exact congrArg
    ((mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I) z).inverse)
    hz

/--
Source-point version of transported-section germ locality.
-/
theorem chartTransportedLeviCivitaSection_congr_of_eventuallyEq_at
    {x₀ y : M} (hy : y ∈ (extChartAt I x₀).source)
    {σ τ : Π y : M, TM y} (hστ : σ =ᶠ[𝓝 y] τ) :
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ
      =ᶠ[𝓝 (extChartAt I x₀ y)]
    CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ := by
  have hys : y ∈ (chartAt F x₀).source := by
    rwa [extChartAt_source] at hy
  have hleft :
      (chartAt F x₀).symm ((chartAt F x₀) y) = y :=
    (chartAt F x₀).left_inv hys
  have hστ' :
      σ =ᶠ[𝓝 ((chartAt F x₀).symm ((chartAt F x₀) y))] τ := by
    simpa [hleft] using hστ
  have hpre :=
    (continuousAt_extChartAt_symm' hy).eventually hστ'
  filter_upwards [hpre] with z hz
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply,
    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
  exact congrArg
    ((mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I) z).inverse)
    hz

/--
The transported chart Levi-Civita hom is germ-local in its field slot at any
source point of the anchor chart.
-/
theorem chartTransportedLeviCivitaHom_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) {x₀ y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    {σ τ : Π y : M, TM y}
    (hσ : MDiffAtTangentField σ y) (hτ : MDiffAtTangentField τ y)
    (hστ : σ =ᶠ[𝓝 y] τ) :
    CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        σ y =
      CovariantDerivative.chartTransportedLeviCivitaHom
        (GeodesicTransport.cutoff (n := n) x₀)
        (GeodesicTransport.backgroundMetric (n := n))
        (GeodesicTransport.backgroundMetric_pos (n := n))
        g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (GeodesicTransport.cutoff_nonneg (n := n) x₀)
        (GeodesicTransport.cutoff_le_one (n := n) x₀)
        (GeodesicTransport.cutoff_support_invertible (n := n) x₀)
        τ y := by
  ext v
  rw [CovariantDerivative.chartTransportedLeviCivitaHom_apply
    (χ := GeodesicTransport.cutoff (n := n) x₀)
    (G₀ := GeodesicTransport.backgroundMetric (n := n))
    (hG₀pos := GeodesicTransport.backgroundMetric_pos (n := n))
    (g := g.inner) (hgpos := fun y u hu => g.inner_pos y (v := u) hu)
    (x₀ := x₀)
    (hχ0 := GeodesicTransport.cutoff_nonneg (n := n) x₀)
    (hχ1 := GeodesicTransport.cutoff_le_one (n := n) x₀)
    (hsupp := GeodesicTransport.cutoff_support_invertible (n := n) x₀)
    (σ := σ) hy v]
  rw [CovariantDerivative.chartTransportedLeviCivitaHom_apply
    (χ := GeodesicTransport.cutoff (n := n) x₀)
    (G₀ := GeodesicTransport.backgroundMetric (n := n))
    (hG₀pos := GeodesicTransport.backgroundMetric_pos (n := n))
    (g := g.inner) (hgpos := fun y u hu => g.inner_pos y (v := u) hu)
    (x₀ := x₀)
    (hχ0 := GeodesicTransport.cutoff_nonneg (n := n) x₀)
    (hχ1 := GeodesicTransport.cutoff_le_one (n := n) x₀)
      (hsupp := GeodesicTransport.cutoff_support_invertible (n := n) x₀)
    (σ := τ) hy v]
  unfold CovariantDerivative.chartTransportedLeviCivitaValueAt
    CovariantDerivative.chartTransportedLeviCivitaModelValue
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hσc :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _)))
        (extChartAt I x₀ y) :=
    CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
      («I» := I) (x₀ := x₀) (y := y) hy
      (by simpa [MDiffAtTangentField] using hσ)
  have hτc :
      MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
        (fun z : F =>
          (⟨z, CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ z⟩ :
            TotalSpace F
              (TangentSpace (𝓘(ℝ, F)) : F → Type _)))
        (extChartAt I x₀ y) :=
    CovariantDerivative.chartTransportedLeviCivitaSection_mdiffAt_apply_chart
      («I» := I) (x₀ := x₀) (y := y) hy
      (by simpa [MDiffAtTangentField] using hτ)
  have hsec :=
    chartTransportedLeviCivitaSection_congr_of_eventuallyEq_at
      (x₀ := x₀) (y := y) hy hστ
  have hcov :
      (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
          (extChartAt I x₀ y) =
        (GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ)
          (extChartAt I x₀ y) := by
    apply (GeodesicTransport.chartLeviCivita g x₀).isCovariantDerivativeOnUniv
      |>.congr_of_eventuallyEq hσc hτc Filter.univ_mem
    exact hsec
  change
    (mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I)
        (extChartAt I x₀ y))
      (((GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
          (extChartAt I x₀ y))
        ((mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y) v)) =
    (mfderivWithin 𝓘(ℝ, F) I ((extChartAt I x₀).symm) (Set.range I)
        (extChartAt I x₀ y))
      (((GeodesicTransport.chartLeviCivita g x₀)
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ)
          (extChartAt I x₀ y))
        ((mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y) v))
  rw [hcov]

/--
Pointwise naturality of the transported chart Levi-Civita hom.  Pulling the
manifold-side transported value through the anchor chart agrees with applying
the chart Levi-Civita connection to the pulled-back field.
-/
theorem chartTransportedLeviCivitaSection_hom_apply_chart
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
        (extChartAt I x₀ y) =
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
        (extChartAt I x₀ y)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
          (extChartAt I x₀ y)) := by
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
          σ y (X y))
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
        σ y (X y)) =
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
    (σ := σ) hy (X y)]
  unfold CovariantDerivative.chartTransportedLeviCivitaValueAt
    CovariantDerivative.chartTransportedLeviCivitaModelValue
  rw [CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
    («I» := I) (x₀ := x₀) (σ := X) (y := y) hy]
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
          (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
          (extChartAt I x₀ y)
          (mfderiv I 𝓘(ℝ, F) (extChartAt I x₀) y (X y)))) hround
  simpa [ContinuousLinearMap.comp_apply] using happ

/--
Germ form of `chartTransportedLeviCivitaSection_hom_apply_chart` at the anchor.
-/
theorem chartTransportedLeviCivitaSection_hom_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M}
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
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    (fun z : F =>
      (GeodesicTransport.chartLeviCivita g x₀)
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ) z
        (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X z)) := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds
      (mem_extChartAt_target x₀)] with z hz
  have hy : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hz_eq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hpoint :=
    chartTransportedLeviCivitaSection_hom_apply_chart
      (g := g) (x₀ := x₀) (y := (extChartAt I x₀).symm z) hy σ X
  rw [hz_eq] at hpoint
  simpa using hpoint

end ChartCurvatureBridge5

end Poincare
