import Poincare.Global.Curvature
import Poincare.Global.GeodesicChart

/-!
# Chart-side geodesic transport for the closed Levi-Civita connection

This file packages the chart-level Christoffel field used by the geodesic
ODE from `Poincare.Global.GeodesicChart`.  The coefficients are the
Christoffel one-form of the already existing transported chart
Levi-Civita connection.  Near the anchor chart center, the transported
connection agrees with `g.leviCivita` by the bridge in
`LeviCivitaTransport`.
-/

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare

universe u

/--
Finite-dimensional `ContDiffAt` lifting for continuous-linear-map-valued
fields from their values on fixed vectors.
-/
theorem contDiffAt_clm_of_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞ω} {Φ : E → E →L[ℝ] F} {x : E}
    (h : ∀ w : E, ContDiffAt ℝ m (fun y ↦ Φ y w) x) :
    ContDiffAt ℝ m Φ x := by
  set bE := Module.finBasis ℝ E with hbE
  set coordC : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i ↦ LinearMap.toContinuousLinearMap (bE.coord i) with hcoord
  have hrepr : ∀ ρ : E →L[ℝ] F, ρ = ∑ i, (coordC i).smulRight (ρ (bE i)) := by
    intro ρ
    ext w
    have hw := bE.sum_repr w
    conv_lhs => rw [← hw]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show coordC i w = bE.coord i w from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun y ↦ ∑ i, (coordC i).smulRight (Φ y (bE i)) := by
    funext y
    exact hrepr (Φ y)
  rw [hfun]
  apply ContDiffAt.sum
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ E F (coordC i)).contDiff.contDiffAt).comp
    x (h (bE i))

namespace GeodesicTransport

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

section Cutoff

variable (x₀ : M)

/-- The standard Euclidean background metric used to globalize the chart metric. -/
def backgroundMetric : E →L[ℝ] E →L[ℝ] ℝ :=
  innerSL ℝ

theorem backgroundMetric_pos : ∀ v : E, v ≠ 0 → 0 < backgroundMetric (n := n) v v := by
  intro v hv
  change 0 < ((innerSL ℝ) v) v
  rw [innerSL_apply_apply]
  exact (real_inner_self_pos).2 hv

theorem backgroundMetric_symm : ∀ v w : E,
    backgroundMetric (n := n) v w = backgroundMetric (n := n) w v := by
  intro v w
  change ((innerSL ℝ) v) w = ((innerSL ℝ) w) v
  rw [innerSL_apply_apply, innerSL_apply_apply]
  exact real_inner_comm w v

/-- A chosen cutoff supported in the anchor chart target and equal to `1` near the anchor. -/
def cutoff : E → ℝ :=
  Classical.choose (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)

omit [T2Space M] in
theorem cutoff_contDiff : ContDiff ℝ ∞ (cutoff (n := n) x₀) :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).1

omit [T2Space M] in
theorem cutoff_nonneg : ∀ z : E, 0 ≤ cutoff (n := n) x₀ z :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.1

omit [T2Space M] in
theorem cutoff_le_one : ∀ z : E, cutoff (n := n) x₀ z ≤ 1 :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.1

omit [T2Space M] in
theorem cutoff_tsupport :
    tsupport (cutoff (n := n) x₀) ⊆ (extChartAt I x₀).target :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.2.1

omit [T2Space M] in
theorem cutoff_eventuallyEq_one :
    ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀), cutoff (n := n) x₀ z = 1 :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.2.2.1

omit [T2Space M] in
/-- If the anchor chart target is the whole model space, the chosen blending
cutoff is canonically the constant function `1`. -/
theorem cutoff_eq_one_of_target_eq_univ
    (htarget : (extChartAt I x₀).target = Set.univ) :
    cutoff (n := n) x₀ = fun _ : E ↦ (1 : ℝ) :=
  (Classical.choose_spec
    (@CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀)).2.2.2.2.2
      htarget

omit [T2Space M] in
theorem cutoff_support_invertible (z : E) (hz : cutoff (n := n) x₀ z ≠ 0) :
    (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) z).IsInvertible :=
  isInvertible_mfderivWithin_extChartAt_symm
    (cutoff_tsupport (n := n) x₀
      (subset_tsupport (cutoff (n := n) x₀) (Function.mem_support.mpr hz)))

end Cutoff

variable (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)

/-- The chart Levi-Civita connection built by the existing transport machinery. -/
def chartLeviCivita :
    CovariantDerivative 𝓘(ℝ, E) E (TangentSpace 𝓘(ℝ, E) : E → Type _) :=
  CovariantDerivative.chartLeviCivita (cutoff (n := n) x₀)
    (backgroundMetric (n := n)) (backgroundMetric_pos (n := n))
    g.inner (fun y u hu => g.inner_pos y (v := u) hu)
    x₀ (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
    (cutoff_support_invertible (n := n) x₀)

/--
The chart-side Christoffel field for `g.leviCivita` at the anchor chart.

This is the Christoffel one-form of `chartLeviCivita`; by
`chartLeviCivita_eventuallyEq_closed`, the transported chart connection
agrees near the anchor with the canonical closed Levi-Civita connection.
The first vector slot is the section-value slot and the second is the
direction slot, matching `christoffelOneForm`.
-/
def chartChristoffelField : E → E →L[ℝ] E →L[ℝ] E :=
  fun z =>
    CovariantDerivative.christoffelOneForm
      (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (CovariantDerivative.chartBilin_nondegenerate
        (cutoff (n := n) x₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
        (cutoff_support_invertible (n := n) x₀))
      z

/--
The transported chart connection defined by the chosen cutoff agrees near the
anchor with the canonical closed Levi-Civita connection.
-/
theorem chartLeviCivita_eventuallyEq_closed
    {σ : Π y : M, TM y}
    (hσ : ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) Set.univ) :
    (fun y : M =>
      (⟨y,
        CovariantDerivative.chartTransportedLeviCivitaHom
          (cutoff (n := n) x₀) (backgroundMetric (n := n))
          (backgroundMetric_pos (n := n)) g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
          (cutoff_support_invertible (n := n) x₀) σ y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      (⟨y, g.leviCivita σ y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y))) := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend :
      ContDiff ℝ 2
        (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀) :=
    CovariantDerivative.contDiff_blendedChartMetric
      (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
      htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
      (cutoff_tsupport (n := n) x₀) hg2
  have hbl :
      Differentiable ℝ
        (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀) :=
    hblend.differentiable (by norm_num)
  simpa [ClosedSmoothRiemannianMetric.leviCivita] using
    LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed
      g (cutoff (n := n) x₀) (backgroundMetric (n := n))
      (backgroundMetric_pos (n := n)) x₀
      (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
      (cutoff_support_invertible (n := n) x₀) hbl
      (backgroundMetric_symm (n := n)) (cutoff_eventuallyEq_one (n := n) x₀)
      hσ

/- The chart Christoffel field is `C¹` at the anchor chart image. -/
omit [T2Space M] in
theorem chartChristoffelField_contDiffAt :
    ContDiffAt ℝ 1 (chartChristoffelField g x₀) (extChartAt I x₀ x₀) := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend :
      ContDiff ℝ (1 + 1)
        (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀) := by
    simpa using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
        htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
        (cutoff_tsupport (n := n) x₀) hg2)
  apply contDiffAt_clm_of_apply
  intro u
  apply contDiffAt_clm_of_apply
  intro v
  simpa [chartChristoffelField] using
    (CovariantDerivative.contDiffAt_christoffelAt
      (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (k := 1) (x := extChartAt I x₀ x₀)
      hblend
      (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (CovariantDerivative.chartBilin_nondegenerate
        (cutoff (n := n) x₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
        (cutoff_support_invertible (n := n) x₀))
      (fun z v w => rfl) v u)

/- The chart geodesic flow field associated to `g.leviCivita` is `C¹` at initial data. -/
omit [T2Space M] in
theorem geodesicFlowField_chartChristoffelField_contDiffAt (v₀ : E) :
    ContDiffAt ℝ 1
      (geodesicFlowField (chartChristoffelField g x₀))
      (extChartAt I x₀ x₀, v₀) :=
  contDiffAt_geodesicFlowField
    (Γ := chartChristoffelField g x₀)
    (p₀ := (extChartAt I x₀ x₀, v₀))
    (chartChristoffelField_contDiffAt g x₀)

/-
Local chart geodesic existence through `x₀` with initial chart velocity `v₀`.
The solution `γ` is the first-order chart curve `(position, velocity)`, and
the pulled-back manifold curve is `t ↦ (extChartAt I x₀).symm (γ t).1`.
-/
omit [T2Space M] in
theorem exists_local_geodesic_chart_solution (v₀ : E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = (extChartAt I x₀ x₀, v₀) ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ
          (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) ∧
      (let c : ℝ → M := fun t => (extChartAt I x₀).symm (γ t).1
       c 0 = x₀ ∧
        ∀ᶠ t in 𝓝 (0 : ℝ),
          (γ t).1 ∈ (extChartAt I x₀).target ∧
            c t ∈ (extChartAt I x₀).source) := by
  rcases exists_geodesicFlowField_solution
      (Γ := chartChristoffelField g x₀)
      (p₀ := (extChartAt I x₀ x₀, v₀))
      (chartChristoffelField_contDiffAt g x₀) with
    ⟨ε, hε, γ, hγ0, hγder⟩
  refine ⟨ε, hε, γ, hγ0, hγder, ?_⟩
  let c : ℝ → M := fun t => (extChartAt I x₀).symm (γ t).1
  have hzero_mem : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have hγder0 :
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ 0)) 0 :=
    hγder 0 hzero_mem
  have hpos_cont : ContinuousAt (fun t : ℝ => (γ t).1) 0 :=
    hγder0.continuousAt.fst
  have htarget₀ :
      (γ 0).1 ∈ (extChartAt I x₀).target := by
    simp [hγ0]
  have htarget :
      ∀ᶠ t in 𝓝 (0 : ℝ), (γ t).1 ∈ (extChartAt I x₀).target :=
    hpos_cont.preimage_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds htarget₀)
  have hc0 : c 0 = x₀ := by
    simp [c, hγ0]
  refine ⟨hc0, ?_⟩
  filter_upwards [htarget] with t ht
  exact ⟨ht, (extChartAt I x₀).map_target ht⟩

end GeodesicTransport

end Poincare
