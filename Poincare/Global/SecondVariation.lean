import Poincare.Global.GeodesicLinearized

/-!
# Second variation opener for chart geodesic flows

This module starts the second-order smooth-dependence chain at the ODE level.
The augmented state is a first-order geodesic state together with a first
variation.  Its vector field is `(F p, D F p ψ)`, and the second-variation
coefficient is the Fréchet linearization of that augmented vector field.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The augmented first-variation system for a chart geodesic vector field.

For `p = (γ, γ')` and `ψ = (J, J')`, this is the combined ODE
`p' = F p`, `ψ' = D F p ψ`.
-/
def augmentedGeodesicFlowField
    (Γ : E → E →L[ℝ] E →L[ℝ] E) :
    (E × E) × (E × E) → (E × E) × (E × E) :=
  fun z ↦
    (geodesicFlowField Γ z.1,
      linearizedGeodesicFlowOperator Γ z.1 z.2)

/--
The linear coefficient for the second-variation equation along an augmented
state.  This is the linearization of `(p, ψ) ↦ (F p, D F p ψ)`, hence it
contains the `D²F` terms, equivalently the `DΓ`/`D²Γ` terms for the geodesic
field.
-/
def secondVariationFlowOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (z : (E × E) × (E × E)) :
    ((E × E) × (E × E)) →L[ℝ] ((E × E) × (E × E)) :=
  fderiv ℝ (augmentedGeodesicFlowField Γ) z

/-- The time-dependent second-variation linear ODE along an augmented curve. -/
def secondVariationFlowFieldAlong
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (ζ : ℝ → (E × E) × (E × E)) :
    ℝ → ((E × E) × (E × E)) → ((E × E) × (E × E)) :=
  fun t ξ ↦ secondVariationFlowOperator Γ (ζ t) ξ

namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "X" => ClosedSmoothModel n

omit [T2Space M] in
/--
Picard-Lindelöf package for the chart-Christoffel second-variation linear ODE
along a continuous augmented curve.

The proof first derives `C²` regularity of the chart-Christoffel geodesic flow
from the smooth blended metric.  Therefore the augmented field
`(p, ψ) ↦ (F p, D F p ψ)` is `C¹`, and its derivative is a continuous
time-dependent family of linear maps after composition with `ζ`.  The existing
generic linear-ODE PL package then supplies the local bounded-coefficient data.
-/
theorem exists_isPicardLindelof_chartChristoffel_secondVariation_linearODE
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → (X × X) × (X × X)} (hζ : Continuous ζ)
    (ξ₀ : (X × X) × (X × X)) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ a r L K : ℝ≥0, 0 < r ∧
      IsPicardLindelof
        (fun t ξ ↦
          secondVariationFlowFieldAlong (chartChristoffelField g x₀) ζ t ξ)
        (tmin := -ε) (tmax := ε)
        ⟨(0 : ℝ), by constructor <;> linarith⟩ ξ₀ a r L K := by
  let Γ : X → X →L[ℝ] X →L[ℝ] X := chartChristoffelField g x₀
  have hΓ : ContDiff ℝ 2 Γ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hthree_le_top : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hthree_add_one_le_top : (3 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
      rw [show (3 : ℕ∞ω) + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hg3 :
        ContMDiff I ((I).prod 𝓘(ℝ, X →L[ℝ] X →L[ℝ] ℝ)) 3
          (fun y : M =>
            (⟨y, g.inner y⟩ :
              TotalSpace (X →L[ℝ] X →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
      simpa using g.contMDiff_inner.of_le hthree_le_top
    have hblend :
        ContDiff ℝ (2 + 1)
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀) := by
      simpa using
        (CovariantDerivative.contDiff_blendedChartMetric
          (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
          hthree_add_one_le_top (cutoff_contDiff (n := n) x₀)
          (cutoff_tsupport (n := n) x₀) hg3)
    apply contDiffAt_clm_of_apply
    intro u
    apply contDiffAt_clm_of_apply
    intro v
    simpa [Γ, chartChristoffelField] using
      (CovariantDerivative.contDiffAt_christoffelAt
        (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (k := 2) (x := z)
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
  have hF : ContDiff ℝ 2 (geodesicFlowField Γ) := by
    have hp : ContDiff ℝ 2 (fun p : X × X ↦ p.1) := contDiff_fst
    have hv : ContDiff ℝ 2 (fun p : X × X ↦ p.2) := contDiff_snd
    have hΓp : ContDiff ℝ 2 (fun p : X × X ↦ Γ p.1) := hΓ.comp hp
    have hΓpv : ContDiff ℝ 2 (fun p : X × X ↦ Γ p.1 p.2) :=
      hΓp.clm_apply hv
    have hΓpvv : ContDiff ℝ 2 (fun p : X × X ↦ Γ p.1 p.2 p.2) :=
      hΓpv.clm_apply hv
    simpa [geodesicFlowField, Γ] using hv.prodMk hΓpvv.neg
  let F : X × X → X × X := geodesicFlowField Γ
  have hbase : ContDiff ℝ 1 (fun z : (X × X) × (X × X) ↦ F z.1) := by
    exact (hF.of_le (by norm_num)).comp contDiff_fst
  have hlin :
      ContDiff ℝ 1
        (fun z : (X × X) × (X × X) ↦
          (fderiv ℝ F z.1 : (X × X) →L[ℝ] (X × X)) z.2) := by
    simpa [F] using
      (hF.contDiff_fderiv_apply (m := 1) (by norm_num))
  have haug : ContDiff ℝ 1 (augmentedGeodesicFlowField Γ) := by
    simpa [augmentedGeodesicFlowField, linearizedGeodesicFlowOperator, F, Γ] using
      hbase.prodMk hlin
  simpa [Γ] using
    exists_isPicardLindelof_continuous_linearODE
      (A := fun t ↦ secondVariationFlowOperator Γ (ζ t))
      (by
        simpa [secondVariationFlowOperator] using
          (haug.continuous_fderiv (by norm_num)).comp hζ)
      ξ₀

end GeodesicTransport

end Poincare
