import Poincare.Global.AugmentedC1

/-!
# Flow smoothness mining boundary

Mathlib's pinned ODE exports provide local-flow existence, uniqueness support,
continuity, and Lipschitz dependence in initial data, but not a ready-made
`ContDiff` smooth-dependence theorem for Picard-Lindelöf flows in initial
conditions.

This module therefore starts the third-variation fallback by exporting the next
regularity layer for the augmented geodesic/first-variation vector field: the
field is `C2` on model space, hence Lipschitz on compact closed-ball tubes.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
The chart-Christoffel augmented geodesic/first-variation field is `C2`, and
therefore Lipschitz on every compact closed-ball tube.

This is the first concrete input for the third-variation replay after the
pinned Mathlib ODE search did not provide `ContDiff` smooth dependence of
Picard-Lindelöf flows in initial conditions.
-/
theorem exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (p : (E × E) × (E × E)) (a : ℝ) :
    ContDiff ℝ 2
        (augmentedGeodesicFlowField (chartChristoffelField g x₀)) ∧
      ∃ K : ℝ≥0,
        LipschitzOnWith K
          (augmentedGeodesicFlowField (chartChristoffelField g x₀))
          (closedBall p (a + 1)) := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  have hΓ : ContDiff ℝ 3 Γ := by
    rw [contDiff_iff_contDiffAt]
    intro q
    have hfour_le_top : (4 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      rw [show (4 : ℕ∞ω) = ((4 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hfour_add_one_le_top : (4 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
      rw [show (4 : ℕ∞ω) + 1 = ((5 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hg4 :
        ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 4
          (fun y : M =>
            (⟨y, g.inner y⟩ :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
      simpa using g.contMDiff_inner.of_le hfour_le_top
    have hblend :
        ContDiff ℝ (3 + 1)
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀) := by
      simpa using
        (CovariantDerivative.contDiff_blendedChartMetric
          (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
          hfour_add_one_le_top (cutoff_contDiff (n := n) x₀)
          (cutoff_tsupport (n := n) x₀) hg4)
    apply contDiffAt_clm_of_apply
    intro u
    apply contDiffAt_clm_of_apply
    intro v
    simpa [Γ, chartChristoffelField] using
      (CovariantDerivative.contDiffAt_christoffelAt
        (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (k := 3) (x := q)
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
  have hF : ContDiff ℝ 3 (geodesicFlowField Γ) := by
    have hp : ContDiff ℝ 3 (fun q : E × E => q.1) := contDiff_fst
    have hv : ContDiff ℝ 3 (fun q : E × E => q.2) := contDiff_snd
    have hΓp : ContDiff ℝ 3 (fun q : E × E => Γ q.1) := hΓ.comp hp
    have hΓpv : ContDiff ℝ 3 (fun q : E × E => Γ q.1 q.2) :=
      hΓp.clm_apply hv
    have hΓpvv : ContDiff ℝ 3 (fun q : E × E => Γ q.1 q.2 q.2) :=
      hΓpv.clm_apply hv
    simpa [geodesicFlowField, Γ] using hv.prodMk hΓpvv.neg
  let F : E × E → E × E := geodesicFlowField Γ
  have haug :
      ContDiff ℝ 2 (augmentedGeodesicFlowField Γ) := by
    have hbase : ContDiff ℝ 2 (fun y : (E × E) × (E × E) => F y.1) :=
      (hF.of_le (by norm_num)).comp contDiff_fst
    have hlin :
        ContDiff ℝ 2
          (fun y : (E × E) × (E × E) =>
            (fderiv ℝ F y.1 : (E × E) →L[ℝ] (E × E)) y.2) := by
      simpa [F] using
        (hF.contDiff_fderiv_apply (m := 2) (by norm_num))
    simpa [augmentedGeodesicFlowField, linearizedGeodesicFlowOperator, F, Γ] using
      hbase.prodMk hlin
  constructor
  · simpa [Γ] using haug
  · simpa [Γ] using
      haug.contDiffOn.exists_lipschitzOnWith
        (by norm_num) (convex_closedBall p (a + 1))
        (isCompact_closedBall p (a + 1))

end GeodesicTransport
end Poincare
