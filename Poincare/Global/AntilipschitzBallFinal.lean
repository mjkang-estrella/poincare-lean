import Poincare.Global.AntilipschitzBall

/-!
# Final anti-Lipschitz chart-ball work

This module records the verified chart-staying half of the final local
anti-Lipschitz ball argument.  If a competing path remains in the fixed chart
source and the forward chart derivative is bounded along the path, then its
Riemannian `pathELength` bounds the Euclidean chart displacement from below.

The remaining unproved input is the uniform two-case assembly for arbitrary
paths in a small chart ball: either the path stays in a controlled larger chart
ball and this module applies, or it exits and the existing exit lower bound
dominates the endpoint chart displacement.
-/

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal RealInnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Forward-chart path displacement estimate.  On a path that stays in the chart
source, a uniform bound for the `extChartAt` derivative bounds the Euclidean
chart displacement by the Riemannian path length.
-/
theorem edist_extChartAt_endpoints_le_mul_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {C : ℝ≥0} {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1))
    (hsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source)
    (hC :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t)‖ₑ ≤ C) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    edist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1)) ≤
      C * Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  let γ' : ℝ → E := fun t => (extChartAt I x₀) (γ t)
  have hsrc_chart : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt E x₀).source := by
    intro t ht
    simpa [extChartAt_source] using hsrc t ht
  have hγ' : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ' (Icc (0 : ℝ) 1) := by
    exact contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt E x₀).source)
      hγ hsrc_chart
  have hcont : ContDiffOn ℝ 1 γ' (Icc (0 : ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mp hγ'
  have hsub :
      ‖γ' 1 - γ' 0‖ₑ ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin γ' (Icc (0 : ℝ) 1) t‖ₑ :=
    enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hcont zero_le_one
  calc
    edist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1)) =
        ‖γ' 1 - γ' 0‖ₑ := by
      rw [edist_comm, edist_eq_enorm_sub]
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
          ‖derivWithin γ' (Icc (0 : ℝ) 1) t‖ₑ := hsub
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
          ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc (0 : ℝ) 1) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
          C * ‖mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
      have hmf :
          mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc (0 : ℝ) 1) t =
            (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t)) ∘L
              (mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (hsrc_chart t ht)
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have happ :
          mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ' (Icc (0 : ℝ) 1) t 1 =
            (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t))
              (mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1) :=
        congrArg (fun L => L 1) hmf
      rw [happ]
      exact (ContinuousLinearMap.le_opNorm_enorm _ _).trans
        (mul_le_mul_left (hC t ht)
          ‖mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1‖ₑ)
    _ = C * Manifold.pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]

/--
The chart-staying estimate in the exact lower-bound shape used by the final
pairwise statement.
-/
theorem ofReal_inv_mul_dist_extChartAt_endpoints_le_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {C : ℝ≥0} (hCpos : 0 < C)
    {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1))
    (hsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source)
    (hC :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t)‖ₑ ≤ C) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ENNReal.ofReal
        (((C : ℝ)⁻¹) *
          dist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1))) ≤
      Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  have hedist :
      edist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1)) ≤
        C * Manifold.pathELength I γ 0 1 :=
    edist_extChartAt_endpoints_le_mul_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
      (g := g) (x₀ := x₀) hγ hsrc hC
  have hCposℝ : 0 < (C : ℝ) := by exact_mod_cast hCpos
  have hCne0 : (C : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt hCpos
  have hCnetop : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hofReal :
      ENNReal.ofReal
          (((C : ℝ)⁻¹) *
            dist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1))) =
        (C : ℝ≥0∞)⁻¹ *
          edist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1)) := by
    rw [edist_dist]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hCposℝ.le)]
    rw [ENNReal.ofReal_inv_of_pos hCposℝ]
    simp
  rw [hofReal]
  calc
    (C : ℝ≥0∞)⁻¹ *
        edist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1)) ≤
      (C : ℝ≥0∞)⁻¹ * ((C : ℝ≥0∞) * Manifold.pathELength I γ 0 1) := by
        exact mul_le_mul_right hedist _
    _ = Manifold.pathELength I γ 0 1 := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hCne0 hCnetop, one_mul]

end GeodesicTransport
end Poincare
