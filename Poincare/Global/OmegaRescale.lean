import Poincare.Global.ThirdFamily

/-!
# Rescaling the hosted third-variation family

This module isolates the level-three analogue of the linearized rescaling
pattern: a zero-centered Picard-Lindelof solution family for the hosted
third-variation linear system yields all-perturbation solutions, and linear ODE
uniqueness gives additivity and homogeneity on the common interval.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace OmegaRescale

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)
local notation "X" => A × A

omit [T2Space M] in
/--
All-perturbation hosted third-variation solutions obtained by rescaling the
zero-ball Picard-Lindelof family.

The selected local family is only defined with hypotheses on
`η ∈ closedBall 0 r`.  Each perturbation is normalized into that ball and then
scaled back.  Additivity and homogeneity follow by scaling both compared curves
into the same zero-centered PL ball and applying linear ODE uniqueness.
-/
theorem exists_rescaled_hosted_thirdVariation_solution_family_linear
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → X} (hζ : Continuous ζ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ Ω : X → ℝ → X,
      (∀ η : X, Ω η 0 = η) ∧
        (∀ η : X, ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt (Ω η)
            (fderiv ℝ
              (fun y : X =>
                let F : A → A :=
                  augmentedGeodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                (F y.1, (fderiv ℝ F y.1) y.2))
              (ζ t) (Ω η t))
            (Icc (-ε) ε) t) ∧
        (∀ η η' : X, ∀ t ∈ Icc (-ε) ε,
          Ω (η + η') t = Ω η t + Ω η' t) ∧
        ∀ (c : ℝ) (η : X), ∀ t ∈ Icc (-ε) ε,
          Ω (c • η) t = c • Ω η t := by
  rcases
      GeodesicTransport.exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE
        (g := g) (x₀ := x₀) (ζ := ζ) hζ (0 : X) with
    ⟨ε, hε, a, r, L, K, hr, hpl⟩
  rcases hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall with
    ⟨Ω₀, hΩ₀⟩
  let doubleF : X → X := fun y =>
    let F : A → A :=
      augmentedGeodesicFlowField
        (GeodesicTransport.chartChristoffelField g x₀)
    (F y.1, (fderiv ℝ F y.1) y.2)
  let Aop : ℝ → X →L[ℝ] X := fun t => fderiv ℝ doubleF (ζ t)
  let scale : X → ℝ := fun η => max 1 ((2 * ‖η‖) / (r : ℝ))
  let base : X → X := fun η => (scale η)⁻¹ • η
  have hscale_pos : ∀ η : X, 0 < scale η := by
    intro η
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase_mem : ∀ η : X, base η ∈ closedBall (0 : X) r := by
    intro η
    have hscale_ge :
        (2 * ‖η‖) / (r : ℝ) ≤ scale η :=
      le_max_right _ _
    have hhalf_nonneg : 0 ≤ (r : ℝ) / 2 := by positivity
    have hnorm_le_half : ‖base η‖ ≤ (r : ℝ) / 2 := by
      have hmul_le :
          ((r : ℝ) / 2) * ((2 * ‖η‖) / (r : ℝ)) ≤
            ((r : ℝ) / 2) * scale η :=
        mul_le_mul_of_nonneg_left hscale_ge hhalf_nonneg
      have hleft :
          ((r : ℝ) / 2) * ((2 * ‖η‖) / (r : ℝ)) = ‖η‖ := by
        field_simp [ne_of_gt hr]
      have hnorm_div : ‖base η‖ = ‖η‖ / scale η := by
        have hscale_abs : |(scale η)⁻¹| = (scale η)⁻¹ := by
          rw [abs_of_pos]
          exact inv_pos.mpr (hscale_pos η)
        have hbase_eq : base η = (scale η)⁻¹ • η := rfl
        rw [hbase_eq, norm_smul, Real.norm_eq_abs, hscale_abs, div_eq_inv_mul]
      rw [hnorm_div, div_le_iff₀ (hscale_pos η)]
      calc
        ‖η‖ = ((r : ℝ) / 2) * ((2 * ‖η‖) / (r : ℝ)) :=
          hleft.symm
        _ ≤ ((r : ℝ) / 2) * scale η := hmul_le
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using
      hnorm_le_half.trans
        (by nlinarith [show 0 ≤ (r : ℝ) from NNReal.coe_nonneg r] :
          (r : ℝ) / 2 ≤ r)
  let Ω : X → ℝ → X := fun η t => scale η • Ω₀ (base η) t
  have hΩ0 : ∀ η : X, Ω η 0 = η := by
    intro η
    have hlocal := (hΩ₀ (base η) (hbase_mem η)).1
    have hsne : scale η ≠ 0 := ne_of_gt (hscale_pos η)
    calc
      Ω η 0 = scale η • Ω₀ (base η) 0 := rfl
      _ = scale η • base η := by rw [hlocal]
      _ = η := by
        have hcoef : scale η * (scale η)⁻¹ = 1 := by
          field_simp [hsne]
        simp [base, smul_smul, hcoef]
  have hΩder : ∀ η : X, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ω η) (Aop t (Ω η t)) (Icc (-ε) ε) t := by
    intro η t ht
    have hlocal := (hΩ₀ (base η) (hbase_mem η)).2.1 t ht
    simpa [Ω, Aop, doubleF] using hlocal.const_smul (scale η)
  have hnorm_scaled_smul_le :
      ∀ (η : X) (d : ℝ) {S : ℝ}, 0 < S →
        ∀ t ∈ Icc (-ε) ε,
          ‖S⁻¹ • (d • Ω η t)‖ ≤
            (S⁻¹ * |d| * scale η) * (a : ℝ) := by
    intro η d S hSpos t ht
    have hlocal_mem := (hΩ₀ (base η) (hbase_mem η)).2.2 t ht
    have hlocal_norm : ‖Ω₀ (base η) t‖ ≤ (a : ℝ) := by
      have hlocal_norm' :
          ‖Ω₀ (base η) t - (0 : X)‖ ≤ (a : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hlocal_mem
      simpa using hlocal_norm'
    have hcoef_nonneg : 0 ≤ S⁻¹ * |d| * scale η := by
      positivity
    have habs : |S⁻¹ * d * scale η| = S⁻¹ * |d| * scale η := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hSpos),
        abs_of_nonneg (hscale_pos η).le]
    calc
      ‖S⁻¹ • (d • Ω η t)‖ =
          ‖(S⁻¹ * d * scale η) • Ω₀ (base η) t‖ := by
        simp [Ω, smul_smul, mul_assoc]
      _ = (S⁻¹ * |d| * scale η) * ‖Ω₀ (base η) t‖ := by
        rw [norm_smul, Real.norm_eq_abs, habs]
      _ ≤ (S⁻¹ * |d| * scale η) * (a : ℝ) :=
        mul_le_mul_of_nonneg_left hlocal_norm hcoef_nonneg
  have hmem_scaled_smul_of_le :
      ∀ (η : X) (d : ℝ) {S : ℝ}, 0 < S → |d| * scale η ≤ S →
        ∀ t ∈ Icc (-ε) ε,
          S⁻¹ • (d • Ω η t) ∈ closedBall (0 : X) a := by
    intro η d S hSpos hle t ht
    have hnorm := hnorm_scaled_smul_le η d hSpos t ht
    have hcoef_le : S⁻¹ * |d| * scale η ≤ 1 := by
      have hle' : S⁻¹ * (|d| * scale η) ≤ 1 :=
        (inv_mul_le_one₀ hSpos).mpr hle
      simpa [mul_assoc] using hle'
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖S⁻¹ • (d • Ω η t) - (0 : X)‖ =
          ‖S⁻¹ • (d • Ω η t)‖ := by simp
      _ ≤ (S⁻¹ * |d| * scale η) * (a : ℝ) := hnorm
      _ ≤ 1 * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef_le (NNReal.coe_nonneg a)
      _ = (a : ℝ) := by ring
  have hmem_scaled_add_of_le :
      ∀ (η η' : X) {S : ℝ}, 0 < S → scale η + scale η' ≤ S →
        ∀ t ∈ Icc (-ε) ε,
          S⁻¹ • (Ω η t + Ω η' t) ∈ closedBall (0 : X) a := by
    intro η η' S hSpos hle t ht
    have hη :
        ‖S⁻¹ • Ω η t‖ ≤ (S⁻¹ * scale η) * (a : ℝ) := by
      simpa using hnorm_scaled_smul_le η (1 : ℝ) hSpos t ht
    have hη' :
        ‖S⁻¹ • Ω η' t‖ ≤ (S⁻¹ * scale η') * (a : ℝ) := by
      simpa using hnorm_scaled_smul_le η' (1 : ℝ) hSpos t ht
    have hcoef_le : S⁻¹ * (scale η + scale η') ≤ 1 :=
      (inv_mul_le_one₀ hSpos).mpr hle
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖S⁻¹ • (Ω η t + Ω η' t) - (0 : X)‖ =
          ‖S⁻¹ • Ω η t + S⁻¹ • Ω η' t‖ := by
        simp [smul_add]
      _ ≤ ‖S⁻¹ • Ω η t‖ + ‖S⁻¹ • Ω η' t‖ := norm_add_le _ _
      _ ≤ (S⁻¹ * scale η) * (a : ℝ) +
            (S⁻¹ * scale η') * (a : ℝ) := add_le_add hη hη'
      _ = (S⁻¹ * (scale η + scale η')) * (a : ℝ) := by ring
      _ ≤ 1 * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef_le (NNReal.coe_nonneg a)
      _ = (a : ℝ) := by ring
  have hΩder' : ∀ η : X, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ω η)
        (fderiv ℝ
          (fun y : X =>
            let F : A → A :=
              augmentedGeodesicFlowField
                (GeodesicTransport.chartChristoffelField g x₀)
            (F y.1, (fderiv ℝ F y.1) y.2))
          (ζ t) (Ω η t))
        (Icc (-ε) ε) t := by
    intro η t ht
    simpa [Aop, doubleF] using hΩder η t ht
  have hΩadd : ∀ η η' : X, ∀ t ∈ Icc (-ε) ε,
      Ω (η + η') t = Ω η t + Ω η' t := by
    intro η η' t ht
    let S : ℝ := max (scale (η + η')) (scale η + scale η')
    have hSpos : 0 < S :=
      lt_of_lt_of_le (hscale_pos (η + η')) (le_max_left _ _)
    have hS_add : scale (η + η') ≤ S := le_max_left _ _
    have hS_sum : scale η + scale η' ≤ S := le_max_right _ _
    have hleft_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • Ω (η + η') t ∈ closedBall (0 : X) a := by
      intro t ht
      simpa using
        hmem_scaled_smul_of_le (η + η') (1 : ℝ) hSpos (by simpa using hS_add) t ht
    have hright_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • (Ω η t + Ω η' t) ∈ closedBall (0 : X) a :=
      hmem_scaled_add_of_le η η' hSpos hS_sum
    have hder_left : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • Ω (η + η') τ)
          (Aop t ((fun τ : ℝ => S⁻¹ • Ω (η + η') τ) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := (hΩder (η + η') t ht).const_smul S⁻¹
      simpa [Aop] using hder
    have hder_right : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • (Ω η τ + Ω η' τ))
          (Aop t ((fun τ : ℝ => S⁻¹ • (Ω η τ + Ω η' τ)) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder_sum := (hΩder η t ht).add (hΩder η' t ht)
      have hder := hder_sum.const_smul S⁻¹
      simpa [Aop, smul_add] using hder
    have hinitial :
        (fun τ : ℝ => S⁻¹ • Ω (η + η') τ)
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) =
          (fun τ : ℝ => S⁻¹ • (Ω η τ + Ω η' τ))
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) := by
      change S⁻¹ • Ω (η + η') 0 = S⁻¹ • (Ω η 0 + Ω η' 0)
      rw [hΩ0 (η + η'), hΩ0 η, hΩ0 η']
    have hEq :
        EqOn (fun τ : ℝ => S⁻¹ • Ω (η + η') τ)
          (fun τ : ℝ => S⁻¹ • (Ω η τ + Ω η' τ)) (Icc (-ε) ε) :=
      linearODE_solution_uniqueOn_Icc
        hpl hder_left hleft_mem hder_right hright_mem hinitial
    have hstate := hEq ht
    have hsne : S ≠ 0 := ne_of_gt hSpos
    have hscaled := congrArg (fun z : X => S • z) hstate
    simpa [smul_smul, hsne] using hscaled
  have hΩsmul : ∀ (c : ℝ) (η : X), ∀ t ∈ Icc (-ε) ε,
      Ω (c • η) t = c • Ω η t := by
    intro c η t ht
    let S : ℝ := max (scale (c • η)) (|c| * scale η)
    have hSpos : 0 < S :=
      lt_of_lt_of_le (hscale_pos (c • η)) (le_max_left _ _)
    have hS_smul : scale (c • η) ≤ S := le_max_left _ _
    have hS_scaled : |c| * scale η ≤ S := le_max_right _ _
    have hleft_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • Ω (c • η) t ∈ closedBall (0 : X) a := by
      intro t ht
      simpa using
        hmem_scaled_smul_of_le (c • η) (1 : ℝ) hSpos (by simpa using hS_smul) t ht
    have hright_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • (c • Ω η t) ∈ closedBall (0 : X) a :=
      hmem_scaled_smul_of_le η c hSpos hS_scaled
    have hder_left : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • Ω (c • η) τ)
          (Aop t ((fun τ : ℝ => S⁻¹ • Ω (c • η) τ) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := (hΩder (c • η) t ht).const_smul S⁻¹
      simpa [Aop] using hder
    have hder_right : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • (c • Ω η τ))
          (Aop t ((fun τ : ℝ => S⁻¹ • (c • Ω η τ)) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := ((hΩder η t ht).const_smul c).const_smul S⁻¹
      simpa [Aop, smul_smul] using hder
    have hinitial :
        (fun τ : ℝ => S⁻¹ • Ω (c • η) τ)
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) =
          (fun τ : ℝ => S⁻¹ • (c • Ω η τ))
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) := by
      change S⁻¹ • Ω (c • η) 0 = S⁻¹ • (c • Ω η 0)
      rw [hΩ0 (c • η), hΩ0 η]
    have hEq :
        EqOn (fun τ : ℝ => S⁻¹ • Ω (c • η) τ)
          (fun τ : ℝ => S⁻¹ • (c • Ω η τ)) (Icc (-ε) ε) :=
      linearODE_solution_uniqueOn_Icc
        hpl hder_left hleft_mem hder_right hright_mem hinitial
    have hstate := hEq ht
    have hsne : S ≠ 0 := ne_of_gt hSpos
    have hscaled := congrArg (fun z : X => S • z) hstate
    simpa [smul_smul, hsne] using hscaled
  exact ⟨ε, hε, Ω, hΩ0, hΩder', hΩadd, hΩsmul⟩

end OmegaRescale
end Poincare
