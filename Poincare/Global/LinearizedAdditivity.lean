import Poincare.Global.LinearizedCLM
import Poincare.Global.LinearizedRescale

/-!
# Endpoint additivity for the rescaled hosted linearized family

This module extends the rescaled hosted linearized family with the two endpoint
linearity identities needed to package its fixed-time endpoint as a
`linearizedEndpointCLM`.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace LinearizedAdditivity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The hosted rescaled linearized family has additive and homogeneous endpoints.

The proof uses the concrete rescaling from `LinearizedRescale`: for each
endpoint direction, solve a normalized initial value in the zero-centered PL
ball and scale the solution back.  To compare sums and scalar multiples, scale
the compared curves down by one common positive factor so both curves stay in
the original PL ball, then apply linear-ODE uniqueness on the common interval.
-/
theorem exists_hosted_rescaled_linearized_solution_family_endpoint_linear
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {ε T : ℝ} (hε : 0 < ε) (hT : T ∈ Icc (-ε) ε)
    {a r L K : ℝ≥0} (hr : 0 < (r : ℝ))
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E), (0 : E)) a r L K) :
    ∃ Ψ : E → ℝ → E × E,
      (∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w)) ∧
        (∀ w : E, ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt (Ψ w)
            (linearizedGeodesicFlowFieldAlong
              (GeodesicTransport.chartChristoffelField g x₀)
              γ t (Ψ w t))
            (Icc (-ε) ε) t) ∧
        (∀ w w' : E,
          (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1) ∧
        ∀ (c : ℝ) (w : E),
          (Ψ (c • w) T).1 = c • (Ψ w T).1 := by
  rcases
    LinearizedFamilyExport.exists_hosted_linearized_solution_family_on_pl_closedBall
      (g := g) (x₀ := x₀) (γ := γ) (ε := ε) (T := T)
      hε hpl with
    ⟨Ψ₀, hΨ₀⟩
  let Γ : E → E →L[ℝ] E →L[ℝ] E :=
    GeodesicTransport.chartChristoffelField g x₀
  let A : ℝ → (E × E) →L[ℝ] (E × E) :=
    fun t => linearizedGeodesicFlowOperator Γ (γ t)
  let scale : E → ℝ :=
    fun w => max 1 ((2 * ‖T⁻¹ • w‖) / (r : ℝ))
  let base : E → E := fun w => (scale w)⁻¹ • w
  have hscale_pos : ∀ w : E, 0 < scale w := by
    intro w
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase_mem :
      ∀ w : E, ((0 : E), T⁻¹ • base w) ∈
        closedBall ((0 : E), (0 : E)) r := by
    intro w
    have hscale_ge :
        (2 * ‖T⁻¹ • w‖) / (r : ℝ) ≤ scale w :=
      le_max_right _ _
    have hhalf_nonneg : 0 ≤ (r : ℝ) / 2 := by linarith
    have hnorm_le_half :
        ‖T⁻¹ • base w‖ ≤ (r : ℝ) / 2 := by
      have hmul_le :
          ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) ≤
            ((r : ℝ) / 2) * scale w :=
        mul_le_mul_of_nonneg_left hscale_ge hhalf_nonneg
      have hleft :
          ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) =
            ‖T⁻¹ • w‖ := by
        field_simp [ne_of_gt hr]
      have hnorm_div :
          ‖T⁻¹ • base w‖ = ‖T⁻¹ • w‖ / scale w := by
        have hcomm :
            T⁻¹ • base w = (scale w)⁻¹ • (T⁻¹ • w) := by
          simp [base, smul_smul, mul_comm]
        have hscale_abs : |(scale w)⁻¹| = (scale w)⁻¹ := by
          rw [abs_of_pos]
          exact inv_pos.mpr (hscale_pos w)
        rw [hcomm, norm_smul, Real.norm_eq_abs, hscale_abs, div_eq_inv_mul]
      rw [hnorm_div, div_le_iff₀ (hscale_pos w)]
      calc
        ‖T⁻¹ • w‖ = ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) :=
          hleft.symm
        _ ≤ ((r : ℝ) / 2) * scale w := hmul_le
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm_pair :
        ‖((0 : E), T⁻¹ • base w) - ((0 : E), (0 : E))‖ ≤ (r : ℝ) := by
      simpa [Prod.norm_def] using hnorm_le_half.trans (by linarith : (r : ℝ) / 2 ≤ r)
    exact hnorm_pair
  let Ψ : E → ℝ → E × E := fun w t => scale w • Ψ₀ (base w) t
  have hΨ0 : ∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w) := by
    intro w
    have hlocal := (hΨ₀ (base w) (hbase_mem w)).1
    have hsne : scale w ≠ 0 := ne_of_gt (hscale_pos w)
    calc
      Ψ w 0 = scale w • Ψ₀ (base w) 0 := rfl
      _ = scale w • ((0 : E), T⁻¹ • base w) := by rw [hlocal]
      _ = ((0 : E), T⁻¹ • w) := by
        have hscalar : scale w * (T⁻¹ * (scale w)⁻¹) = T⁻¹ := by
          field_simp [hsne]
        have hvec : scale w • (T⁻¹ • base w) = T⁻¹ • w := by
          ext i
          simp [base, smul_smul, hscalar]
        exact Prod.ext (by simp) hvec
  have hΨder : ∀ w : E, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ w t))
        (Icc (-ε) ε) t := by
    intro w t ht
    have hlocal := (hΨ₀ (base w) (hbase_mem w)).2.1 t ht
    simpa [Ψ, Γ, linearizedGeodesicFlowFieldAlong_smul] using
      hlocal.const_smul (scale w)
  have hnorm_scaled_smul_le :
      ∀ (u : E) (d : ℝ) {S : ℝ}, 0 < S →
        ∀ t ∈ Icc (-ε) ε,
          ‖S⁻¹ • (d • Ψ u t)‖ ≤
            (S⁻¹ * |d| * scale u) * (a : ℝ) := by
    intro u d S hSpos t ht
    have hlocal_mem := (hΨ₀ (base u) (hbase_mem u)).2.2 t ht
    have hlocal_norm : ‖Ψ₀ (base u) t‖ ≤ (a : ℝ) := by
      have hlocal_norm' : ‖Ψ₀ (base u) t - ((0 : E), (0 : E))‖ ≤ (a : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hlocal_mem
      have hzero_pair : ((0 : E), (0 : E)) = (0 : E × E) := rfl
      simpa [hzero_pair] using hlocal_norm'
    have hcoef_nonneg : 0 ≤ S⁻¹ * |d| * scale u := by
      positivity
    have habs : |S⁻¹ * d * scale u| = S⁻¹ * |d| * scale u := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hSpos),
        abs_of_nonneg (hscale_pos u).le]
    calc
      ‖S⁻¹ • (d • Ψ u t)‖ =
          ‖(S⁻¹ * d * scale u) • Ψ₀ (base u) t‖ := by
        simp [Ψ, smul_smul, mul_assoc]
      _ = (S⁻¹ * |d| * scale u) * ‖Ψ₀ (base u) t‖ := by
        rw [norm_smul, Real.norm_eq_abs, habs]
      _ ≤ (S⁻¹ * |d| * scale u) * (a : ℝ) :=
        mul_le_mul_of_nonneg_left hlocal_norm hcoef_nonneg
  have hmem_scaled_smul_of_le :
      ∀ (u : E) (d : ℝ) {S : ℝ}, 0 < S → |d| * scale u ≤ S →
        ∀ t ∈ Icc (-ε) ε,
          S⁻¹ • (d • Ψ u t) ∈ closedBall ((0 : E), (0 : E)) a := by
    intro u d S hSpos hle t ht
    have hnorm := hnorm_scaled_smul_le u d hSpos t ht
    have hcoef_le : S⁻¹ * |d| * scale u ≤ 1 := by
      have hle' : S⁻¹ * (|d| * scale u) ≤ 1 :=
        (inv_mul_le_one₀ hSpos).mpr hle
      simpa [mul_assoc] using hle'
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖S⁻¹ • (d • Ψ u t) - ((0 : E), (0 : E))‖ =
          ‖S⁻¹ • (d • Ψ u t)‖ := by
        change ‖S⁻¹ • (d • Ψ u t) - (0 : E × E)‖ =
          ‖S⁻¹ • (d • Ψ u t)‖
        simp
      _ ≤ (S⁻¹ * |d| * scale u) * (a : ℝ) := hnorm
      _ ≤ 1 * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef_le (NNReal.coe_nonneg a)
      _ = (a : ℝ) := by ring
  have hmem_scaled_add_of_le :
      ∀ (u v : E) {S : ℝ}, 0 < S → scale u + scale v ≤ S →
        ∀ t ∈ Icc (-ε) ε,
          S⁻¹ • (Ψ u t + Ψ v t) ∈ closedBall ((0 : E), (0 : E)) a := by
    intro u v S hSpos hle t ht
    have hu :
        ‖S⁻¹ • Ψ u t‖ ≤ (S⁻¹ * scale u) * (a : ℝ) := by
      simpa using hnorm_scaled_smul_le u (1 : ℝ) hSpos t ht
    have hv :
        ‖S⁻¹ • Ψ v t‖ ≤ (S⁻¹ * scale v) * (a : ℝ) := by
      simpa using hnorm_scaled_smul_le v (1 : ℝ) hSpos t ht
    have hcoef_le : S⁻¹ * (scale u + scale v) ≤ 1 :=
      (inv_mul_le_one₀ hSpos).mpr hle
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖S⁻¹ • (Ψ u t + Ψ v t) - ((0 : E), (0 : E))‖ =
          ‖S⁻¹ • Ψ u t + S⁻¹ • Ψ v t‖ := by
        change ‖S⁻¹ • (Ψ u t + Ψ v t) - (0 : E × E)‖ =
          ‖S⁻¹ • Ψ u t + S⁻¹ • Ψ v t‖
        simp [smul_add]
      _ ≤ ‖S⁻¹ • Ψ u t‖ + ‖S⁻¹ • Ψ v t‖ := norm_add_le _ _
      _ ≤ (S⁻¹ * scale u) * (a : ℝ) +
            (S⁻¹ * scale v) * (a : ℝ) := add_le_add hu hv
      _ = (S⁻¹ * (scale u + scale v)) * (a : ℝ) := by ring
      _ ≤ 1 * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef_le (NNReal.coe_nonneg a)
      _ = (a : ℝ) := by ring
  refine ⟨Ψ, hΨ0, ?_, ?_, ?_⟩
  · intro w t ht
    simpa [Γ] using hΨder w t ht
  · intro w w'
    let S : ℝ := max (scale (w + w')) (scale w + scale w')
    have hSpos : 0 < S :=
      lt_of_lt_of_le (hscale_pos (w + w')) (le_max_left _ _)
    have hS_add : scale (w + w') ≤ S := le_max_left _ _
    have hS_sum : scale w + scale w' ≤ S := le_max_right _ _
    have hleft_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • Ψ (w + w') t ∈ closedBall ((0 : E), (0 : E)) a := by
      intro t ht
      simpa using
        hmem_scaled_smul_of_le (w + w') (1 : ℝ) hSpos (by simpa using hS_add) t ht
    have hright_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • (Ψ w t + Ψ w' t) ∈ closedBall ((0 : E), (0 : E)) a :=
      hmem_scaled_add_of_le w w' hSpos hS_sum
    have hder_left : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • Ψ (w + w') τ)
          (A t ((fun τ : ℝ => S⁻¹ • Ψ (w + w') τ) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := (hΨder (w + w') t ht).const_smul S⁻¹
      simpa [A, linearizedGeodesicFlowFieldAlong_smul] using hder
    have hder_right : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • (Ψ w τ + Ψ w' τ))
          (A t ((fun τ : ℝ => S⁻¹ • (Ψ w τ + Ψ w' τ)) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder_sum := (hΨder w t ht).add (hΨder w' t ht)
      have hder := hder_sum.const_smul S⁻¹
      simpa [A, linearizedGeodesicFlowFieldAlong_add,
        linearizedGeodesicFlowFieldAlong_smul] using hder
    have hinitial :
        (fun τ : ℝ => S⁻¹ • Ψ (w + w') τ)
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) =
          (fun τ : ℝ => S⁻¹ • (Ψ w τ + Ψ w' τ))
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) := by
      change S⁻¹ • Ψ (w + w') 0 = S⁻¹ • (Ψ w 0 + Ψ w' 0)
      rw [hΨ0 (w + w'), hΨ0 w, hΨ0 w']
      ext i <;> simp [smul_add]
    have hEq :
        EqOn (fun τ : ℝ => S⁻¹ • Ψ (w + w') τ)
          (fun τ : ℝ => S⁻¹ • (Ψ w τ + Ψ w' τ)) (Icc (-ε) ε) :=
      linearODE_solution_uniqueOn_Icc
        (A := A) (t₀ := ⟨(0 : ℝ), by constructor <;> linarith⟩)
        (x₀ := ((0 : E), (0 : E))) (a := a) (r := r) (L := L) (K := K)
        hpl hder_left hleft_mem hder_right hright_mem hinitial
    have hstate := hEq hT
    have hsne : S ≠ 0 := ne_of_gt hSpos
    have hpair : Ψ (w + w') T = Ψ w T + Ψ w' T := by
      have hscaled := congrArg (fun z : E × E => S • z) hstate
      simpa [smul_smul, hsne] using hscaled
    exact congrArg Prod.fst hpair
  · intro c w
    let S : ℝ := max (scale (c • w)) (|c| * scale w)
    have hSpos : 0 < S :=
      lt_of_lt_of_le (hscale_pos (c • w)) (le_max_left _ _)
    have hS_smul : scale (c • w) ≤ S := le_max_left _ _
    have hS_scaled : |c| * scale w ≤ S := le_max_right _ _
    have hleft_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • Ψ (c • w) t ∈ closedBall ((0 : E), (0 : E)) a := by
      intro t ht
      simpa using
        hmem_scaled_smul_of_le (c • w) (1 : ℝ) hSpos (by simpa using hS_smul) t ht
    have hright_mem : ∀ t ∈ Icc (-ε) ε,
        S⁻¹ • (c • Ψ w t) ∈ closedBall ((0 : E), (0 : E)) a :=
      hmem_scaled_smul_of_le w c hSpos hS_scaled
    have hder_left : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • Ψ (c • w) τ)
          (A t ((fun τ : ℝ => S⁻¹ • Ψ (c • w) τ) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := (hΨder (c • w) t ht).const_smul S⁻¹
      simpa [A, linearizedGeodesicFlowFieldAlong_smul] using hder
    have hder_right : ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun τ : ℝ => S⁻¹ • (c • Ψ w τ))
          (A t ((fun τ : ℝ => S⁻¹ • (c • Ψ w τ)) t))
          (Icc (-ε) ε) t := by
      intro t ht
      have hder := ((hΨder w t ht).const_smul c).const_smul S⁻¹
      simpa [A, linearizedGeodesicFlowFieldAlong_smul, smul_smul] using hder
    have hinitial :
        (fun τ : ℝ => S⁻¹ • Ψ (c • w) τ)
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) =
          (fun τ : ℝ => S⁻¹ • (c • Ψ w τ))
            (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) := by
      change S⁻¹ • Ψ (c • w) 0 = S⁻¹ • (c • Ψ w 0)
      rw [hΨ0 (c • w), hΨ0 w]
      ext i <;> simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]
    have hEq :
        EqOn (fun τ : ℝ => S⁻¹ • Ψ (c • w) τ)
          (fun τ : ℝ => S⁻¹ • (c • Ψ w τ)) (Icc (-ε) ε) :=
      linearODE_solution_uniqueOn_Icc
        (A := A) (t₀ := ⟨(0 : ℝ), by constructor <;> linarith⟩)
        (x₀ := ((0 : E), (0 : E))) (a := a) (r := r) (L := L) (K := K)
        hpl hder_left hleft_mem hder_right hright_mem hinitial
    have hstate := hEq hT
    have hsne : S ≠ 0 := ne_of_gt hSpos
    have hpair : Ψ (c • w) T = c • Ψ w T := by
      have hscaled := congrArg (fun z : E × E => S • z) hstate
      simpa [smul_smul, hsne] using hscaled
    simpa using congrArg Prod.fst hpair

end LinearizedAdditivity
end Poincare
