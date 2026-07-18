import Poincare.Global.SemilinearHeatBUC

/-!
# Time regularity of corrected semilinear heat mild solutions

Joint continuity alone is enough to differentiate a Volterra integral from
the right at its initial time.  Consequently the nonlinear Duhamel term has
right derivative `N(u₀)` without any extra output hypothesis.  A classical
right derivative for the full solution then requires exactly that the initial
datum lie in the strong generator domain of the heat semigroup.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction Laplacian

namespace Poincare

/-- A jointly continuous triangular Volterra integral has initial right
derivative equal to the diagonal value. -/
theorem hasDerivWithinAt_parametricVolterra_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (g : ℝ → ℝ → X) (hg : Continuous g.uncurry) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..t, g t s)
      (g 0 0) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousAt g.uncurry (0, 0) := hg.continuousAt
  rcases Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hclose⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t htδ
  intro htIci
  have ht0 : 0 ≤ t := Set.mem_Ici.mp htIci
  by_cases htzero : t = 0
  · subst t
    simpa using hε
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
  have htlt : t < δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos htpos] using htδ
  have hgintegrable : IntervalIntegrable (fun s : ℝ ↦ g t s) volume 0 t :=
    (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hconstintegrable : IntervalIntegrable (fun _s : ℝ ↦ g 0 0) volume 0 t :=
    continuous_const.intervalIntegrable _ _
  have heq :
      (∫ s : ℝ in (0 : ℝ)..t, g t s) - t • g 0 0 =
        ∫ s : ℝ in (0 : ℝ)..t, (g t s - g 0 0) := by
    rw [intervalIntegral.integral_sub hgintegrable hconstintegrable,
      intervalIntegral.integral_const, sub_zero]
  have hpoint : ∀ s ∈ Ι (0 : ℝ) t, ‖g t s - g 0 0‖ ≤ ε / 2 := by
    intro s hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa [Set.uIoc_of_le ht0] using hs
    have hs0 : 0 ≤ s := hsIoc.1.le
    have hslt : s < δ := lt_of_le_of_lt hsIoc.2 htlt
    have hpair : dist (t, s) ((0 : ℝ), (0 : ℝ)) < δ := by
      rw [Prod.dist_eq]
      apply max_lt
      · simpa [Real.dist_eq, abs_of_pos htpos] using htlt
      · simpa [Real.dist_eq, abs_of_nonneg hs0] using hslt
    have hgclose := hclose hpair
    simpa [Function.uncurry, dist_eq_norm] using hgclose.le
  have hnorm : ‖∫ s : ℝ in (0 : ℝ)..t, (g t s - g 0 0)‖ ≤
      (ε / 2) * t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa [abs_of_pos htpos] using h
  rw [show (∫ s : ℝ in (0 : ℝ)..(0 : ℝ), g 0 s) = 0 by simp,
    sub_zero, sub_zero, heq]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg t)) (norm_nonneg _))]
  rw [Real.norm_eq_abs, abs_of_pos htpos]
  calc
    t⁻¹ * ‖∫ s : ℝ in (0 : ℝ)..t, (g t s - g 0 0)‖
        ≤ t⁻¹ * ((ε / 2) * t) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ht0)
    _ = ε / 2 := by field_simp [htzero]
    _ < ε := half_lt_self hε

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- The nonlinear Duhamel term has right derivative `N(u(0))` at zero for
every continuous path and continuous intrinsic nonlinearity. -/
theorem hasDerivWithinAt_heatDuhamelBUCIntrinsic_zero
    (T : ℝ≥0) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))))
      (N (u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))))
      (Set.Ici 0) 0 := by
  let g : ℝ → ℝ → BUC := fun t s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  have hg : Continuous g.uncurry := by
    simpa [g, Function.uncurry] using
      continuous_heatDuhamelBUCIntrinsic_integrand
        (E := E) (F := F) T N hN u
  have h := hasDerivWithinAt_parametricVolterra_zero g hg
  simpa [g, vectorHeatSemigroupBUCExtended] using h

/-- Strong heat-generator domain at zero, with its actual derivative value. -/
def IsInBUCHeatGeneratorDomain (u₀ Au₀ : BUC) : Prop :=
  HasDerivWithinAt
    (fun t : ℝ ↦ vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀)
    Au₀ (Set.Ici 0) 0

/-- At every positive time and spatial point, the homogeneous `BUC` heat orbit
is differentiable and satisfies the classical vector heat equation. -/
theorem heatLinearBUC_orbit_solves_heatEquation
    {t : ℝ} (ht : 0 < t) (u₀ : BUC) (x : E) :
    deriv (fun τ : ℝ ↦
      ((vectorHeatSemigroupBUCExtended (E := E) (F := F) τ u₀ : BUC) : E →ᵇ F) x) t =
      (Δ fun z : E ↦ vectorHeatSolution (E := E) t (u₀ : E → F) z) x := by
  have heq :
      (fun τ : ℝ ↦
        ((vectorHeatSemigroupBUCExtended (E := E) (F := F) τ u₀ : BUC) : E →ᵇ F) x) =ᶠ[
          nhds t]
        (fun τ : ℝ ↦ vectorHeatSolution (E := E) τ (u₀ : E → F) x) := by
    filter_upwards [eventually_gt_nhds ht] with τ hτ
    simp [vectorHeatSemigroupBUCExtended, hτ, vectorHeatSemigroupBUCLM_apply,
      vectorHeatSemigroupBUC, vectorHeatSolutionBCF_apply]
  rw [heq.deriv_eq]
  exact vectorHeatSolution_solves_heatEquation_of_bounded_measurable
    (E := E) ht u₀.1.continuous.aestronglyMeasurable
      (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm (u₀ : E →ᵇ F) y) x

/-- Mild-to-classical initial-time upgrade.  The nonlinear contribution is
proved unconditionally; the exact remaining analytic hypothesis is membership
of `u₀` in the strong heat-generator domain. -/
theorem semilinearHeatBUCSolution_hasDerivWithinAt_zero
    (T L : ℝ≥0) (hT : 0 < T)
    (u₀ Au₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) u₀ Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ semilinearHeatBUCSolution T L u₀ N hN hsmall
        (Set.projIcc 0 (T : ℝ) T.property t))
      (Au₀ + N u₀) (Set.Icc 0 (T : ℝ)) 0 := by
  have _hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  let u := semilinearHeatBUCSolution T L u₀ N hN hsmall
  let D : ℝ → BUC := fun t ↦ ∫ s : ℝ in (0 : ℝ)..t,
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  have hD : HasDerivWithinAt D (N u₀) (Set.Ici 0) 0 := by
    have h := hasDerivWithinAt_heatDuhamelBUCIntrinsic_zero
      (E := E) (F := F) T N hN.continuous u
    simpa [D, u] using h
  have hsum := hu₀.add hD
  have hsumIcc : HasDerivWithinAt
      (fun t : ℝ ↦
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ + D t)
      (Au₀ + N u₀) (Set.Icc 0 (T : ℝ)) 0 := by
    apply hsum.mono
    intro t ht
    exact ht.1
  apply hsumIcc.congr
  · intro t ht
    have hproj : Set.projIcc 0 (T : ℝ) T.property t =
        (⟨t, ht⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := by
      apply Subtype.ext
      simp [Set.coe_projIcc, max_eq_right ht.1, min_eq_right ht.2]
    rw [hproj]
    simpa [u, D] using semilinearHeatBUCSolution_mild
      (E := E) (F := F) T L u₀ N hN hsmall
        (⟨t, ht⟩ : Set.Icc (0 : ℝ) (T : ℝ))
  · simp [u, D, vectorHeatSemigroupBUCExtended]

end Poincare
