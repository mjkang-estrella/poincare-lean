import Poincare.Global.GeodesicFlowDerivative
import Poincare.Global.SecondVariation

/-!
# Fixed-time derivative for the augmented first-variation flow

This module replays the first-order residual/Gronwall argument for the
augmented system `(p, ψ)' = (F p, D F p ψ)`.  The derivative of the augmented
flow is the second-variation solution, i.e. the linearized equation along the
augmented curve.
-/

noncomputable section

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Fixed-time derivative of a local augmented geodesic/first-variation flow.

The statement is the second-order analogue of
`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`, with the
chart-specific existence and tube data supplied as hypotheses.  The proof uses
the compact-uniform Taylor remainder for the augmented vector field and the
same residual Gronwall comparison as the first-order chain.
-/
theorem augmentedFlow_hasDerivAt_of_secondVariation_gronwall
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {β : ((E × E) × (E × E)) → ℝ → ((E × E) × (E × E))}
    {z η : (E × E) × (E × E)}
    {Ξ : ℝ → (E × E) × (E × E)}
    {T a : ℝ} {K : ℝ≥0} {p : (E × E) × (E × E)} {t : ℝ}
    (hT : 0 < T)
    (haug : ContDiff ℝ 1 (augmentedGeodesicFlowField Γ))
    (hcompact : IsCompact (closedBall p (a + 1)))
    (hLip :
      LipschitzOnWith K (augmentedGeodesicFlowField Γ)
        (closedBall p (a + 1)))
    (hbase0 : β z 0 = z)
    (hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β z)
        (augmentedGeodesicFlowField Γ (β z τ)) (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T,
      β z τ ∈ closedBall p a)
    (hpert : ∀ᶠ s in 𝓝 (0 : ℝ),
      β (z + s • η) 0 = z + s • η ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (z + s • η))
            (augmentedGeodesicFlowField Γ (β (z + s • η) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          β (z + s • η) τ ∈ closedBall p a)
    (hΞ0 : Ξ 0 = η)
    (hΞder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ξ
        (secondVariationFlowFieldAlong Γ (β z) τ (Ξ τ))
        (Icc (0 : ℝ) T) τ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => β (z + s • η) t) (Ξ t) 0 := by
  let X := (E × E) × (E × E)
  let F : X → X := augmentedGeodesicFlowField Γ
  let R : ℝ → ℝ → X := fun s τ =>
    β (z + s • η) τ - β z τ - s • Ξ τ
  let Rder : ℝ → ℝ → X := fun s τ =>
    F (β (z + s • η) τ) - F (β z τ) -
      s • secondVariationFlowOperator Γ (β z τ) (Ξ τ)
  let C : ℝ := Real.exp ((K : ℝ) * T) * ‖η‖
  have hT_nonneg : 0 ≤ T := hT.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hIco_subset : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) T :=
    Ico_subset_Icc_self
  have hclose : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖β (z + s • η) τ - β z τ‖ ≤ C * ‖s‖ := by
    filter_upwards [hpert] with s hs
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hpert_cont : ContinuousOn (β (z + s • η)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (z + s • η) r)) (by
          intro r hr
          simpa [F] using hs.2.1 r hr)
    have hbase_cont : ContinuousOn (β z) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β z r)) (by
          intro r hr
          simpa [F] using hbase_der r hr)
    have hdist :
        dist (β (z + s • η) τ) (β z τ) ≤
          dist (z + s • η) z * Real.exp ((K : ℝ) * (τ - 0)) := by
      exact
        dist_le_of_trajectories_ODE_of_mem
          (v := fun _ : ℝ => F)
          (s := fun _ : ℝ => closedBall p (a + 1))
          (K := K) (a := 0) (b := T)
          (by
            intro _ _
            simpa [F] using hLip)
          hpert_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hs.2.1 r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hs.2.2 r (hIco_subset hr)))
          hbase_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hbase_der r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hbase_mem r (hIco_subset hr)))
          (by
            rw [hs.1, hbase0])
          τ hτIcc
    have hexp_le :
        Real.exp ((K : ℝ) * (τ - 0)) ≤ Real.exp ((K : ℝ) * T) := by
      apply Real.exp_le_exp.mpr
      have hτ_le : τ ≤ T := hτIcc.2
      have hK_nonneg : 0 ≤ (K : ℝ) := K.2
      nlinarith
    calc
      ‖β (z + s • η) τ - β z τ‖ =
          dist (β (z + s • η) τ) (β z τ) := by
            rw [dist_eq_norm]
      _ ≤ dist (z + s • η) z * Real.exp ((K : ℝ) * (τ - 0)) :=
          hdist
      _ ≤ (‖s‖ * ‖η‖) * Real.exp ((K : ℝ) * T) := by
          have hdist0 : dist (z + s • η) z = ‖s‖ * ‖η‖ := by
            simp [dist_eq_norm, norm_smul]
          rw [hdist0]
          exact mul_le_mul_of_nonneg_left hexp_le
            (mul_nonneg (norm_nonneg s) (norm_nonneg η))
      _ = C * ‖s‖ := by
          simp [C]
          ring
  have hRcont : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContinuousOn (R s) (Icc (0 : ℝ) T) := by
    filter_upwards [hpert] with s hs
    have hpert_cont : ContinuousOn (β (z + s • η)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (z + s • η) r)) (by
          intro r hr
          simpa [F] using hs.2.1 r hr)
    have hbase_cont : ContinuousOn (β z) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β z r)) (by
          intro r hr
          simpa [F] using hbase_der r hr)
    have hΞ_cont : ContinuousOn Ξ (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r =>
          secondVariationFlowFieldAlong Γ (β z) r (Ξ r)) (by
            intro r hr
            exact hΞder r hr)
    simpa [R] using (hpert_cont.sub hbase_cont).sub (hΞ_cont.const_smul s)
  have hRderiv : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (R s) (Rder s τ) (Ici τ) τ := by
    filter_upwards [hpert] with s hs
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hnhds : Icc (0 : ℝ) T ∈ 𝓝[Ici τ] τ :=
      Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩
    have hpert_der :
        HasDerivWithinAt (β (z + s • η))
          (F (β (z + s • η) τ)) (Ici τ) τ := by
      simpa [F] using
        (hs.2.1 τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hbase_der' :
        HasDerivWithinAt (β z) (F (β z τ)) (Ici τ) τ := by
      simpa [F] using
        (hbase_der τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hΞ_der' :
        HasDerivWithinAt Ξ
          (secondVariationFlowOperator Γ (β z τ) (Ξ τ)) (Ici τ) τ := by
      simpa [secondVariationFlowFieldAlong] using
        (hΞder τ hτIcc).mono_of_mem_nhdsWithin hnhds
    simpa [R, Rder, F] using
      (hpert_der.sub hbase_der').sub (hΞ_der'.const_smul s)
  have hR0 : ∀ᶠ s in 𝓝 (0 : ℝ), R s 0 = 0 := by
    filter_upwards [hpert] with s hs
    simp [R, hs.1, hbase0, hΞ0]
  have hbound : ∀ μ > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖Rder s τ‖ ≤ (K : ℝ) * ‖R s τ‖ + μ * ‖s‖ := by
    intro μ hμ
    let θ : ℝ := μ / (C + 1)
    have hden_pos : 0 < C + 1 := by positivity
    have hθ_pos : 0 < θ := by
      dsimp [θ]
      positivity
    have hθC_le : θ * C ≤ μ := by
      dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      nlinarith [hμ.le, hC_nonneg]
    rcases
        uniform_taylor_remainder_norm_le_on_compact_convex
          (f := F) (K := closedBall p (a + 1))
          haug hcompact (convex_closedBall p (a + 1)) θ hθ_pos with
      ⟨ρ, hρ_pos, hrem⟩
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), C * ‖s‖ ≤ ρ :=
      eventually_const_mul_norm_le_nhds_zero hC_nonneg hρ_pos
    filter_upwards [hpert, hclose, hsmall] with s hs hsclose hsmall_s
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    let base : X := β z τ
    let q : X := β (z + s • η) τ
    let A : X →L[ℝ] X := secondVariationFlowOperator Γ base
    have hbase_mem_small : base ∈ closedBall p a := by
      simpa [base] using hbase_mem τ hτIcc
    have hq_mem_small : q ∈ closedBall p a := by
      simpa [q] using hs.2.2 τ hτIcc
    have hbase_mem_wide : base ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hbase_mem_small
    have hq_mem_wide : q ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hq_mem_small
    have hdiff : ‖q - base‖ ≤ C * ‖s‖ := by
      simpa [q, base] using hsclose τ hτ
    have hcloseρ : ‖q - base‖ ≤ ρ := hdiff.trans hsmall_s
    have hremθ :
        ‖F q - F base - A (q - base)‖ ≤ θ * ‖q - base‖ := by
      simpa [A, secondVariationFlowOperator, F] using
        hrem base hbase_mem_wide q hq_mem_wide hcloseρ
    have hremμ :
        ‖F q - F base - A (q - base)‖ ≤ μ * ‖s‖ := by
      calc
        ‖F q - F base - A (q - base)‖
            ≤ θ * ‖q - base‖ := hremθ
        _ ≤ θ * (C * ‖s‖) :=
          mul_le_mul_of_nonneg_left hdiff hθ_pos.le
        _ = (θ * C) * ‖s‖ := by ring
        _ ≤ μ * ‖s‖ :=
          mul_le_mul_of_nonneg_right hθC_le (norm_nonneg s)
    have hbase_nhds : closedBall p (a + 1) ∈ 𝓝 base :=
      closedBall_radius_add_one_mem_nhds hbase_mem_small
    have hAnorm : ‖A‖ ≤ (K : ℝ) := by
      have hfd : ‖fderiv ℝ F base‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hbase_nhds hLip
      simpa [A, secondVariationFlowOperator, F] using hfd
    have hlinear :
        ‖A (q - base - s • Ξ τ)‖ ≤
          (K : ℝ) * ‖q - base - s • Ξ τ‖ := by
      calc
        ‖A (q - base - s • Ξ τ)‖
            ≤ ‖A‖ * ‖q - base - s • Ξ τ‖ :=
          ContinuousLinearMap.le_opNorm A (q - base - s • Ξ τ)
        _ ≤ (K : ℝ) * ‖q - base - s • Ξ τ‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hraw :
        ‖Rder s τ‖ ≤
          (K : ℝ) * ‖q - base - s • Ξ τ‖ + μ * ‖s‖ :=
      residual_derivative_norm_bound_of_taylor_remainder
        (F := F) (A := A) (q := q) (γ := base) (ψ := Ξ τ)
        (R' := Rder s τ) (K := (K : ℝ)) (η := μ) (s := s)
        (by
          simp [Rder, A, q, base, F])
        hlinear hremμ
    simpa [R, Rder, q, base] using hraw
  have hunif :
      ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
        ∀ τ ∈ Icc (0 : ℝ) T, ‖R s τ‖ ≤ ε * ‖s‖ :=
    residual_uniform_isLittleO_on_Icc_of_gronwall_bound
      (R := R) (R' := Rder) hT_nonneg K.2 hRcont hRderiv hR0 hbound
  have hres :
      (fun s : ℝ => R s t) =o[𝓝 (0 : ℝ)] (fun s : ℝ => s) :=
    residual_isLittleO_at_fixedTime_of_uniform (R := R) hunif ht
  have hres' :
      (fun s : ℝ => β (z + s • η) t - β z t - s • Ξ t)
        =o[𝓝 (0 : ℝ)] (fun s : ℝ => s) := by
    simpa only [R]
      using hres
  rw [hasDerivAt_iff_isLittleO]
  simpa only [zero_smul, add_zero, sub_zero] using hres'

end Poincare
