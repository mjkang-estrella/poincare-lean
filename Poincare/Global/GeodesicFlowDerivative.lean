import Poincare.Global.GeodesicDerivativeFinal

/-!
# Initial-velocity derivative for the uniform chart geodesic flow

This module instantiates the abstract residual Gronwall layer from
`Poincare.Global.GeodesicDerivativeFinal` for the Picard-Lindelöf chart
geodesic flow.  The residual derivative is computed from the two flow ODEs and
the linearized equation; the growth estimate uses the compact-uniform Taylor
remainder on a widened common PL ball and fixed-time Lipschitz dependence in the
initial velocity.
-/

noncomputable section

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Time derivative candidate for the initial-velocity residual. -/
def initialVelocityResidualDeriv
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (α : E × E → ℝ → E × E) (z₀ v w : E) (Ψ : ℝ → E × E)
    (s t : ℝ) : E × E :=
  geodesicFlowField Γ (α (z₀, v + s • w) t) -
    geodesicFlowField Γ (α (z₀, v) t) -
      s • linearizedGeodesicFlowFieldAlong Γ (α (z₀, v)) t (Ψ t)

/--
Differentiating the residual in time: the two nonlinear curves contribute the
geodesic flow field and the linearized curve contributes the linearized field.
-/
theorem initialVelocityResidual_hasDerivWithinAt_of_flow_linearized
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {s t : ℝ} {S : Set ℝ}
    (hpert : HasDerivWithinAt (α (z₀, v + s • w))
      (geodesicFlowField Γ (α (z₀, v + s • w) t)) S t)
    (hbase : HasDerivWithinAt (α (z₀, v))
      (geodesicFlowField Γ (α (z₀, v) t)) S t)
    (hΨ : HasDerivWithinAt Ψ
      (linearizedGeodesicFlowFieldAlong Γ (α (z₀, v)) t (Ψ t)) S t) :
    HasDerivWithinAt
      (fun τ : ℝ => initialVelocityResidual α z₀ v w Ψ s τ)
      (initialVelocityResidualDeriv Γ α z₀ v w Ψ s t) S t := by
  simpa [initialVelocityResidual, initialVelocityResidualDeriv] using
    (hpert.sub hbase).sub (hΨ.const_smul s)

/-- A fixed multiple of `‖s‖` is eventually below any positive threshold. -/
theorem eventually_const_mul_norm_le_nhds_zero {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), C * ‖s‖ ≤ δ := by
  have hden : 0 < C + 1 := by linarith
  have hball :
      Metric.ball (0 : ℝ) (δ / (C + 1)) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds _ (div_pos hδ hden)
  filter_upwards [hball] with s hs
  have hs_norm : ‖s‖ < δ / (C + 1) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  exact le_of_lt <| by
    calc
      C * ‖s‖ ≤ (C + 1) * ‖s‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg s)
      _ < (C + 1) * (δ / (C + 1)) :=
        mul_lt_mul_of_pos_left hs_norm hden
      _ = δ := by
        field_simp [ne_of_gt hden]

/--
If a point lies in a closed ball of radius `a`, then the ball of radius
`a + 1` around the same center is a neighborhood of that point.
-/
theorem closedBall_radius_add_one_mem_nhds
    {X : Type*} [PseudoMetricSpace X] {p x : X} {a : ℝ}
    (hx : x ∈ closedBall p a) :
    closedBall p (a + 1) ∈ 𝓝 x := by
  refine mem_of_superset (Metric.ball_mem_nhds x zero_lt_one) ?_
  intro y hy
  have hyx : dist y x < 1 := by
    simpa [Metric.mem_ball] using hy
  have hxp : dist x p ≤ a := by
    simpa [Metric.mem_closedBall] using hx
  rw [Metric.mem_closedBall]
  calc
    dist y p ≤ dist y x + dist x p := dist_triangle y x p
    _ ≤ 1 + a := by linarith
    _ = a + 1 := by ring

/-- Small scalar perturbations of an interior velocity remain in the velocity ball. -/
theorem eventually_norm_add_smul_lt
    {v w : E} {δ : ℝ} (hv : ‖v‖ < δ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ‖v + s • w‖ < δ := by
  have htend :
      Tendsto (fun s : ℝ => v + s • w) (𝓝 (0 : ℝ)) (𝓝 v) := by
    have htend0 :
        Tendsto (fun s : ℝ => v + s • w) (𝓝 (0 : ℝ)) (𝓝 (v + (0 : ℝ) • w)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
        ContinuousAt (fun s : ℝ => v + s • w) 0)
    simpa using htend0
  have hvball : v ∈ ball (0 : E) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  exact (htend.eventually (Metric.isOpen_ball.mem_nhds hvball)).mono fun s hs => by
    simpa [Metric.mem_ball, dist_eq_norm] using hs

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
The fixed-time derivative of the uniform PL chart geodesic flow with respect to
the initial velocity, in the direction `w`, is the solution of the linearized
geodesic equation.

The hypotheses are exactly the already exported common-flow data plus a
linearized solution on the same interval.  The proof discharges the residual
Gronwall hypotheses from the flow ODE, zero initial residual, compact-uniform
Taylor remainder, and Lipschitz dependence on the initial velocity.
-/
theorem chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ ε : ℝ} {a : ℝ≥0} {α : E × E → ℝ → E × E}
    {v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hε : 0 < ε) (hv : ‖v‖ < δ)
    (hα : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ τ ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) τ))
            (Icc (-ε) ε) τ) ∧
        ∀ τ ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) τ ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) a)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨder : ∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) τ (Ψ τ))
        (Icc (-ε) ε) τ)
    (ht : t ∈ Icc (0 : ℝ) ε) :
    HasDerivAt
      (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
      (Ψ t) 0 := by
  let z₀ : E := extChartAt I x₀ x₀
  let p₀ : E × E := (z₀, (0 : E))
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : E × E → E × E := geodesicFlowField Γ
  rcases geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      (g := g) (x₀ := x₀) (p := p₀) (a := (a : ℝ) + 1) with
    ⟨K, hLipF⟩
  let C : ℝ := Real.exp ((K : ℝ) * ε) * ‖w‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hIcc_subset : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := by
    intro τ hτ
    exact ⟨by linarith [hτ.1, hε], hτ.2⟩
  have hIco_subset : Ico (0 : ℝ) ε ⊆ Icc (-ε) ε := by
    intro τ hτ
    exact hIcc_subset (Ico_subset_Icc_self hτ)
  have hbase := hα v hv
  have hvel_eventually :
      ∀ᶠ s in 𝓝 (0 : ℝ), ‖v + s • w‖ < δ :=
    eventually_norm_add_smul_lt (v := v) (w := w) hv
  have hRcont : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContinuousOn
        (fun τ : ℝ => initialVelocityResidual α z₀ v w Ψ s τ)
        (Icc (0 : ℝ) ε) := by
    filter_upwards [hvel_eventually] with s hs
    have hpert := hα (v + s • w) hs
    have hqcont : ContinuousOn (α (z₀, v + s • w)) (Icc (0 : ℝ) ε) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun τ => F (α (z₀, v + s • w) τ)) ?_
      intro τ hτ
      simpa [F, Γ, z₀] using
        (hpert.2.1 τ (hIcc_subset hτ)).mono hIcc_subset
    have hbasecont : ContinuousOn (α (z₀, v)) (Icc (0 : ℝ) ε) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun τ => F (α (z₀, v) τ)) ?_
      intro τ hτ
      simpa [F, Γ, z₀] using
        (hbase.2.1 τ (hIcc_subset hτ)).mono hIcc_subset
    have hΨcont : ContinuousOn Ψ (Icc (0 : ℝ) ε) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun τ =>
          linearizedGeodesicFlowFieldAlong Γ (α (z₀, v)) τ (Ψ τ)) ?_
      intro τ hτ
      simpa [Γ, z₀] using (hΨder τ (hIcc_subset hτ)).mono hIcc_subset
    simpa [initialVelocityResidual] using
      (hqcont.sub hbasecont).sub (hΨcont.const_smul s)
  have hRderiv : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) ε,
        HasDerivWithinAt
          (fun r : ℝ => initialVelocityResidual α z₀ v w Ψ s r)
          (initialVelocityResidualDeriv Γ α z₀ v w Ψ s τ) (Ici τ) τ := by
    filter_upwards [hvel_eventually] with s hs
    intro τ hτ
    have hτfull : τ ∈ Icc (-ε) ε := hIco_subset hτ
    have hnhds : Icc (-ε) ε ∈ 𝓝[Ici τ] τ :=
      Icc_mem_nhdsGE_of_mem ⟨hτfull.1, hτ.2⟩
    have hpert := hα (v + s • w) hs
    have hpert_der :
        HasDerivWithinAt (α (z₀, v + s • w))
          (F (α (z₀, v + s • w) τ)) (Ici τ) τ := by
      simpa [F, Γ, z₀] using
        (hpert.2.1 τ hτfull).mono_of_mem_nhdsWithin hnhds
    have hbase_der :
        HasDerivWithinAt (α (z₀, v))
          (F (α (z₀, v) τ)) (Ici τ) τ := by
      simpa [F, Γ, z₀] using
        (hbase.2.1 τ hτfull).mono_of_mem_nhdsWithin hnhds
    have hΨ_der :
        HasDerivWithinAt Ψ
          (linearizedGeodesicFlowFieldAlong Γ (α (z₀, v)) τ (Ψ τ))
          (Ici τ) τ := by
      simpa [Γ, z₀] using
        (hΨder τ hτfull).mono_of_mem_nhdsWithin hnhds
    exact initialVelocityResidual_hasDerivWithinAt_of_flow_linearized
      (Γ := Γ) (α := α) (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ)
      (s := s) (t := τ) hpert_der hbase_der hΨ_der
  have hR0 : ∀ᶠ s in 𝓝 (0 : ℝ),
      initialVelocityResidual α z₀ v w Ψ s 0 = 0 := by
    filter_upwards [hvel_eventually] with s hs
    have hpert := hα (v + s • w) hs
    have hpert0 : α (z₀, v + s • w) 0 = (z₀, v + s • w) := by
      simpa [z₀] using hpert.1
    have hbase0 : α (z₀, v) 0 = (z₀, v) := by
      simpa [z₀] using hbase.1
    ext <;> simp [initialVelocityResidual, hpert0, hbase0, hΨ0]
  have hTaylor :
      ∀ θ > (0 : ℝ), ∃ ρ > (0 : ℝ),
        ∀ base ∈ closedBall p₀ ((a : ℝ) + 1),
        ∀ q ∈ closedBall p₀ ((a : ℝ) + 1),
          ‖q - base‖ ≤ ρ →
            ‖F q - F base -
                linearizedGeodesicFlowOperator Γ base (q - base)‖ ≤
              θ * ‖q - base‖ := by
    simpa [F, Γ] using
      geodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
        (Γ := Γ)
        (K := closedBall p₀ ((a : ℝ) + 1))
        (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff
          (g := g) (x₀ := x₀))
        (isCompact_closedBall p₀ ((a : ℝ) + 1))
        (convex_closedBall p₀ ((a : ℝ) + 1))
  have hbound : ∀ η > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) ε,
        ‖initialVelocityResidualDeriv Γ α z₀ v w Ψ s τ‖ ≤
          (K : ℝ) * ‖initialVelocityResidual α z₀ v w Ψ s τ‖ +
            η * ‖s‖ := by
    intro η hη
    let θ : ℝ := η / (C + 1)
    have hden_pos : 0 < C + 1 := by positivity
    have hθ_pos : 0 < θ := by
      dsimp [θ]
      positivity
    have hθC_le : θ * C ≤ η := by
      dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      nlinarith [hη.le, hC_nonneg]
    rcases hTaylor θ hθ_pos with ⟨ρ, hρ_pos, hrem⟩
    have hsmall :
        ∀ᶠ s in 𝓝 (0 : ℝ), C * ‖s‖ ≤ ρ :=
      eventually_const_mul_norm_le_nhds_zero hC_nonneg hρ_pos
    filter_upwards [hvel_eventually, hsmall] with s hs hsmall_s
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) ε := Ico_subset_Icc_self hτ
    have hτfull : τ ∈ Icc (-ε) ε := hIco_subset hτ
    have hpert := hα (v + s • w) hs
    let base : E × E := α (z₀, v) τ
    let q : E × E := α (z₀, v + s • w) τ
    have hbase_mem_small :
        base ∈ closedBall p₀ (a : ℝ) := by
      simpa [base, p₀, z₀] using hbase.2.2 τ hτfull
    have hq_mem_small :
        q ∈ closedBall p₀ (a : ℝ) := by
      simpa [q, p₀, z₀] using hpert.2.2 τ hτfull
    have hbase_mem :
        base ∈ closedBall p₀ ((a : ℝ) + 1) :=
      closedBall_subset_closedBall (by linarith [NNReal.coe_nonneg a]) hbase_mem_small
    have hq_mem :
        q ∈ closedBall p₀ ((a : ℝ) + 1) :=
      closedBall_subset_closedBall (by linarith [NNReal.coe_nonneg a]) hq_mem_small
    have hstate_lip :
        LipschitzOnWith
          ⟨Real.exp ((K : ℝ) * ε), (Real.exp_pos _).le⟩
          (fun u : E => α (z₀, u) τ)
          (ball (0 : E) δ) :=
      chart_flow_initialVelocity_lipschitzOn_of_ODE
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε)
        (a := (a : ℝ) + 1) (K := K) (α := α)
        hε hLipF
        (fun u hu => (hα u hu).1)
        (fun u hu r hr => (hα u hu).2.1 r hr)
        (fun u hu r hr =>
          closedBall_subset_closedBall
            (by linarith [NNReal.coe_nonneg a]) ((hα u hu).2.2 r hr))
        hτIcc
    have hvball : v ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    have hsball : v + s • w ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hdiff : ‖q - base‖ ≤ C * ‖s‖ := by
      have hdist :=
        hstate_lip.dist_le_mul (v + s • w) hsball v hvball
      calc
        ‖q - base‖ = dist q base := by
          rw [dist_eq_norm]
        _ ≤ Real.exp ((K : ℝ) * ε) * dist (v + s • w) v := by
          simpa [q, base, z₀] using hdist
        _ = Real.exp ((K : ℝ) * ε) * ‖s • w‖ := by
          simp [dist_eq_norm]
        _ = C * ‖s‖ := by
          simp [C, norm_smul]
          ring
    have hclose : ‖q - base‖ ≤ ρ := hdiff.trans hsmall_s
    have hremθ :
        ‖F q - F base -
            linearizedGeodesicFlowOperator Γ base (q - base)‖ ≤
          θ * ‖q - base‖ :=
      hrem base hbase_mem q hq_mem hclose
    have hremη :
        ‖F q - F base -
            linearizedGeodesicFlowOperator Γ base (q - base)‖ ≤
          η * ‖s‖ := by
      calc
        ‖F q - F base -
            linearizedGeodesicFlowOperator Γ base (q - base)‖
            ≤ θ * ‖q - base‖ := hremθ
        _ ≤ θ * (C * ‖s‖) :=
          mul_le_mul_of_nonneg_left hdiff hθ_pos.le
        _ = (θ * C) * ‖s‖ := by ring
        _ ≤ η * ‖s‖ :=
          mul_le_mul_of_nonneg_right hθC_le (norm_nonneg s)
    have hbase_nhds :
        closedBall p₀ ((a : ℝ) + 1) ∈ 𝓝 base :=
      closedBall_radius_add_one_mem_nhds hbase_mem_small
    have hAnorm :
        ‖linearizedGeodesicFlowOperator Γ base‖ ≤ (K : ℝ) := by
      have hfd :
          ‖fderiv ℝ F base‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hbase_nhds hLipF
      simpa [linearizedGeodesicFlowOperator, F, Γ] using hfd
    have hlinear :
        ‖linearizedGeodesicFlowOperator Γ base
            (q - base - s • Ψ τ)‖ ≤
          (K : ℝ) * ‖q - base - s • Ψ τ‖ := by
      calc
        ‖linearizedGeodesicFlowOperator Γ base
            (q - base - s • Ψ τ)‖
            ≤ ‖linearizedGeodesicFlowOperator Γ base‖ *
                ‖q - base - s • Ψ τ‖ :=
          ContinuousLinearMap.le_opNorm
            (linearizedGeodesicFlowOperator Γ base)
            (q - base - s • Ψ τ)
        _ ≤ (K : ℝ) * ‖q - base - s • Ψ τ‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hraw :
        ‖initialVelocityResidualDeriv Γ α z₀ v w Ψ s τ‖ ≤
          (K : ℝ) * ‖q - base - s • Ψ τ‖ + η * ‖s‖ :=
      residual_derivative_norm_bound_of_taylor_remainder
        (F := F) (A := linearizedGeodesicFlowOperator Γ base)
        (q := q) (γ := base) (ψ := Ψ τ)
        (R' := initialVelocityResidualDeriv Γ α z₀ v w Ψ s τ)
        (K := (K : ℝ)) (η := η) (s := s)
        (by
          simp [initialVelocityResidualDeriv, linearizedGeodesicFlowFieldAlong,
            F, Γ, q, base])
        hlinear hremη
    simpa [initialVelocityResidual, q, base] using hraw
  exact
    initialVelocity_hasDerivAt_of_gronwall_residual_bound
      (α := α) (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ)
      (R' := initialVelocityResidualDeriv Γ α z₀ v w Ψ)
      (K := (K : ℝ)) (T := ε) hε.le K.2 hRcont hRderiv hR0 hbound ht

end GeodesicTransport
end Poincare
