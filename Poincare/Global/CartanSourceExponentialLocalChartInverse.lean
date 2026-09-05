import Poincare.Global.CartanSourceExponentialLocalChartStationary

/-!
# The concrete one-chart source exponential inverse

This file completes the coordinate-level parameterized inverse-function
construction begun in `CartanSourceExponentialLocalChartSelector`.

One regular variational selector evolves all nearby anchor/velocity initial
states in a fixed chart.  At a suitably small positive time `T`, velocity is
normalized by `T⁻¹`.  ODE uniqueness then compares the central-anchor slice
with the public fixed-time exponential package, so its velocity derivative is
the identity.  The stationary selector theorem supplies the anchor slice.
Together with joint strict differentiability, the block derivative is the
invertible shear and yields one product partial homeomorphism with a jointly
continuous inverse.

This remains a coordinate product theorem.  Passing its inverse velocity to
the varying anchor chart requires postcomposition with the chart-transition
derivative; that manifold `LocalFamily` transport is deliberately separate.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanSourceExponentialLocalChartSelector

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
For one retained selector, some protected positive time makes the normalized
central-anchor endpoint germ equal to the public charted exponential germ.
Both curves solve the same fixed-chart ODE; interval uniqueness is applied on
a common closed ball.
-/
theorem exists_normalizedSelectorTime_velocity_eventuallyEq_chart_expAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E))) :
    ∃ T > (0 : ℝ),
      T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
      (fun w : E =>
        normalizedSelectorEndpoint g x₀ H T (extChartAt I x₀ x₀, w))
        =ᶠ[𝓝 (0 : E)]
      (fun w : E =>
        extChartAt I x₀ (GeodesicTransport.expAt g x₀ w)) := by
  rcases GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc
      (g := g) (x₀ := x₀) with
    ⟨tau, htau, deltaPublic, hdeltaPublic, epsilonPublic, hepsilonPublic,
      a, alpha, halpha, hexp⟩
  let T : ℝ := min (H.epsilon / 4) (min tau epsilonPublic)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min (div_pos H.epsilon_pos (by norm_num))
      (lt_min htau hepsilonPublic)
  have hT_le_quarter : T ≤ H.epsilon / 4 := by
    dsimp [T]
    exact min_le_left _ _
  have hT_le_tau : T ≤ tau := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hT_le_epsilonPublic : T ≤ epsilonPublic := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hTprotected : T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) := by
    constructor <;> linarith [H.epsilon_pos]
  let delta : ℝ := min deltaPublic (H.initialRadius : ℝ)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaPublic (by exact_mod_cast H.initialRadius_pos)
  refine ⟨T, hT, hTprotected, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : E) (mul_pos hT hdelta)] with w hw
  have hwNorm : ‖w‖ < T * delta := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  let v : E := T⁻¹ • w
  have hv : ‖v‖ < delta := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    calc
      T⁻¹ * ‖w‖ < T⁻¹ * (T * delta) :=
        mul_lt_mul_of_pos_left hwNorm (inv_pos.mpr hT)
      _ = delta := by field_simp [ne_of_gt hT]
  have hvPublic : ‖v‖ < deltaPublic :=
    hv.trans_le (by dsimp [delta]; exact min_le_left _ _)
  have hvSelector : ‖v‖ < (H.initialRadius : ℝ) :=
    hv.trans_le (by dsimp [delta]; exact min_le_right _ _)
  have hscale : T • v = w := by
    simp [v, smul_smul, ne_of_gt hT]
  let B := H.projectFirstVariational
  have hvInitial : (extChartAt I x₀ x₀, v) ∈
      closedBall (extChartAt I x₀ x₀, (0 : E))
        (B.initialRadius : ℝ) := by
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self,
      max_eq_right (dist_nonneg : 0 ≤ dist v (0 : E))]
    simpa [dist_eq_norm] using hvSelector.le
  have hB := B.selector_data (extChartAt I x₀ x₀, v) hvInitial
  rcases halpha v hvPublic with
    ⟨halphaZero, halphaDeriv, halphaMem, halphaTarget, _halphaHom⟩
  let F : E × E → E × E := fixedChartGeodesicField g x₀
  let gammaSelector : ℝ → E × E :=
    B.selector (extChartAt I x₀ x₀, v)
  let gammaPublic : ℝ → E × E :=
    alpha (extChartAt I x₀ x₀, v)
  let center : E × E := (extChartAt I x₀ x₀, (0 : E))
  let radius : ℝ := max (H.tubeRadius : ℝ) (a : ℝ)
  have hSelectorInterval : Icc (0 : ℝ) T ⊆
      Icc (-H.epsilon) H.epsilon := by
    intro t ht
    exact ⟨by linarith [H.epsilon_pos, ht.1],
      ht.2.trans (hT_le_quarter.trans (by linarith [H.epsilon_pos]))⟩
  have hPublicInterval : Icc (0 : ℝ) T ⊆
      Icc (-epsilonPublic) epsilonPublic := by
    intro t ht
    exact ⟨by linarith [hepsilonPublic, ht.1],
      ht.2.trans hT_le_epsilonPublic⟩
  have hSelectorDeriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt gammaSelector (F (gammaSelector t))
        (Icc (0 : ℝ) T) t := by
    intro t ht
    simpa [gammaSelector, F, fixedChartGeodesicField] using
      (hB.2.1 t (hSelectorInterval ht)).mono hSelectorInterval
  have hPublicDeriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt gammaPublic (F (gammaPublic t))
        (Icc (0 : ℝ) T) t := by
    intro t ht
    simpa [gammaPublic, F, fixedChartGeodesicField] using
      (halphaDeriv t (hPublicInterval ht)).mono hPublicInterval
  have hSelectorMem : ∀ t ∈ Icc (0 : ℝ) T,
      gammaSelector t ∈ closedBall center radius := by
    intro t ht
    exact closedBall_subset_closedBall
      (by dsimp [radius]; exact le_max_left _ _)
      (by simpa [gammaSelector, center, B] using
        hB.2.2 t (hSelectorInterval ht))
  have hPublicMem : ∀ t ∈ Icc (0 : ℝ) T,
      gammaPublic t ∈ closedBall center radius := by
    intro t ht
    exact closedBall_subset_closedBall
      (by dsimp [radius]; exact le_max_right _ _)
      (by simpa [gammaPublic, center] using
        halphaMem t (hPublicInterval ht))
  rcases
      GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        g x₀ center radius with
    ⟨K, hLip⟩
  have hSelectorContinuous : ContinuousOn gammaSelector (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn hSelectorDeriv
  have hPublicContinuous : ContinuousOn gammaPublic (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn hPublicDeriv
  have hInitial : gammaSelector 0 = gammaPublic 0 := by
    rw [show gammaSelector 0 = (extChartAt I x₀ x₀, v) by
      simpa [gammaSelector] using hB.1]
    rw [show gammaPublic 0 = (extChartAt I x₀ x₀, v) by
      simpa [gammaPublic] using halphaZero]
  have hEq : EqOn gammaSelector gammaPublic (Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ => F)
      (s := fun _ : ℝ => closedBall center radius)
      (K := K) ?_ hSelectorContinuous ?_ ?_
        hPublicContinuous ?_ ?_ hInitial
    · intro _t _ht
      simpa [F, fixedChartGeodesicField] using hLip
    · intro t ht
      exact
        (hSelectorDeriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
    · intro t ht
      exact hSelectorMem t (Ico_subset_Icc_self ht)
    · intro t ht
      exact
        (hPublicDeriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
    · intro t ht
      exact hPublicMem t (Ico_subset_Icc_self ht)
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hstateT : gammaSelector T = gammaPublic T := hEq hTmem
  have hTtau : T ∈ Icc (0 : ℝ) tau := ⟨hT.le, hT_le_tau⟩
  have hTpublic : T ∈ Icc (-epsilonPublic) epsilonPublic :=
    hPublicInterval hTmem
  have hchartExp :
      extChartAt I x₀ (GeodesicTransport.expAt g x₀ w) =
        (gammaPublic T).1 := by
    rw [← hscale, hexp v hvPublic T hTtau]
    apply (extChartAt I x₀).right_inv
    simpa [gammaPublic] using halphaTarget T hTpublic
  calc
    normalizedSelectorEndpoint g x₀ H T (extChartAt I x₀ x₀, w) =
        (gammaSelector T).1 := by
      simp [normalizedSelectorEndpoint, gammaSelector, B, v]
    _ = (gammaPublic T).1 := congrArg Prod.fst hstateT
    _ = extChartAt I x₀ (GeodesicTransport.expAt g x₀ w) := hchartExp.symm

/-- Identity derivative of the normalized central velocity slice. -/
theorem exists_normalizedSelectorTime_velocity_hasStrictFDerivAt_id
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E))) :
    ∃ T > (0 : ℝ),
      T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
      HasStrictFDerivAt
        (fun w : E =>
          normalizedSelectorEndpoint g x₀ H T (extChartAt I x₀ x₀, w))
        (ContinuousLinearMap.id ℝ E) 0 := by
  rcases exists_normalizedSelectorTime_velocity_eventuallyEq_chart_expAt
      g x₀ H with ⟨T, hT, hTprotected, heq⟩
  refine ⟨T, hT, hTprotected, ?_⟩
  exact
    (GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
      (g := g) (x₀ := x₀)).congr_of_eventuallyEq heq.symm

/-- The stationary theorem, rewritten for the normalized endpoint map. -/
theorem normalizedSelectorEndpoint_anchor_eventuallyEq_id
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E)))
    {T : ℝ} (hT : T ∈ Icc (-H.epsilon) H.epsilon) :
    (fun z : E => normalizedSelectorEndpoint g x₀ H T (z, 0))
      =ᶠ[𝓝 (extChartAt I x₀ x₀)] id := by
  filter_upwards [Metric.ball_mem_nhds (extChartAt I x₀ x₀)
      (by exact_mod_cast H.initialRadius_pos)] with z hz
  have hzClosed : z ∈
      closedBall (extChartAt I x₀ x₀) (H.initialRadius : ℝ) :=
    ball_subset_closedBall hz
  have hzState : (z, (0 : E)) ∈
      closedBall (extChartAt I x₀ x₀, (0 : E))
        (H.initialRadius : ℝ) := by
    rw [Metric.mem_closedBall, Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ dist z (extChartAt I x₀ x₀))]
    exact mem_closedBall.mp hzClosed
  have hstationary :=
    projectedSelector_zeroVelocity_fst_eq_anchor g x₀ H hzState hT
  simpa [normalizedSelectorEndpoint] using hstationary

/--
At the selected normalized time, both endpoint slices have identity strict
derivative and the complete endpoint map is jointly strictly differentiable.
-/
theorem exists_normalizedSelectorTime_complete_derivative_data
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E))) :
    ∃ T > (0 : ℝ),
      ∃ D : (E × E) →L[ℝ] E,
        T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
        HasStrictFDerivAt (normalizedSelectorEndpoint g x₀ H T) D
          (extChartAt I x₀ x₀, (0 : E)) ∧
        HasStrictFDerivAt
          (fun z : E => normalizedSelectorEndpoint g x₀ H T (z, 0))
          (ContinuousLinearMap.id ℝ E) (extChartAt I x₀ x₀) ∧
        HasStrictFDerivAt
          (fun w : E =>
            normalizedSelectorEndpoint g x₀ H T (extChartAt I x₀ x₀, w))
          (ContinuousLinearMap.id ℝ E) 0 := by
  rcases exists_normalizedSelectorTime_velocity_hasStrictFDerivAt_id
      g x₀ H with ⟨T, hT, hTprotected, hvelocity⟩
  rcases normalizedSelectorEndpoint_exists_hasStrictFDerivAt
      g x₀ H hTprotected with ⟨D, hjoint⟩
  have hTfull : T ∈ Icc (-H.epsilon) H.epsilon := by
    constructor <;> linarith [hTprotected.1, hTprotected.2, H.epsilon_pos]
  have hanchorEq := normalizedSelectorEndpoint_anchor_eventuallyEq_id
    g x₀ H hTfull
  have hanchor : HasStrictFDerivAt
      (fun z : E => normalizedSelectorEndpoint g x₀ H T (z, 0))
      (ContinuousLinearMap.id ℝ E) (extChartAt I x₀ x₀) :=
    (hasStrictFDerivAt_id (extChartAt I x₀ x₀)).congr_of_eventuallyEq
      hanchorEq.symm
  exact ⟨T, hT, D, hTprotected, hjoint, hanchor, hvelocity⟩

/--
The concrete product inverse-function theorem for one fixed chart.  The
forward map is exactly `(anchor, normal velocity) |-> (anchor, endpoint)`;
its inverse is jointly continuous by the `OpenPartialHomeomorph` package.
-/
theorem exists_normalizedSelector_anchorEndpointOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (H : LocalRegularControlledContinuousAutonomousSelector
      (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
      ((extChartAt I x₀ x₀, (0 : E)),
        ContinuousLinearMap.id ℝ (E × E))) :
    ∃ T > (0 : ℝ), ∃ D : (E × E) →L[ℝ] E,
      ∃ U : OpenPartialHomeomorph (E × E) (E × E),
        T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
        HasStrictFDerivAt (normalizedSelectorEndpoint g x₀ H T) D
          (extChartAt I x₀ x₀, (0 : E)) ∧
        HasStrictFDerivAt
          (fun q : E × E =>
            (q.1, normalizedSelectorEndpoint g x₀ H T q))
          (anchorEndpointShear (X := E) : (E × E) →L[ℝ] (E × E))
          (extChartAt I x₀ x₀, (0 : E)) ∧
        (U : (E × E) → (E × E)) =
          (fun q : E × E =>
            (q.1, normalizedSelectorEndpoint g x₀ H T q)) ∧
        (extChartAt I x₀ x₀, (0 : E)) ∈ U.source ∧
        (extChartAt I x₀ x₀, extChartAt I x₀ x₀) ∈ U.target := by
  rcases exists_normalizedSelectorTime_complete_derivative_data
      g x₀ H with
    ⟨T, hT, D, hTprotected, hjoint, hanchor, hvelocity⟩
  let endpoint : E × E → E := normalizedSelectorEndpoint g x₀ H T
  let z₀ : E := extChartAt I x₀ x₀
  let U : OpenPartialHomeomorph (E × E) (E × E) :=
    anchorEndpointOpenPartialHomeomorph endpoint z₀ D hjoint
      hanchor.hasFDerivAt hvelocity.hasFDerivAt
  have hproduct : HasStrictFDerivAt
      (fun q : E × E => (q.1, endpoint q))
      (anchorEndpointShear (X := E) : (E × E) →L[ℝ] (E × E)) (z₀, 0) :=
    hasStrictFDerivAt_anchorEndpoint_of_slice_derivatives
      endpoint z₀ D hjoint hanchor.hasFDerivAt hvelocity.hasFDerivAt
  have hUcoe : (U : (E × E) → (E × E)) =
      (fun q : E × E => (q.1, endpoint q)) := by
    funext q
    exact anchorEndpointOpenPartialHomeomorph_apply
      endpoint z₀ D hjoint hanchor.hasFDerivAt hvelocity.hasFDerivAt q
  have hsource : (z₀, (0 : E)) ∈ U.source := by
    exact center_mem_anchorEndpointOpenPartialHomeomorph_source
      endpoint z₀ D hjoint hanchor.hasFDerivAt hvelocity.hasFDerivAt
  have hendpointCenter : endpoint (z₀, (0 : E)) = z₀ := by
    have hTfull : T ∈ Icc (-H.epsilon) H.epsilon := by
      constructor <;> linarith [hTprotected.1, hTprotected.2, H.epsilon_pos]
    exact (normalizedSelectorEndpoint_anchor_eventuallyEq_id
      g x₀ H hTfull).self_of_nhds
  have htargetRaw : (z₀, endpoint (z₀, (0 : E))) ∈ U.target := by
    exact center_image_mem_anchorEndpointOpenPartialHomeomorph_target
      endpoint z₀ D hjoint hanchor.hasFDerivAt hvelocity.hasFDerivAt
  refine ⟨T, hT, D, U, hTprotected, hjoint, ?_, ?_, hsource, ?_⟩
  · simpa [endpoint, z₀] using hproduct
  · simpa [endpoint] using hUcoe
  · simpa [hendpointCenter] using htargetRaw

/--
Every prescribed neighborhood of the central fixed-chart state admits a
concrete joint inverse package whose selector remains protected inside that
same neighborhood.
-/
theorem exists_fixedChart_anchorEndpointOpenPartialHomeomorph_with_projected_protectedInnerBall_subset
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {U : Set (E × E)}
    (hU : U ∈ nhds (extChartAt I x₀ x₀, (0 : E))) :
    ∃ H : LocalRegularControlledContinuousAutonomousSelector
        (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
        ((extChartAt I x₀ x₀, (0 : E)),
          ContinuousLinearMap.id ℝ (E × E)),
      closedBall (extChartAt I x₀ x₀, (0 : E))
          H.projectFirstVariational.protectedInnerRadius ⊆ U ∧
      ∃ T > (0 : ℝ), ∃ D : (E × E) →L[ℝ] E,
        ∃ P : OpenPartialHomeomorph (E × E) (E × E),
          T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
          HasStrictFDerivAt (normalizedSelectorEndpoint g x₀ H T) D
            (extChartAt I x₀ x₀, (0 : E)) ∧
          (P : (E × E) → (E × E)) =
            (fun q : E × E =>
              (q.1, normalizedSelectorEndpoint g x₀ H T q)) ∧
          (extChartAt I x₀ x₀, (0 : E)) ∈ P.source ∧
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) ∈ P.target := by
  rcases
      exists_regularVariationalSelector_fixedChart_with_projected_protectedInnerBall_subset
        g x₀ hU with ⟨H, hprotected⟩
  rcases exists_normalizedSelector_anchorEndpointOpenPartialHomeomorph
      g x₀ H with
    ⟨T, hT, D, P, hTprotected, hjoint, _hproduct, hPapply,
      hcenterSource, hcenterTarget⟩
  exact ⟨H, hprotected, T, hT, D, P, hTprotected, hjoint, hPapply,
    hcenterSource, hcenterTarget⟩

/-- Every fixed manifold chart admits the concrete joint inverse package. -/
theorem exists_fixedChart_anchorEndpointOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ H : LocalRegularControlledContinuousAutonomousSelector
        (firstVariationalAugmentedField (fixedChartGeodesicField g x₀))
        ((extChartAt I x₀ x₀, (0 : E)),
          ContinuousLinearMap.id ℝ (E × E)),
      ∃ T > (0 : ℝ), ∃ D : (E × E) →L[ℝ] E,
        ∃ U : OpenPartialHomeomorph (E × E) (E × E),
          T ∈ Ioo (-(H.epsilon / 2)) (H.epsilon / 2) ∧
          HasStrictFDerivAt (normalizedSelectorEndpoint g x₀ H T) D
            (extChartAt I x₀ x₀, (0 : E)) ∧
          (U : (E × E) → (E × E)) =
            (fun q : E × E =>
              (q.1, normalizedSelectorEndpoint g x₀ H T q)) ∧
          (extChartAt I x₀ x₀, (0 : E)) ∈ U.source ∧
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) ∈ U.target := by
  rcases
      exists_fixedChart_anchorEndpointOpenPartialHomeomorph_with_projected_protectedInnerBall_subset
        g x₀ (U := Set.univ) Filter.univ_mem with
    ⟨H, _hprotected, T, hT, D, U, hTprotected, hjoint, hUcoe,
      hsource, htarget⟩
  exact ⟨H, T, hT, D, U, hTprotected, hjoint, hUcoe, hsource, htarget⟩

end CartanSourceExponentialLocalChartSelector
end Poincare
