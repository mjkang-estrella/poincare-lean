import Poincare.Global.GeodesicDependence

/-!
# Linearized chart geodesic equation

This module isolates the variational equation for the chart geodesic flow.
It deliberately stops before the full differentiability theorem: the verified
comparison currently available here is the pointwise first-order Taylor
remainder for the geodesic vector field.  Uniformizing that estimate on the
common compact tube is the remaining Grönwall input.
-/

noncomputable section

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The coordinate Jacobi acceleration term along a first-order chart state
`base = (γ, γ')`.

No symmetry of the Christoffel field is assumed here, so the two bilinear
velocity terms are kept separately.  Under the usual symmetry this is the
`-(DΓ)_γ(J)(γ',γ') - 2 Γ_γ(K,γ')` term.
-/
def coordinateJacobiAcceleration
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (base ψ : E × E) : E :=
  -((fderiv ℝ Γ base.1) ψ.1 base.2 base.2) -
    Γ base.1 ψ.2 base.2 - Γ base.1 base.2 ψ.2

/--
The shaped coordinate Jacobi operator at a first-order chart state.  Applied
to `ψ = (J,K)`, it gives `(K, coordinateJacobiAcceleration Γ base ψ)`.
-/
def coordinateJacobiFlowOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (base : E × E) :
    E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod
    ( -((ContinuousLinearMap.apply ℝ E base.2).comp
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) base.2).comp
          ((fderiv ℝ Γ base.1).comp (ContinuousLinearMap.fst ℝ E E)))) -
      ((ContinuousLinearMap.apply ℝ E base.2).comp
        ((Γ base.1).comp (ContinuousLinearMap.snd ℝ E E))) -
      ((Γ base.1 base.2).comp (ContinuousLinearMap.snd ℝ E E)) )

@[simp]
theorem coordinateJacobiFlowOperator_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (base ψ : E × E) :
    coordinateJacobiFlowOperator Γ base ψ =
      (ψ.2, coordinateJacobiAcceleration Γ base ψ) := by
  simp [coordinateJacobiFlowOperator, coordinateJacobiAcceleration]

/-- The Fréchet-linearization operator of the first-order chart geodesic flow. -/
def linearizedGeodesicFlowOperator
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (base : E × E) :
    E × E →L[ℝ] E × E :=
  fderiv ℝ (geodesicFlowField Γ) base

/--
The time-dependent linearized geodesic vector field along a chosen base chart
curve `γ`.
-/
def linearizedGeodesicFlowFieldAlong
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E × E) :
    ℝ → E × E → E × E :=
  fun t ψ ↦ linearizedGeodesicFlowOperator Γ (γ t) ψ

@[simp]
theorem linearizedGeodesicFlowFieldAlong_zero
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E × E) (t : ℝ) :
    linearizedGeodesicFlowFieldAlong Γ γ t 0 = 0 := by
  simp [linearizedGeodesicFlowFieldAlong, linearizedGeodesicFlowOperator]

theorem linearizedGeodesicFlowFieldAlong_add
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E × E) (t : ℝ)
    (ψ₁ ψ₂ : E × E) :
    linearizedGeodesicFlowFieldAlong Γ γ t (ψ₁ + ψ₂) =
      linearizedGeodesicFlowFieldAlong Γ γ t ψ₁ +
        linearizedGeodesicFlowFieldAlong Γ γ t ψ₂ := by
  simp [linearizedGeodesicFlowFieldAlong, linearizedGeodesicFlowOperator]

theorem linearizedGeodesicFlowFieldAlong_smul
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E × E) (t c : ℝ)
    (ψ : E × E) :
    linearizedGeodesicFlowFieldAlong Γ γ t (c • ψ) =
      c • linearizedGeodesicFlowFieldAlong Γ γ t ψ := by
  simp [linearizedGeodesicFlowFieldAlong, linearizedGeodesicFlowOperator]

/--
The coefficient operator `t ↦ D(geodesicFlowField Γ)_{γ t}` is continuous
when the geodesic vector field is `C¹` and the base curve is continuous.
-/
theorem continuous_linearizedGeodesicFlowOperator_comp
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ)) (hγ : Continuous γ) :
    Continuous (fun t : ℝ ↦ linearizedGeodesicFlowOperator Γ (γ t)) := by
  simpa [linearizedGeodesicFlowOperator] using
    (hF.continuous_fderiv (by norm_num)).comp hγ

section LinearODE

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/--
Local Picard-Lindelöf data for a continuous time-dependent linear ODE
`x' = A(t) x`.

The proof chooses a compact time window, bounds the operator norm there, and
then shrinks the interval so the PL endpoint ball is invariant.
-/
theorem exists_isPicardLindelof_continuous_linearODE
    (A : ℝ → X →L[ℝ] X) (hA : Continuous A) (x₀ : X) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ a r L K : ℝ≥0, 0 < r ∧
      IsPicardLindelof (fun t x ↦ A t x)
        (tmin := -ε) (tmax := ε)
        ⟨(0 : ℝ), by constructor <;> linarith⟩ x₀ a r L K := by
  rcases (isCompact_Icc.exists_bound_of_continuousOn
      (hA.continuousOn.mono fun _ ht ↦ ht)) with ⟨C, hC⟩
  let K : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  let a : ℝ≥0 := 1
  let r : ℝ≥0 := (1 / 2 : ℝ≥0)
  let B : ℝ≥0 := ⟨‖x₀‖ + 1, add_nonneg (norm_nonneg _) zero_le_one⟩
  let L : ℝ≥0 := K * B
  let ε : ℝ := 1 / (4 * ((L : ℝ) + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, a, r, L, K, ?_, ?_⟩
  · dsimp [r]
    norm_num
  · refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      have hε_le_one : ε ≤ 1 := by
        dsimp [ε]
        have hden_nonneg : 0 ≤ 4 * ((L : ℝ) + 1) := by positivity
        have hden : 1 ≤ 4 * ((L : ℝ) + 1) := by
          nlinarith [NNReal.coe_nonneg L]
        exact div_le_one_of_le₀ hden hden_nonneg
      have ht₁ : t ∈ Icc (-1 : ℝ) 1 := by
        constructor
        · linarith [ht.1, hε_le_one]
        · linarith [ht.2, hε_le_one]
      have hnorm : ‖A t‖ ≤ (K : ℝ) := by
        exact (hC t ht₁).trans (le_max_left C 0)
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le hnorm).lipschitzOnWith
    · intro x hx
      exact (hA.clm_apply continuous_const).continuousOn
    · intro t ht x hx
      have hε_le_one : ε ≤ 1 := by
        dsimp [ε]
        have hden_nonneg : 0 ≤ 4 * ((L : ℝ) + 1) := by positivity
        have hden : 1 ≤ 4 * ((L : ℝ) + 1) := by
          nlinarith [NNReal.coe_nonneg L]
        exact div_le_one_of_le₀ hden hden_nonneg
      have ht₁ : t ∈ Icc (-1 : ℝ) 1 := by
        constructor
        · linarith [ht.1, hε_le_one]
        · linarith [ht.2, hε_le_one]
      have hnormA : ‖A t‖ ≤ (K : ℝ) :=
        (hC t ht₁).trans (le_max_left C 0)
      have hxnorm : ‖x‖ ≤ (B : ℝ) := by
        have hdist : ‖x - x₀‖ ≤ (1 : ℝ) := by
          simpa [a, dist_eq_norm] using hx
        calc
          ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_le_norm_sub_add x x₀
          _ ≤ 1 + ‖x₀‖ := by linarith
          _ = ‖x₀‖ + 1 := by ring
      calc
        ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A t) x
        _ ≤ (K : ℝ) * (B : ℝ) := by
          gcongr
        _ = (L : ℝ) := by simp [L]
    · dsimp [ε, a, r]
      rw [sub_zero, zero_sub, neg_neg, max_eq_left (le_of_eq rfl)]
      have hLnonneg : 0 ≤ (L : ℝ) := by positivity
      calc
        (L : ℝ) * (1 / (4 * ((L : ℝ) + 1)))
            = (L : ℝ) / (4 * ((L : ℝ) + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
          nlinarith
        _ ≤ (1 : ℝ) - 1 / 2 := by norm_num

/-- Local existence for a continuous time-dependent linear ODE. -/
theorem exists_solution_continuous_linearODE
    (A : ℝ → X →L[ℝ] X) (hA : Continuous A) (x₀ : X) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ x : ℝ → X,
      x 0 = x₀ ∧
        ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt x (A t (x t)) (Icc (-ε) ε) t := by
  rcases exists_isPicardLindelof_continuous_linearODE A hA x₀ with
    ⟨ε, hε, a, r, L, K, hr, hpl⟩
  rcases hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := x₀) (Metric.mem_closedBall_self hr.le) with
    ⟨x, hx0, hxder⟩
  exact ⟨ε, hε, x, hx0, hxder⟩

omit [CompleteSpace X] in
/-- Uniqueness on the PL interval for a linear ODE, with the usual closed-ball hypothesis. -/
theorem linearODE_solution_uniqueOn_Icc
    {A : ℝ → X →L[ℝ] X} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : X} {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof (fun t x ↦ A t x) t₀ x₀ a r L K)
    {x y : ℝ → X}
    (hx : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt x (A t (x t)) (Icc tmin tmax) t)
    (hxmem : ∀ t ∈ Icc tmin tmax, x t ∈ closedBall x₀ a)
    (hy : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt y (A t (y t)) (Icc tmin tmax) t)
    (hymem : ∀ t ∈ Icc tmin tmax, y t ∈ closedBall x₀ a)
    (h₀ : x t₀ = y t₀) :
    EqOn x y (Icc tmin tmax) :=
  hpl.eqOn_Icc_of_mem_closedBall hx hxmem hy hymem h₀

end LinearODE

/-- Local existence for the linearized geodesic equation along a continuous base curve. -/
theorem exists_linearizedGeodesicFlow_solution
    [CompleteSpace (E × E)]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ)) (hγ : Continuous γ)
    (ψ₀ : E × E) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ Ψ : ℝ → E × E,
      Ψ 0 = ψ₀ ∧
        ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt Ψ
            (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t))
            (Icc (-ε) ε) t := by
  exact exists_solution_continuous_linearODE
    (A := fun t ↦ linearizedGeodesicFlowOperator Γ (γ t))
    (continuous_linearizedGeodesicFlowOperator_comp hF hγ) ψ₀

/-- Local existence for the chart Christoffel geodesic variational equation. -/
theorem exists_chartChristoffel_linearizedGeodesicFlow_solution
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    [CompleteSpace (ClosedSmoothModel n × ClosedSmoothModel n)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {γ : ℝ → ClosedSmoothModel n × ClosedSmoothModel n}
    (hγ : Continuous γ) (ψ₀ : ClosedSmoothModel n × ClosedSmoothModel n) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ Ψ : ℝ → ClosedSmoothModel n × ClosedSmoothModel n,
      Ψ 0 = ψ₀ ∧
        ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt Ψ
            (linearizedGeodesicFlowFieldAlong
              (GeodesicTransport.chartChristoffelField g x₀) γ t (Ψ t))
            (Icc (-ε) ε) t := by
  exact exists_linearizedGeodesicFlow_solution
    (Γ := GeodesicTransport.chartChristoffelField g x₀) (γ := γ)
    (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff
      (g := g) (x₀ := x₀))
    hγ ψ₀

/--
The pointwise Taylor remainder for the geodesic flow field.  This is the
currently verified comparison estimate: it is local at one base state.
-/
theorem geodesicFlowField_taylor_remainder_isLittleO
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {base : E × E}
    (hF : DifferentiableAt ℝ (geodesicFlowField Γ) base) :
    (fun q : E × E ↦
      geodesicFlowField Γ q - geodesicFlowField Γ base -
        linearizedGeodesicFlowOperator Γ base (q - base))
      =o[𝓝 base] fun q : E × E ↦ q - base := by
  simpa [linearizedGeodesicFlowOperator] using hF.hasFDerivAt.isLittleO

/-- The same Taylor remainder, specialized to a globally `C¹` geodesic flow field. -/
theorem geodesicFlowField_taylor_remainder_isLittleO_of_contDiff
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {base : E × E}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ)) :
    (fun q : E × E ↦
      geodesicFlowField Γ q - geodesicFlowField Γ base -
        linearizedGeodesicFlowOperator Γ base (q - base))
      =o[𝓝 base] fun q : E × E ↦ q - base :=
  geodesicFlowField_taylor_remainder_isLittleO
    (hF.differentiable (by norm_num) base)

/-- Taylor remainder for the chart Christoffel geodesic flow field. -/
theorem chartChristoffel_geodesicFlowField_taylor_remainder_isLittleO
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (base : ClosedSmoothModel n × ClosedSmoothModel n) :
    (fun q : ClosedSmoothModel n × ClosedSmoothModel n ↦
      geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) q -
        geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) base -
          linearizedGeodesicFlowOperator
            (GeodesicTransport.chartChristoffelField g x₀) base (q - base))
      =o[𝓝 base] fun q : ClosedSmoothModel n × ClosedSmoothModel n ↦ q - base :=
  geodesicFlowField_taylor_remainder_isLittleO_of_contDiff
    (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff
      (g := g) (x₀ := x₀))

end Poincare
