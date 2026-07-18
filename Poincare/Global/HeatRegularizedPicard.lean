import Poincare.Global.HeatSemigroupOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Concrete heat-regularized Picard map

This module instantiates the abstract Duhamel contraction theorem on the
spatial Banach space `C_b(E,F)`.  At a fixed positive smoothing time `ε`, the
heat operator has norm at most one.  Therefore

`u ↦ u₀ + ∫₀ᵗ H_ε (N(u(s))) ds`

is a contraction on continuous `C_b(E,F)`-valued paths whenever `T L < 1`.
This is a fully concrete fixed-smoothing Volterra equation.  It is not the
semilinear heat mild problem, whose propagator is `H_{t-s}` and whose
homogeneous term is `H_t u₀`; that corrected theory is developed separately.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

/-- The explicit Picard map obtained by applying one fixed positive-time heat
smoothing operator to the nonlinearity before time integration. -/
def heatRegularizedPicard
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N) (u : DuhamelPath T (E →ᵇ F)) :
    DuhamelPath T (E →ᵇ F) where
  toFun t := u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
    vectorHeatSemigroupCLM (E := E) (F := F) hε
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  continuous_toFun := by
    let H := vectorHeatSemigroupCLM (E := E) (F := F) hε
    let g : ℝ → (E →ᵇ F) := fun s ↦
      H (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
    have hg : Continuous g := by
      exact H.continuous.comp
        (hN.comp (u.continuous.comp (continuous_projIcc (h := T.property))))
    have hprimitive : Continuous (fun r : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..r, g s) := by
      rw [continuous_iff_continuousAt]
      intro r
      exact (hg.integral_hasStrictDerivAt 0 r).hasDerivAt.continuousAt
    exact (continuous_const.add hprimitive).comp continuous_subtype_val

@[simp]
theorem heatRegularizedPicard_apply
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N) (u : DuhamelPath T (E →ᵇ F))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatRegularizedPicard hε T u₀ N hN u t =
      u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupCLM (E := E) (F := F) hε
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))) :=
  rfl

/-- Differences of concrete heat-regularized Picard iterates have exactly the
projected Duhamel form used by `DuhamelContraction`. -/
theorem heatRegularizedPicard_sub_eq_projectedDuhamelDifference
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N) (u v : DuhamelPath T (E →ᵇ F))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatRegularizedPicard hε T u₀ N hN u t -
        heatRegularizedPicard hε T u₀ N hN v t =
      projectedDuhamelDifference T
        (fun _ ↦ vectorHeatSemigroupCLM (E := E) (F := F) hε) N u v t := by
  let H := vectorHeatSemigroupCLM (E := E) (F := F) hε
  let gu : ℝ → (E →ᵇ F) := fun s ↦
    H (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  let gv : ℝ → (E →ᵇ F) := fun s ↦
    H (N (v (Set.projIcc 0 (T : ℝ) T.property s)))
  have hgu : Continuous gu := H.continuous.comp
    (hN.comp (u.continuous.comp (continuous_projIcc (h := T.property))))
  have hgv : Continuous gv := H.continuous.comp
    (hN.comp (v.continuous.comp (continuous_projIcc (h := T.property))))
  rw [heatRegularizedPicard_apply, heatRegularizedPicard_apply,
    add_sub_add_left_eq_sub, projectedDuhamelDifference]
  rw [← intervalIntegral.integral_sub (hgu.intervalIntegrable _ _)
    (hgv.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _hs
  exact (H.map_sub _ _).symm

/-- The concrete heat-regularized Picard map is a contraction with constant
`T L`. -/
theorem heatRegularizedPicard_contractingWith
    {ε : ℝ} (hε : 0 < ε) (T L : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ContractingWith (T * L)
      (heatRegularizedPicard hε T u₀ N hN.continuous) := by
  have h := contractingWith_of_projectedDuhamelDifference
    (X := E →ᵇ F) T 1 L
    (fun _ ↦ vectorHeatSemigroupCLM (E := E) (F := F) hε) N
    (fun r _hr ↦ norm_vectorHeatSemigroupCLM_le_one (E := E) (F := F) hε)
    hN (heatRegularizedPicard hε T u₀ N hN.continuous)
    (heatRegularizedPicard_sub_eq_projectedDuhamelDifference hε T u₀ N
      hN.continuous)
    (by simpa using hsmall)
  simpa using h

/-- A concrete unique fixed point for the fixed-smoothing Volterra problem. -/
theorem exists_unique_heatRegularizedPicard_fixedPoint
    {ε : ℝ} (hε : 0 < ε) (T L : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T (E →ᵇ F),
      heatRegularizedPicard hε T u₀ N hN.continuous u = u := by
  have hc := heatRegularizedPicard_contractingWith
    (E := E) (F := F) hε T L u₀ N hN hsmall
  let u := hc.fixedPoint (heatRegularizedPicard hε T u₀ N hN.continuous)
  refine ⟨u, hc.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact hc.fixedPoint_unique' hv hc.fixedPoint_isFixedPt

/-- Constant path at the prescribed initial bounded continuous field. -/
def constantDuhamelPath (T : ℝ≥0) (u₀ : E →ᵇ F) :
    DuhamelPath T (E →ᵇ F) :=
  ContinuousMap.const _ u₀

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
@[simp]
theorem constantDuhamelPath_apply (T : ℝ≥0) (u₀ : E →ᵇ F)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    constantDuhamelPath T u₀ t = u₀ :=
  rfl

/-- A uniform bound on the nonlinearity makes the heat-regularized Picard map
stay within distance `T B` of its initial constant path. -/
theorem dist_heatRegularizedPicard_constantDuhamelPath_le
    {ε : ℝ} (hε : 0 < ε) (T B : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    (u : DuhamelPath T (E →ᵇ F)) :
    dist (heatRegularizedPicard hε T u₀ N hN u)
      (constantDuhamelPath T u₀) ≤ (T : ℝ) * (B : ℝ) := by
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg T.property B.property)).mpr
  intro t
  change ‖u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupCLM (E := E) (F := F) hε
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))) - u₀‖ ≤ _
  rw [add_sub_cancel_left]
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupCLM (E := E) (F := F) hε
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤ (B : ℝ) := by
    intro s _hs
    calc
      ‖vectorHeatSemigroupCLM (E := E) (F := F) hε
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
          ≤ ‖vectorHeatSemigroupCLM (E := E) (F := F) hε‖ *
              ‖N (u (Set.projIcc 0 (T : ℝ) T.property s))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (B : ℝ) :=
        mul_le_mul (norm_vectorHeatSemigroupCLM_le_one (E := E) (F := F) hε)
          (hNbound _) (norm_nonneg _) zero_le_one
      _ = (B : ℝ) := one_mul _
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupCLM (E := E) (F := F) hε
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ (B : ℝ) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (B : ℝ) * (t : ℝ) := by
      rw [sub_zero, abs_of_nonneg t.property.1]
    _ ≤ (B : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 B.property
    _ = (T : ℝ) * (B : ℝ) := mul_comm _ _

/-- Explicit ball preservation for the concrete heat-regularized Picard map. -/
theorem heatRegularizedPicard_mapsTo_closedBall
    {ε : ℝ} (hε : 0 < ε) (T B : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hTR : (T : ℝ) * (B : ℝ) ≤ R) :
    MapsTo (heatRegularizedPicard hε T u₀ N hN)
      (Metric.closedBall (constantDuhamelPath T u₀) R)
      (Metric.closedBall (constantDuhamelPath T u₀) R) := by
  intro u _hu
  exact (dist_heatRegularizedPicard_constantDuhamelPath_le
    (E := E) (F := F) hε T B u₀ N hN hNbound u).trans hTR

/-- Local closed-ball fixed point for the concrete heat-regularized Picard
problem, with both ball preservation and contraction discharged by explicit
`T B` and `T L` estimates. -/
theorem exists_heatRegularizedPicard_fixedPoint_mem_closedBall
    {ε : ℝ} (hε : 0 < ε) (T B L : ℝ≥0)
    (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hR : 0 ≤ R) (hTR : (T : ℝ) * (B : ℝ) ≤ R)
    (hsmall : T * L < 1) :
    ∃ u ∈ Metric.closedBall (constantDuhamelPath T u₀) R,
      heatRegularizedPicard hε T u₀ N hN.continuous u = u ∧
      ∀ v ∈ Metric.closedBall (constantDuhamelPath T u₀) R,
        heatRegularizedPicard hε T u₀ N hN.continuous v = v → v = u := by
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := E →ᵇ F) (q := T * L)
    (heatRegularizedPicard hε T u₀ N hN.continuous)
    (constantDuhamelPath T u₀) hR
  · exact heatRegularizedPicard_mapsTo_closedBall
      (E := E) (F := F) hε T B u₀ N hN.continuous hNbound hTR
  · intro u v _hu _hv t
    rw [heatRegularizedPicard_sub_eq_projectedDuhamelDifference
      (E := E) (F := F) hε T u₀ N hN.continuous u v t]
    have hbound := norm_projectedDuhamelDifference_le
      (X := E →ᵇ F) T 1 L
      (fun _ ↦ vectorHeatSemigroupCLM (E := E) (F := F) hε) N
      (fun r _hr ↦ norm_vectorHeatSemigroupCLM_le_one (E := E) (F := F) hε)
      hN u v t
    simpa using hbound
  · simpa using hsmall

/-- Positive-time operator-norm continuity needed away from the Duhamel
diagonal. -/
def HeatSemigroupStrongContinuityOnPositiveTimes : Prop :=
  Continuous (fun p : {t : ℝ // 0 < t} ↦
    vectorHeatSemigroupCLM (E := E) (F := F) p.property)

/-- Exact diagonal frontier for the true heat Duhamel operator.  On arbitrary
`C_b(E,F)` the heat semigroup need not converge uniformly to the identity at
zero.  It is enough to have this convergence on the image of the chosen
nonlinearity; bounded uniformly continuous or Holder path spaces are standard
ways to discharge it. -/
def HeatSemigroupStrongContinuityAtZeroOn
    (N : (E →ᵇ F) → (E →ᵇ F)) : Prop :=
  ∀ (z : E →ᵇ F) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ (t : ℝ) (ht : 0 < t), t < δ →
      ‖vectorHeatSemigroupCLM (E := E) (F := F) ht (N z) - N z‖ < η

end Poincare
