import Poincare.Global.HeatSemigroupBUCOperator
import Poincare.Global.HeatDuhamelPicard

/-!
# Intrinsic heat-propagated Volterra theory on `BUC`

The spatial Banach space in this file is the complete closed subspace of
bounded uniformly continuous functions.  Thus a nonlinearity `N : BUC → BUC`
needs no separate output-regularity hypothesis.  The extended heat semigroup
is strongly continuous on every value by construction.  The Picard map below
has constant linear term `u₀`; it is therefore a Volterra equation, not the
standard semilinear heat mild formula with linear orbit `H_t u₀`.
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

/-- The extended heat operator is norm-nonexpanding on intrinsic `BUC`. -/
theorem norm_vectorHeatSemigroupBUCExtended_le_one (r : ℝ) :
    ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) r‖ ≤ 1 := by
  by_cases hr : 0 < r
  · simp only [vectorHeatSemigroupBUCExtended, dif_pos hr]
    exact norm_vectorHeatSemigroupBUCLM_le_one (E := E) (F := F) hr
  · simp only [vectorHeatSemigroupBUCExtended, dif_neg hr]
    exact ContinuousLinearMap.norm_id_le

/-- Joint continuity of the extended heat action on a varying `BUC` datum. -/
theorem continuous_vectorHeatSemigroupBUCExtended_apply_comp
    {X : Type*} [TopologicalSpace X] {r : X → ℝ}
    {v : X → BoundedUniformContinuousFunction (E := E) (F := F)}
    (hr : Continuous r) (hv : Continuous v) :
    Continuous (fun x ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (r x) (v x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let d : X → BoundedUniformContinuousFunction (E := E) (F := F) :=
    fun y ↦ v y - v x
  have hvx : Tendsto v (nhds x) (nhds (v x)) := hv.continuousAt
  have hd : Tendsto d (nhds x) (nhds 0) := by
    simpa [d] using hvx.sub_const (v x)
  have hd_norm : Tendsto (fun y ↦ ‖d y‖) (nhds x) (nhds 0) := by
    simpa using hd.norm
  have hsmall_norm : Tendsto (fun y ↦
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (d y)‖)
      (nhds x) (nhds 0) := by
    apply squeeze_zero
    · exact fun y ↦ norm_nonneg _
    · intro y
      calc
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (d y)‖
            ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y)‖ * ‖d y‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖d y‖ := mul_le_mul_of_nonneg_right
          (norm_vectorHeatSemigroupBUCExtended_le_one (E := E) (F := F) (r y))
          (norm_nonneg _)
        _ = ‖d y‖ := one_mul _
    · exact hd_norm
  have hsmall : Tendsto (fun y ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (d y))
      (nhds x) (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hsmall_norm
  have hfixed : Tendsto (fun y ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (v x))
      (nhds x) (nhds
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (r x) (v x))) := by
    simpa only [Function.comp_apply] using
      (continuous_vectorHeatSemigroupBUCExtended_apply
        (E := E) (F := F) (v x)).continuousAt.comp hr.continuousAt
  have hsum := hsmall.add hfixed
  have heq : (fun y ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (v y)) =
      (fun y ↦
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (d y) +
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y) (v x)) := by
    funext y
    rw [← (vectorHeatSemigroupBUCExtended (E := E) (F := F) (r y)).map_add]
    simp [d]
  rw [heq]
  rw [ContinuousAt]
  simpa [d] using hsum

/-- Joint continuity of the intrinsic terminal/integration-time integrand. -/
theorem continuous_heatDuhamelBUCIntrinsic_integrand
    (T : ℝ≥0)
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N)
    (u : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F))) :
    Continuous (fun p : ℝ × ℝ ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (p.1 - p.2)
        (N (u (Set.projIcc 0 (T : ℝ) T.property p.2)))) := by
  apply continuous_vectorHeatSemigroupBUCExtended_apply_comp (E := E) (F := F)
  · exact continuous_fst.sub continuous_snd
  · exact hN.comp (u.continuous.comp
      ((continuous_projIcc (h := T.property)).comp continuous_snd))

/-- The intrinsic heat-propagated Volterra Picard map on `BUC`. -/
def heatDuhamelBUCIntrinsicPicard
    (T : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N)
    (u : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F))) :
    DuhamelPath T (BoundedUniformContinuousFunction (E := E) (F := F)) where
  toFun t := u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
    vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  continuous_toFun := by
    let f : ℝ → ℝ → BoundedUniformContinuousFunction (E := E) (F := F) :=
      fun t s ↦ vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
    have hf : Continuous f.uncurry := by
      simpa [f, Function.uncurry] using
        continuous_heatDuhamelBUCIntrinsic_integrand
          (E := E) (F := F) T N hN u
    have hprimitive : Continuous (fun t : ℝ ↦
        ∫ s : ℝ in (0 : ℝ)..t, f t s) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        hf continuous_id
    exact (continuous_const.add hprimitive).comp continuous_subtype_val

@[simp]
theorem heatDuhamelBUCIntrinsicPicard_apply
    (T : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N)
    (u : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F)))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatDuhamelBUCIntrinsicPicard T u₀ N hN u t =
      u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))) :=
  rfl

/-- Exact projected difference identity in intrinsic `BUC`. -/
theorem heatDuhamelBUCIntrinsicPicard_sub_eq_projectedDuhamelDifference
    (T : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N)
    (u v : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F)))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatDuhamelBUCIntrinsicPicard T u₀ N hN u t -
        heatDuhamelBUCIntrinsicPicard T u₀ N hN v t =
      projectedDuhamelDifference T
        (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N u v t := by
  let gu : ℝ → BoundedUniformContinuousFunction (E := E) (F := F) := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  let gv : ℝ → BoundedUniformContinuousFunction (E := E) (F := F) := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
      (N (v (Set.projIcc 0 (T : ℝ) T.property s)))
  have hgu : Continuous gu := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hN.comp (u.continuous.comp (continuous_projIcc (h := T.property)))
  have hgv : Continuous gv := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hN.comp (v.continuous.comp (continuous_projIcc (h := T.property)))
  rw [heatDuhamelBUCIntrinsicPicard_apply, heatDuhamelBUCIntrinsicPicard_apply,
    add_sub_add_left_eq_sub, projectedDuhamelDifference]
  rw [← intervalIntegral.integral_sub (hgu.intervalIntegrable _ _)
    (hgv.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _hs
  exact (vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)).map_sub _ _ |>.symm

/-- Intrinsic `BUC` contraction theorem. -/
theorem heatDuhamelBUCIntrinsicPicard_contractingWith
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ContractingWith (T * L)
      (heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous) := by
  have h := contractingWith_of_projectedDuhamelDifference
    (X := BoundedUniformContinuousFunction (E := E) (F := F))
    T 1 L (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N
    (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
      (E := E) (F := F) r)
    hN (heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous)
    (heatDuhamelBUCIntrinsicPicard_sub_eq_projectedDuhamelDifference
      T u₀ N hN.continuous)
    (by simpa using hsmall)
  simpa using h

/-- Unique intrinsic `BUC` fixed point. -/
theorem exists_unique_heatDuhamelBUCIntrinsicPicard_fixedPoint
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T
        (BoundedUniformContinuousFunction (E := E) (F := F)),
      heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous u = u := by
  have hc := heatDuhamelBUCIntrinsicPicard_contractingWith
    (E := E) (F := F) T L u₀ N hN hsmall
  let u := hc.fixedPoint (heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous)
  refine ⟨u, hc.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact hc.fixedPoint_unique' hv hc.fixedPoint_isFixedPt

/-- Unique intrinsic `BUC` Volterra solution, including its initial value and
exact identity.  The historical name contains `mildSolution`; the displayed
identity makes the constant-linear-term convention explicit. -/
theorem exists_unique_heatDuhamelBUCIntrinsic_mildSolution
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T
        (BoundedUniformContinuousFunction (E := E) (F := F)),
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ ∧
      ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
        u t = u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
  rcases exists_unique_heatDuhamelBUCIntrinsicPicard_fixedPoint
    (E := E) (F := F) T L u₀ N hN hsmall with ⟨u, hu, huniq⟩
  have hmild : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      u t = u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
    intro t
    have ht := congrArg
      (fun w : DuhamelPath T
        (BoundedUniformContinuousFunction (E := E) (F := F)) ↦ w t) hu
    exact ht.symm
  refine ⟨u, ⟨?_, hmild⟩, ?_⟩
  · simpa using hmild (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))
  · intro v hv
    apply huniq v
    apply ContinuousMap.ext
    intro t
    exact (hv.2 t).symm

/-- Constant intrinsic `BUC` path at the initial datum. -/
def constantDuhamelBUCIntrinsicPath
    (T : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F)) :
    DuhamelPath T (BoundedUniformContinuousFunction (E := E) (F := F)) :=
  ContinuousMap.const _ u₀

@[simp]
theorem constantDuhamelBUCIntrinsicPath_apply
    (T : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    constantDuhamelBUCIntrinsicPath T u₀ t = u₀ :=
  rfl

/-- A uniform intrinsic nonlinearity bound gives the explicit `T B` radius
estimate. -/
theorem dist_heatDuhamelBUCIntrinsicPicard_constant_le
    (T B : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    (u : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F))) :
    dist (heatDuhamelBUCIntrinsicPicard T u₀ N hN u)
      (constantDuhamelBUCIntrinsicPath T u₀) ≤ (T : ℝ) * (B : ℝ) := by
  apply (ContinuousMap.dist_le (mul_nonneg T.property B.property)).mpr
  intro t
  change dist (u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s))))) u₀ ≤ _
  rw [Subtype.dist_eq, dist_eq_norm]
  simp only [Submodule.coe_add, add_sub_cancel_left]
  change ‖(∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s))))‖ ≤ _
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤ (B : ℝ) := by
    intro s _hs
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
          ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)‖ *
              ‖N (u (Set.projIcc 0 (T : ℝ) T.property s))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (B : ℝ) :=
        mul_le_mul
          (norm_vectorHeatSemigroupBUCExtended_le_one
            (E := E) (F := F) ((t : ℝ) - s))
          (hNbound _) (norm_nonneg _) zero_le_one
      _ = (B : ℝ) := one_mul _
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ (B : ℝ) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (B : ℝ) * (t : ℝ) := by
      rw [sub_zero, abs_of_nonneg t.property.1]
    _ ≤ (B : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 B.property
    _ = (T : ℝ) * (B : ℝ) := mul_comm _ _

/-- Closed-ball preservation for the intrinsic `BUC` Picard map. -/
theorem heatDuhamelBUCIntrinsicPicard_mapsTo_closedBall
    (T B : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : Continuous N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hTR : (T : ℝ) * (B : ℝ) ≤ R) :
    MapsTo (heatDuhamelBUCIntrinsicPicard T u₀ N hN)
      (Metric.closedBall (constantDuhamelBUCIntrinsicPath T u₀) R)
      (Metric.closedBall (constantDuhamelBUCIntrinsicPath T u₀) R) := by
  intro u _hu
  exact (dist_heatDuhamelBUCIntrinsicPicard_constant_le
    (E := E) (F := F) T B u₀ N hN hNbound u).trans hTR

/-- Local invariant-ball fixed point intrinsically on the complete `BUC`
space. -/
theorem exists_heatDuhamelBUCIntrinsicPicard_fixedPoint_mem_closedBall
    (T B L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hR : 0 ≤ R) (hTR : (T : ℝ) * (B : ℝ) ≤ R)
    (hsmall : T * L < 1) :
    ∃ u ∈ Metric.closedBall (constantDuhamelBUCIntrinsicPath T u₀) R,
      heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous u = u ∧
      ∀ v ∈ Metric.closedBall (constantDuhamelBUCIntrinsicPath T u₀) R,
        heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous v = v → v = u := by
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := BoundedUniformContinuousFunction (E := E) (F := F))
    (q := T * L) (heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous)
    (constantDuhamelBUCIntrinsicPath T u₀) hR
  · exact heatDuhamelBUCIntrinsicPicard_mapsTo_closedBall
      (E := E) (F := F) T B u₀ N hN.continuous hNbound hTR
  · intro u v _hu _hv t
    rw [heatDuhamelBUCIntrinsicPicard_sub_eq_projectedDuhamelDifference
      (E := E) (F := F) T u₀ N hN.continuous u v t]
    have hbound := norm_projectedDuhamelDifference_le
      (X := BoundedUniformContinuousFunction (E := E) (F := F))
      T 1 L (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N
      (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
        (E := E) (F := F) r)
      hN u v t
    simpa using hbound
  · simpa using hsmall

/-- Quantitative dependence of intrinsic `BUC` fixed points on their initial
data.  The denominator is positive precisely under the contraction condition
`T L < 1`. -/
theorem dist_heatDuhamelBUCIntrinsic_fixedPoints_le
    (T L : ℝ≥0)
    (u₀ v₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (u v : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F)))
    (hu : heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous u = u)
    (hv : heatDuhamelBUCIntrinsicPicard T v₀ N hN.continuous v = v) :
    dist u v ≤
      (1 - (((T * L : ℝ≥0) : ℝ)))⁻¹ * dist u₀ v₀ := by
  let Φu := heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous
  let Φv := heatDuhamelBUCIntrinsicPicard T v₀ N hN.continuous
  have hcontract := heatDuhamelBUCIntrinsicPicard_contractingWith
    (E := E) (F := F) T L u₀ N hN hsmall
  have hlip : LipschitzWith (T * L) Φu := by
    simpa [Φu] using hcontract.2
  have hshift : dist (Φu v) (Φv v) ≤ dist u₀ v₀ := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    change dist (u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (v (Set.projIcc 0 (T : ℝ) T.property s)))))
      (v₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (v (Set.projIcc 0 (T : ℝ) T.property s))))) ≤ dist u₀ v₀
    exact (dist_add_right u₀ v₀ _).le
  have htotal : dist u v ≤
      (((T * L : ℝ≥0) : ℝ)) * dist u v + dist u₀ v₀ := by
    calc
      dist u v = dist (Φu u) (Φv v) := by
        simp only [Φu, Φv]
        rw [hu, hv]
      _ ≤ dist (Φu u) (Φu v) + dist (Φu v) (Φv v) :=
        dist_triangle _ _ _
      _ ≤ (((T * L : ℝ≥0) : ℝ)) * dist u v + dist u₀ v₀ :=
        add_le_add (hlip.dist_le_mul u v) hshift
  have hq : (((T * L : ℝ≥0) : ℝ)) < 1 := by
    exact_mod_cast hsmall
  have hden : 0 < 1 - (((T * L : ℝ≥0) : ℝ)) := sub_pos.mpr hq
  rw [le_inv_mul_iff₀ hden]
  nlinarith

/-- The same continuous-dependence estimate stated directly for two paths
satisfying their exact heat-propagated Volterra identities. -/
theorem dist_heatDuhamelBUCIntrinsic_mildSolutions_le
    (T L : ℝ≥0)
    (u₀ v₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (u v : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F)))
    (hu : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      u t = u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))))
    (hv : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      v t = v₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (v (Set.projIcc 0 (T : ℝ) T.property s)))) :
    dist u v ≤
      (1 - (((T * L : ℝ≥0) : ℝ)))⁻¹ * dist u₀ v₀ := by
  apply dist_heatDuhamelBUCIntrinsic_fixedPoints_le
    (E := E) (F := F) T L u₀ v₀ N hN hsmall u v
  · apply ContinuousMap.ext
    intro t
    exact (hu t).symm
  · apply ContinuousMap.ext
    intro t
    exact (hv t).symm

/-- The canonical intrinsic `BUC` Volterra solution selected from uniqueness. -/
noncomputable def heatDuhamelBUCIntrinsicSolution
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    DuhamelPath T (BoundedUniformContinuousFunction (E := E) (F := F)) :=
  Classical.choose
    (exists_unique_heatDuhamelBUCIntrinsicPicard_fixedPoint
      (E := E) (F := F) T L u₀ N hN hsmall)

/-- The selected solution is the Picard fixed point. -/
theorem heatDuhamelBUCIntrinsicSolution_isFixedPt
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    heatDuhamelBUCIntrinsicPicard T u₀ N hN.continuous
        (heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall) =
      heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall :=
  (Classical.choose_spec
    (exists_unique_heatDuhamelBUCIntrinsicPicard_fixedPoint
      (E := E) (F := F) T L u₀ N hN hsmall)).1

/-- Exact heat-propagated Volterra identity for the selected intrinsic solution. -/
theorem heatDuhamelBUCIntrinsicSolution_mild
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall t =
      u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall
            (Set.projIcc 0 (T : ℝ) T.property s))) := by
  have h := congrArg
    (fun w : DuhamelPath T
      (BoundedUniformContinuousFunction (E := E) (F := F)) ↦ w t)
    (heatDuhamelBUCIntrinsicSolution_isFixedPt
      (E := E) (F := F) T L u₀ N hN hsmall)
  exact h.symm

/-- Initial value of the selected intrinsic solution. -/
@[simp]
theorem heatDuhamelBUCIntrinsicSolution_zero
    (T L : ℝ≥0)
    (u₀ : BoundedUniformContinuousFunction (E := E) (F := F))
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ := by
  simpa using heatDuhamelBUCIntrinsicSolution_mild
    (E := E) (F := F) T L u₀ N hN hsmall
      (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))

/-- The exact nonnegative stability constant. -/
noncomputable def heatDuhamelBUCIntrinsicStabilityConstant
    (T L : ℝ≥0) (hsmall : T * L < 1) : ℝ≥0 := by
  have hq : (((T * L : ℝ≥0) : ℝ)) < 1 := by exact_mod_cast hsmall
  exact ⟨(1 - (((T * L : ℝ≥0) : ℝ)))⁻¹,
    (inv_pos.mpr (sub_pos.mpr hq)).le⟩

/-- The canonical solution operator is Lipschitz in the initial datum with
constant `(1 - T L)⁻¹`. -/
theorem lipschitzWith_heatDuhamelBUCIntrinsicSolution
    (T L : ℝ≥0)
    (N : BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F))
    (hN : LipschitzWith L N) (hsmall : T * L < 1) :
    LipschitzWith (heatDuhamelBUCIntrinsicStabilityConstant T L hsmall)
      (fun u₀ : BoundedUniformContinuousFunction (E := E) (F := F) ↦
        heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall) := by
  apply LipschitzWith.of_dist_le_mul
  intro u₀ v₀
  have h := dist_heatDuhamelBUCIntrinsic_fixedPoints_le
    (E := E) (F := F) T L u₀ v₀ N hN hsmall
    (heatDuhamelBUCIntrinsicSolution T L u₀ N hN hsmall)
    (heatDuhamelBUCIntrinsicSolution T L v₀ N hN hsmall)
    (heatDuhamelBUCIntrinsicSolution_isFixedPt
      (E := E) (F := F) T L u₀ N hN hsmall)
    (heatDuhamelBUCIntrinsicSolution_isFixedPt
      (E := E) (F := F) T L v₀ N hN hsmall)
  simpa [heatDuhamelBUCIntrinsicStabilityConstant] using h

end Poincare
