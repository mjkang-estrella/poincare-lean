import Poincare.Global.BoundedUniformContinuousHeat
import Poincare.Global.HeatSemigroupPositiveContinuity

/-!
# A variable-time heat-propagated Volterra map

This module extends the positive-time heat operator by the identity at zero,
proves continuity of its action along paths whose values are Lipschitz in the
spatial variable, and uses it to define the Picard map

`u₀ + ∫₀ᵗ H_(t-s) (N (u s)) ds`.

This is a useful heat-propagated Volterra equation, but it is not the standard
semilinear heat mild formula: the latter has `H_t u₀` as its linear term.
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

/-- The heat propagator at positive time, extended by the identity at zero
(and, harmlessly, at negative times). -/
def vectorHeatSemigroupNonnegative (r : ℝ) :
    (E →ᵇ F) →L[ℝ] (E →ᵇ F) :=
  if hr : 0 < r then vectorHeatSemigroupCLM (E := E) (F := F) hr
  else ContinuousLinearMap.id ℝ (E →ᵇ F)

@[simp]
theorem vectorHeatSemigroupNonnegative_of_pos {r : ℝ} (hr : 0 < r) :
    vectorHeatSemigroupNonnegative (E := E) (F := F) r =
      vectorHeatSemigroupCLM (E := E) (F := F) hr := by
  simp [vectorHeatSemigroupNonnegative, hr]

@[simp]
theorem vectorHeatSemigroupNonnegative_of_nonpos {r : ℝ} (hr : ¬ 0 < r) :
    vectorHeatSemigroupNonnegative (E := E) (F := F) r =
      ContinuousLinearMap.id ℝ (E →ᵇ F) := by
  simp [vectorHeatSemigroupNonnegative, hr]

/-- Uniform contraction bound, including the zero-time identity. -/
theorem norm_vectorHeatSemigroupNonnegative_le_one (r : ℝ) :
    ‖vectorHeatSemigroupNonnegative (E := E) (F := F) r‖ ≤ 1 := by
  by_cases hr : 0 < r
  · rw [vectorHeatSemigroupNonnegative_of_pos (E := E) (F := F) hr]
    exact norm_vectorHeatSemigroupCLM_le_one (E := E) (F := F) hr
  · rw [vectorHeatSemigroupNonnegative_of_nonpos (E := E) (F := F) hr]
    exact ContinuousLinearMap.norm_id_le

/-- The zero-time Lipschitz convergence, extended from the positive half-line
to a full neighborhood by making the propagator the identity on the left. -/
theorem tendsto_vectorHeatSemigroupNonnegative_apply_zero_of_lipschitz
    (f : E →ᵇ F) (K : NNReal) (hf : LipschitzWith K (f : E → F)) :
    Tendsto (fun r : ℝ ↦
      vectorHeatSemigroupNonnegative (E := E) (F := F) r f)
      (nhds 0) (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos := tendsto_norm_vectorHeatSemigroup_sub_of_lipschitz
    (E := E) (F := F) f K hf
  rw [Metric.tendsto_nhdsWithin_nhds] at hpos
  rcases hpos ε hε with ⟨δ, hδ, hclose⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hrball
  by_cases hr : 0 < r
  · have h := hclose (Set.mem_Ioi.mpr hr) (by simpa using hrball)
    simpa [vectorHeatSemigroupNonnegative, hr, Real.dist_eq] using h
  · simpa [vectorHeatSemigroupNonnegative, hr] using hε

/-- Continuity at one parameter point for a varying spatial field. -/
theorem continuousAt_vectorHeatSemigroupNonnegative_apply
    {X : Type*} [TopologicalSpace X] {r : X → ℝ} {v : X → (E →ᵇ F)} {x : X}
    (hr : ContinuousAt r x) (hv : ContinuousAt v x)
    (hvlip : ∃ K : NNReal, LipschitzWith K (v x : E → F)) :
    ContinuousAt (fun y ↦
      vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (v y)) x := by
  rcases lt_trichotomy (r x) 0 with hneg | hzero | hpos
  · have hev : ∀ᶠ y in nhds x, r y < 0 := hr (Iio_mem_nhds hneg)
    have heq : (fun y ↦
        vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (v y)) =ᶠ[nhds x]
        v := hev.mono fun y hy ↦ by
      simp [vectorHeatSemigroupNonnegative, not_lt.mpr hy.le]
    exact hv.congr_of_eventuallyEq heq
  · have hr0 : Tendsto r (nhds x) (nhds 0) := by
      change Tendsto r (nhds x) (nhds (r x)) at hr
      simpa [hzero] using hr
    rcases hvlip with ⟨K, hK⟩
    have hfixed :=
      (tendsto_vectorHeatSemigroupNonnegative_apply_zero_of_lipschitz
        (E := E) (F := F) (v x) K hK).comp hr0
    let d : X → (E →ᵇ F) := fun y ↦ v y - v x
    have hd_norm : Tendsto (fun y ↦ ‖d y‖) (nhds x) (nhds 0) := by
      simpa [d] using (hv.sub_const (v x)).norm
    have hsmall_norm : Tendsto (fun y ↦
        ‖vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (d y)‖)
        (nhds x) (nhds 0) := by
      apply squeeze_zero
      · exact fun y ↦ norm_nonneg _
      · intro y
        calc
          ‖vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (d y)‖
              ≤ ‖vectorHeatSemigroupNonnegative (E := E) (F := F) (r y)‖ * ‖d y‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖d y‖ := mul_le_mul_of_nonneg_right
            (norm_vectorHeatSemigroupNonnegative_le_one (E := E) (F := F) (r y))
            (norm_nonneg _)
          _ = ‖d y‖ := one_mul _
      · exact hd_norm
    have hsmall : Tendsto (fun y ↦
        vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (d y))
        (nhds x) (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa using hsmall_norm
    have hsum := hsmall.add hfixed
    have heq : (fun y ↦
        vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (v y)) =
        (fun y ↦
          vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (d y) +
            vectorHeatSemigroupNonnegative (E := E) (F := F) (r y) (v x)) := by
      funext y
      rw [← (vectorHeatSemigroupNonnegative (E := E) (F := F) (r y)).map_add]
      simp [d]
    rw [ContinuousAt]
    rw [heq]
    simpa [hzero, vectorHeatSemigroupNonnegative] using hsum
  · have hev : ∀ᶠ y in nhds x, 0 < r y := hr (Ioi_mem_nhds hpos)
    let rp : X → {t : ℝ // 0 < t} := fun y ↦
      if hy : 0 < r y then ⟨r y, hy⟩ else ⟨r x, hpos⟩
    have hrp : Tendsto rp (nhds x) (nhds (⟨r x, hpos⟩ : {t : ℝ // 0 < t})) := by
      rw [tendsto_subtype_rng]
      apply hr.congr'
      exact hev.mono fun y hy ↦ by simp [rp, hy]
    have hrpx : rp x = (⟨r x, hpos⟩ : {t : ℝ // 0 < t}) := by
      simp [rp, hpos]
    have hrp_at : ContinuousAt rp x := by
      rw [ContinuousAt, hrpx]
      exact hrp
    have hop :=
      (continuous_vectorHeatSemigroupCLM_positive (E := E) (F := F)).continuousAt.comp hrp_at
    have hmain : ContinuousAt (fun y ↦
        vectorHeatSemigroupCLM (E := E) (F := F) (rp y).property (v y)) x := by
      simpa only [Function.comp_apply] using hop.clm_apply hv
    apply hmain.congr_of_eventuallyEq
    exact hev.mono fun y hy ↦ by simp [rp, hy, vectorHeatSemigroupNonnegative]

/-- Pathwise version of the preceding joint continuity statement. -/
theorem continuous_vectorHeatSemigroupNonnegative_apply
    {X : Type*} [TopologicalSpace X] {r : X → ℝ} {v : X → (E →ᵇ F)}
    (hr : Continuous r) (hv : Continuous v)
    (hvlip : ∀ x, ∃ K : NNReal, LipschitzWith K (v x : E → F)) :
    Continuous (fun x ↦
      vectorHeatSemigroupNonnegative (E := E) (F := F) (r x) (v x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_vectorHeatSemigroupNonnegative_apply
    (E := E) (F := F) hr.continuousAt hv.continuousAt (hvlip x)

/-- Joint continuity of the true Duhamel integrand in terminal and integration
time. -/
theorem continuous_heatDuhamel_integrand
    (T : ℝ≥0) (N : (E →ᵇ F) → (E →ᵇ F)) (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (u : DuhamelPath T (E →ᵇ F)) :
    Continuous (fun p : ℝ × ℝ ↦
      vectorHeatSemigroupNonnegative (E := E) (F := F) (p.1 - p.2)
        (N (u (Set.projIcc 0 (T : ℝ) T.property p.2)))) := by
  apply continuous_vectorHeatSemigroupNonnegative_apply (E := E) (F := F)
  · exact continuous_fst.sub continuous_snd
  · exact hN.comp (u.continuous.comp
      ((continuous_projIcc (h := T.property)).comp continuous_snd))
  · intro p
    exact hNlip _

/-- The variable-time heat-propagated Volterra Picard map. -/
def heatDuhamelPicard
    (T : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (u : DuhamelPath T (E →ᵇ F)) : DuhamelPath T (E →ᵇ F) where
  toFun t := u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
    vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  continuous_toFun := by
    let f : ℝ → ℝ → (E →ᵇ F) := fun t s ↦
      vectorHeatSemigroupNonnegative (E := E) (F := F) (t - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
    have hf : Continuous f.uncurry := by
      simpa [f, Function.uncurry] using
        continuous_heatDuhamel_integrand (E := E) (F := F) T N hN hNlip u
    have hprimitive : Continuous (fun t : ℝ ↦
        ∫ s : ℝ in (0 : ℝ)..t, f t s) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        hf continuous_id
    exact (continuous_const.add hprimitive).comp continuous_subtype_val

@[simp]
theorem heatDuhamelPicard_apply
    (T : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (u : DuhamelPath T (E →ᵇ F)) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatDuhamelPicard T u₀ N hN hNlip u t =
      u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))) :=
  rfl

/-- Differences of these heat-propagated Volterra iterates have the projected form used by
the abstract contraction estimate. -/
theorem heatDuhamelPicard_sub_eq_projectedDuhamelDifference
    (T : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (u v : DuhamelPath T (E →ᵇ F)) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    heatDuhamelPicard T u₀ N hN hNlip u t -
        heatDuhamelPicard T u₀ N hN hNlip v t =
      projectedDuhamelDifference T
        (vectorHeatSemigroupNonnegative (E := E) (F := F)) N u v t := by
  let gu : ℝ → (E →ᵇ F) := fun s ↦
    vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  let gv : ℝ → (E →ᵇ F) := fun s ↦
    vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
      (N (v (Set.projIcc 0 (T : ℝ) T.property s)))
  have hgu : Continuous gu := by
    apply continuous_vectorHeatSemigroupNonnegative_apply (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hN.comp (u.continuous.comp (continuous_projIcc (h := T.property)))
    · intro s
      exact hNlip _
  have hgv : Continuous gv := by
    apply continuous_vectorHeatSemigroupNonnegative_apply (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hN.comp (v.continuous.comp (continuous_projIcc (h := T.property)))
    · intro s
      exact hNlip _
  rw [heatDuhamelPicard_apply, heatDuhamelPicard_apply,
    add_sub_add_left_eq_sub, projectedDuhamelDifference]
  rw [← intervalIntegral.integral_sub (hgu.intervalIntegrable _ _)
    (hgv.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _hs
  exact (vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)).map_sub _ _ |>.symm

/-- The heat-propagated Volterra Picard map is a contraction for `T L < 1`. -/
theorem heatDuhamelPicard_contractingWith
    (T L : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hsmall : T * L < 1) :
    ContractingWith (T * L)
      (heatDuhamelPicard T u₀ N hN.continuous hNlip) := by
  have h := contractingWith_of_projectedDuhamelDifference
    (X := E →ᵇ F) T 1 L
    (vectorHeatSemigroupNonnegative (E := E) (F := F)) N
    (fun r _hr ↦ norm_vectorHeatSemigroupNonnegative_le_one
      (E := E) (F := F) r)
    hN (heatDuhamelPicard T u₀ N hN.continuous hNlip)
    (heatDuhamelPicard_sub_eq_projectedDuhamelDifference
      T u₀ N hN.continuous hNlip)
    (by simpa using hsmall)
  simpa using h

/-- Existence and uniqueness of the short-time Volterra fixed point. -/
theorem exists_unique_heatDuhamelPicard_fixedPoint
    (T L : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T (E →ᵇ F),
      heatDuhamelPicard T u₀ N hN.continuous hNlip u = u := by
  have hc := heatDuhamelPicard_contractingWith
    (E := E) (F := F) T L u₀ N hN hNlip hsmall
  let u := hc.fixedPoint (heatDuhamelPicard T u₀ N hN.continuous hNlip)
  refine ⟨u, hc.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact hc.fixedPoint_unique' hv hc.fixedPoint_isFixedPt

/-- The fixed point is equivalently the unique solution of the displayed
Volterra identity.  The historical declaration name contains `mildSolution`,
but the identity has constant linear term `u₀`, not `H_t u₀`. -/
theorem exists_unique_heatDuhamel_mildSolution
    (T L : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hsmall : T * L < 1) :
    ∃! u : DuhamelPath T (E →ᵇ F),
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) = u₀ ∧
      ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
        u t = u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
            (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
  rcases exists_unique_heatDuhamelPicard_fixedPoint
    (E := E) (F := F) T L u₀ N hN hNlip hsmall with ⟨u, hu, huniq⟩
  have hmild : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      u t = u₀ + ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
    intro t
    have ht := congrArg
      (fun w : DuhamelPath T (E →ᵇ F) ↦ w t) hu
    exact ht.symm
  refine ⟨u, ⟨?_, hmild⟩, ?_⟩
  · simpa using hmild (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ))
  · intro v hv
    apply huniq v
    apply ContinuousMap.ext
    intro t
    exact (hv.2 t).symm

/-- A uniform nonlinearity bound keeps the Volterra iterate within
distance `T B` of the prescribed initial path. -/
theorem dist_heatDuhamelPicard_constantDuhamelPath_le
    (T B : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    (u : DuhamelPath T (E →ᵇ F)) :
    dist (heatDuhamelPicard T u₀ N hN hNlip u)
      (constantDuhamelPath T u₀) ≤ (T : ℝ) * (B : ℝ) := by
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg T.property B.property)).mpr
  intro t
  change ‖u₀ + (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))) - u₀‖ ≤ _
  rw [add_sub_cancel_left]
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤ (B : ℝ) := by
    intro s _hs
    calc
      ‖vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
          ≤ ‖vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)‖ *
              ‖N (u (Set.projIcc 0 (T : ℝ) T.property s))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (B : ℝ) :=
        mul_le_mul
          (norm_vectorHeatSemigroupNonnegative_le_one
            (E := E) (F := F) ((t : ℝ) - s))
          (hNbound _) (norm_nonneg _) zero_le_one
      _ = (B : ℝ) := one_mul _
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupNonnegative (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ (B : ℝ) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (B : ℝ) * (t : ℝ) := by
      rw [sub_zero, abs_of_nonneg t.property.1]
    _ ≤ (B : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2 B.property
    _ = (T : ℝ) * (B : ℝ) := mul_comm _ _

/-- Explicit closed-ball preservation for the heat-propagated Volterra map. -/
theorem heatDuhamelPicard_mapsTo_closedBall
    (T B : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : Continuous N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hTR : (T : ℝ) * (B : ℝ) ≤ R) :
    MapsTo (heatDuhamelPicard T u₀ N hN hNlip)
      (Metric.closedBall (constantDuhamelPath T u₀) R)
      (Metric.closedBall (constantDuhamelPath T u₀) R) := by
  intro u _hu
  exact (dist_heatDuhamelPicard_constantDuhamelPath_le
    (E := E) (F := F) T B u₀ N hN hNlip hNbound u).trans hTR

/-- Local fixed point in a prescribed invariant closed ball. -/
theorem exists_heatDuhamelPicard_fixedPoint_mem_closedBall
    (T B L : ℝ≥0) (u₀ : E →ᵇ F) (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : LipschitzWith L N)
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F))
    (hNbound : ∀ z, ‖N z‖ ≤ (B : ℝ))
    {R : ℝ} (hR : 0 ≤ R) (hTR : (T : ℝ) * (B : ℝ) ≤ R)
    (hsmall : T * L < 1) :
    ∃ u ∈ Metric.closedBall (constantDuhamelPath T u₀) R,
      heatDuhamelPicard T u₀ N hN.continuous hNlip u = u ∧
      ∀ v ∈ Metric.closedBall (constantDuhamelPath T u₀) R,
        heatDuhamelPicard T u₀ N hN.continuous hNlip v = v → v = u := by
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := E →ᵇ F) (q := T * L)
    (heatDuhamelPicard T u₀ N hN.continuous hNlip)
    (constantDuhamelPath T u₀) hR
  · exact heatDuhamelPicard_mapsTo_closedBall
      (E := E) (F := F) T B u₀ N hN.continuous hNlip hNbound hTR
  · intro u v _hu _hv t
    rw [heatDuhamelPicard_sub_eq_projectedDuhamelDifference
      (E := E) (F := F) T u₀ N hN.continuous hNlip u v t]
    have hbound := norm_projectedDuhamelDifference_le
      (X := E →ᵇ F) T 1 L
      (vectorHeatSemigroupNonnegative (E := E) (F := F)) N
      (fun r _hr ↦ norm_vectorHeatSemigroupNonnegative_le_one
        (E := E) (F := F) r)
      hN u v t
    simpa using hbound
  · simpa using hsmall

end Poincare
