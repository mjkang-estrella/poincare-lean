import Poincare.Global.HeatSemigroupBUCStrongContinuity
import Poincare.Global.HeatSemigroupPositiveContinuity

/-!
# The heat operator on the `BUC` Banach space

Positive-time heat convolution restricts to a norm-nonexpanding continuous
linear map on bounded uniformly continuous functions.  Its zero-time extension
converges strongly to the identity on every datum.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Positive-time heat convolution as a linear map on `BUC(E,F)`. -/
def vectorHeatSemigroupBUCLinearMap {t : ℝ} (ht : 0 < t) :
    BoundedUniformContinuousFunction (E := E) (F := F) →ₗ[ℝ]
      BoundedUniformContinuousFunction (E := E) (F := F) where
  toFun := vectorHeatSemigroupBUC (E := E) (F := F) ht
  map_add' f g := by
    apply Subtype.ext
    exact vectorHeatSolutionBCF_add (E := E) ht (f : E →ᵇ F) (g : E →ᵇ F)
  map_smul' c f := by
    apply Subtype.ext
    exact vectorHeatSolutionBCF_smul (E := E) ht c (f : E →ᵇ F)

@[simp]
theorem vectorHeatSemigroupBUCLinearMap_apply {t : ℝ} (ht : 0 < t)
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    vectorHeatSemigroupBUCLinearMap (E := E) (F := F) ht f =
      vectorHeatSemigroupBUC (E := E) (F := F) ht f :=
  rfl

/-- Positive-time heat convolution as a contraction operator on `BUC`. -/
def vectorHeatSemigroupBUCLM {t : ℝ} (ht : 0 < t) :
    BoundedUniformContinuousFunction (E := E) (F := F) →L[ℝ]
      BoundedUniformContinuousFunction (E := E) (F := F) :=
  LinearMap.mkContinuous
    (vectorHeatSemigroupBUCLinearMap (E := E) (F := F) ht) 1
    (fun f ↦ by
      change ‖vectorHeatSolutionBCF (E := E) ht (f : E →ᵇ F)‖ ≤ 1 * ‖f‖
      simpa using norm_vectorHeatSolutionBCF_le (E := E) ht (f : E →ᵇ F))

@[simp]
theorem vectorHeatSemigroupBUCLM_apply {t : ℝ} (ht : 0 < t)
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    vectorHeatSemigroupBUCLM (E := E) (F := F) ht f =
      vectorHeatSemigroupBUC (E := E) (F := F) ht f :=
  rfl

/-- The positive-time heat operator has norm at most one on `BUC`. -/
theorem norm_vectorHeatSemigroupBUCLM_le_one {t : ℝ} (ht : 0 < t) :
    ‖vectorHeatSemigroupBUCLM (E := E) (F := F) ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro f
  change ‖vectorHeatSolutionBCF (E := E) ht (f : E →ᵇ F)‖ ≤ 1 * ‖f‖
  simpa using norm_vectorHeatSolutionBCF_le (E := E) ht (f : E →ᵇ F)

/-- Restriction from `C_b` to `BUC` cannot increase the norm of a difference
of heat operators. -/
theorem norm_vectorHeatSemigroupBUCLM_sub_le
    (s t : {t : ℝ // 0 < t}) :
    ‖vectorHeatSemigroupBUCLM (E := E) (F := F) s.property -
        vectorHeatSemigroupBUCLM (E := E) (F := F) t.property‖ ≤
      ‖vectorHeatSemigroupCLM (E := E) (F := F) s.property -
        vectorHeatSemigroupCLM (E := E) (F := F) t.property‖ := by
  let C := ‖vectorHeatSemigroupCLM (E := E) (F := F) s.property -
    vectorHeatSemigroupCLM (E := E) (F := F) t.property‖
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro f
  change ‖(vectorHeatSemigroupCLM (E := E) (F := F) s.property -
      vectorHeatSemigroupCLM (E := E) (F := F) t.property) (f : E →ᵇ F)‖ ≤
    C * ‖f‖
  exact ContinuousLinearMap.le_opNorm _ _

/-- The zero-time extension of the heat operator on `BUC`. -/
def vectorHeatSemigroupBUCExtended (t : ℝ) :
    BoundedUniformContinuousFunction (E := E) (F := F) →L[ℝ]
      BoundedUniformContinuousFunction (E := E) (F := F) :=
  if ht : 0 < t then vectorHeatSemigroupBUCLM (E := E) (F := F) ht else
    ContinuousLinearMap.id ℝ _

@[simp]
theorem vectorHeatSemigroupBUCExtended_zero :
    vectorHeatSemigroupBUCExtended (E := E) (F := F) 0 =
      ContinuousLinearMap.id ℝ _ := by
  simp [vectorHeatSemigroupBUCExtended]

/-- The zero-time extension is strongly continuous at zero on every `BUC`
datum. -/
theorem tendsto_vectorHeatSemigroupBUCExtended_apply_zero
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    Tendsto
      (fun t : ℝ ↦ vectorHeatSemigroupBUCExtended (E := E) (F := F) t f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  have hnorm := tendsto_norm_vectorHeatSemigroup_sub_of_uniformContinuous
    (E := E) (F := F) (f : E →ᵇ F) f.property
  rw [Metric.tendsto_nhdsWithin_nhds] at hnorm
  intro ε hε
  rcases hnorm ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro t htI htδ
  have ht : 0 < t := Set.mem_Ioi.mp htI
  have h := hclose htI htδ
  rw [vectorHeatSemigroupBUCExtended, dif_pos ht]
  change dist
      (vectorHeatSemigroupBUCLM (E := E) (F := F) ht f) f < ε
  rw [dist_eq_norm]
  simpa [dif_pos ht, Real.norm_of_nonneg (norm_nonneg _), dist_eq_norm] using h

/-- Strong continuity at zero, in norm-difference form. -/
theorem tendsto_norm_vectorHeatSemigroupBUCExtended_sub_zero
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    Tendsto
      (fun t : ℝ ↦
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t f - f‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [tendsto_iff_norm_sub_tendsto_zero] using
    tendsto_vectorHeatSemigroupBUCExtended_apply_zero (E := E) (F := F) f

/-- The zero-time strong limit also holds from a full two-sided neighborhood,
because the extension is the identity at nonpositive times. -/
theorem tendsto_vectorHeatSemigroupBUCExtended_apply_zero_full
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    Tendsto
      (fun t : ℝ ↦ vectorHeatSemigroupBUCExtended (E := E) (F := F) t f)
      (nhds 0) (nhds f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos := tendsto_vectorHeatSemigroupBUCExtended_apply_zero
    (E := E) (F := F) f
  rw [Metric.tendsto_nhdsWithin_nhds] at hpos
  rcases hpos ε hε with ⟨δ, hδ, hclose⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t htδ
  by_cases ht : 0 < t
  · exact hclose (Set.mem_Ioi.mpr ht) htδ
  · simp [vectorHeatSemigroupBUCExtended, ht, hε]

/-- For each `BUC` datum, the extended heat orbit is continuous at every real
time (and hence in particular on the nonnegative half-line). -/
theorem continuous_vectorHeatSemigroupBUCExtended_apply
    (f : BoundedUniformContinuousFunction (E := E) (F := F)) :
    Continuous (fun t : ℝ ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t f) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hev : ∀ᶠ s in 𝓝 t, s < 0 := Iio_mem_nhds ht
    have hc : ContinuousAt (fun _ : ℝ ↦ f) t := continuousAt_const
    apply hc.congr_of_eventuallyEq
    exact hev.mono fun s hs ↦ by
      simp [vectorHeatSemigroupBUCExtended, not_lt.mpr hs.le]
  · rw [ContinuousAt]
    simpa using tendsto_vectorHeatSemigroupBUCExtended_apply_zero_full
      (E := E) (F := F) f
  · let tp : {s : ℝ // 0 < s} := ⟨t, ht⟩
    have hev : ∀ᶠ s in 𝓝 t, 0 < s := Ioi_mem_nhds ht
    let lift : ℝ → {s : ℝ // 0 < s} := fun s ↦
      if hs : 0 < s then ⟨s, hs⟩ else tp
    have hlift : ContinuousAt lift t := by
      rw [ContinuousAt, tendsto_subtype_rng]
      have hv : Tendsto (fun s ↦ (lift s).1) (𝓝 t) (𝓝 t) := by
        apply tendsto_id.congr'
        exact hev.mono fun s hs ↦ by simp [lift, hs]
      simpa [lift, ht] using hv
    have hop :=
      (continuous_vectorHeatSemigroupCLM_positive
        (E := E) (F := F)).continuousAt.comp hlift
    have hbase : ContinuousAt (fun s ↦
        vectorHeatSemigroupCLM (E := E) (F := F) (lift s).property
          (f : E →ᵇ F)) t :=
      hop.clm_apply continuousAt_const
    have happ : ContinuousAt (fun s ↦
        vectorHeatSemigroupBUCLM (E := E) (F := F) (lift s).property f) t := by
      rw [ContinuousAt, tendsto_subtype_rng]
      simpa using hbase
    apply happ.congr_of_eventuallyEq
    exact hev.mono fun s hs ↦ by
      simp [lift, hs, vectorHeatSemigroupBUCExtended]

end Poincare
