import Poincare.Global.HeatDuhamelBUCGeneratorDini
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of Hölder-controlled heat Duhamel generator values

The endpoint cancellation in a heat Duhamel term has size `O(r^α)` while the
positive-time generator has size `O(r⁻¹)`.  A uniform positive Hölder exponent
therefore gives the integrable majorant `r^(α-1)`.  This file uses that
majorant to prove continuity, on compact intervals separated from zero, of
the strong-generator value constructed in `HeatDuhamelBUCGeneratorDini`.

The moving interval is first written on the fixed domain `[0,b]` by the
substitution `r = t-s` and an indicator of `{r ≤ t}`.  The indicator is
continuous in `t` away from the single null point `r = t`, so dominated
convergence applies.
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

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Uniform endpoint Hölder control of the forcing makes the selected Duhamel
generator value continuous on every compact positive-time interval.  Only
comparisons of an earlier time `s` with an endpoint `t ∈ [a,b]` are needed. -/
theorem continuousOn_heatDuhamelBUCGeneratorValue_of_uniformHolder
    {G : ℝ → BUC} (hG : Continuous G) {a b K α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ t ∈ Set.Icc a b,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖G s - G t‖ ≤ K * |t - s| ^ α) :
    ContinuousOn
      (heatDuhamelBUCGeneratorValue (E := E) (F := F) G)
      (Set.Icc a b) := by
  let q : ℝ → ℝ → BUC := fun t r ↦
    vectorHeatTimeDerivativeBUC (E := E) (F := F) r
      (G (t - r) - G t)
  let qcut : ℝ → ℝ → BUC := fun t r ↦
    Set.indicator (Set.Iic t) (q t) r
  let C : ℝ := heatKernelTimeDerivativeL1Norm (E := E) 1
  let bound : ℝ → ℝ := fun r ↦ (C * K) * r ^ (α - 1)
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 ≤ C := by
    dsimp [C, heatKernelTimeDerivativeL1Norm]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hpowOn : IntegrableOn (fun r : ℝ ↦ r ^ (α - 1))
      (Set.Ioo (0 : ℝ) b) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hb).2 (by linarith)
  have hpow : IntervalIntegrable (fun r : ℝ ↦ r ^ (α - 1))
      volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).2 hpowOn
  have hboundInt : IntervalIntegrable bound volume 0 b := by
    simpa only [bound] using hpow.const_mul (C * K)
  have hqMeas (t : ℝ) :
      AEStronglyMeasurable (q t) (volume.restrict (Ι (0 : ℝ) b)) := by
    have hqCont : ContinuousOn (q t) (Set.Ioi (0 : ℝ)) := by
      have hjoint := continuousOn_vectorHeatTimeDerivativeBUC_prod_Ioi
        (E := E) (F := F)
      have hmap : Continuous (fun r : ℝ ↦ (r, G (t - r) - G t)) :=
        continuous_id.prodMk
          ((hG.comp (continuous_const.sub continuous_id)).sub continuous_const)
      apply hjoint.comp hmap.continuousOn
      intro r hr
      exact ⟨hr, Set.mem_univ _⟩
    rw [Set.uIoc_of_le hb.le]
    exact (hqCont.mono fun _ hr ↦ hr.1).aestronglyMeasurable measurableSet_Ioc
  have hqcutMeas : ∀ t,
      AEStronglyMeasurable (qcut t) (volume.restrict (Ι (0 : ℝ) b)) := by
    intro t
    simpa only [qcut] using
      (hqMeas t).indicator (measurableSet_Iic : MeasurableSet (Set.Iic t))
  have hdominated (t : ℝ) (ht : t ∈ Set.Icc a b) (r : ℝ)
      (hr : r ∈ Ι (0 : ℝ) b) :
      ‖qcut t r‖ ≤ bound r := by
    rw [Set.uIoc_of_le hb.le] at hr
    have hrpos : 0 < r := hr.1
    by_cases hrt : r ≤ t
    · dsimp [qcut]
      rw [Set.indicator_of_mem (show r ∈ Set.Iic t from hrt)]
      have htr : t - r ∈ Set.Icc (0 : ℝ) t :=
        ⟨sub_nonneg.mpr hrt,
          sub_le_self t hrpos.le⟩
      have hmod : ‖G (t - r) - G t‖ ≤ K * r ^ α := by
        simpa [abs_of_pos hrpos] using hholder t ht (t - r) htr
      calc
        ‖q t r‖ ≤ (C / r) * ‖G (t - r) - G t‖ := by
          simpa only [q, C] using
            norm_vectorHeatTimeDerivativeBUC_le_inv
              (E := E) (F := F) hrpos (G (t - r) - G t)
        _ ≤ (C / r) * (K * r ^ α) :=
          mul_le_mul_of_nonneg_left hmod (div_nonneg hC hrpos.le)
        _ = bound r := by
          dsimp [bound]
          rw [Real.rpow_sub_one hrpos.ne' α]
          field_simp [hrpos.ne']
    · dsimp [qcut]
      rw [Set.indicator_of_notMem (show r ∉ Set.Iic t from hrt)]
      dsimp [bound]
      simpa only [norm_zero] using
        mul_nonneg (mul_nonneg hC hK)
          (Real.rpow_nonneg hrpos.le (α - 1))
  have hqContinuous (r : ℝ) (hr : 0 < r) :
      Continuous (fun t ↦ q t r) := by
    let Ar : BUC →L[ℝ] BUC :=
      vectorHeatTimeDerivativeBUCCLM (E := E) (F := F) r hr
    have harg : Continuous (fun t ↦ G (t - r) - G t) :=
      (hG.comp (continuous_id.sub continuous_const)).sub hG
    have h := Ar.continuous.comp harg
    simpa only [q, Ar, vectorHeatTimeDerivativeBUCCLM_apply] using h
  have hfixed : ContinuousOn
      (fun t ↦ ∫ r : ℝ in (0 : ℝ)..b, qcut t r)
      (Set.Icc a b) := by
    intro t₀ ht₀
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (μ := volume) (F := qcut) (bound := bound)
    · exact Filter.Eventually.of_forall hqcutMeas
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Filter.Eventually.of_forall fun r hr ↦ hdominated t ht r hr
    · exact hboundInt
    · refine (MeasureTheory.volume.ae_ne t₀).mono ?_
      intro r hne hr
      rw [Set.uIoc_of_le hb.le] at hr
      have hqr := hqContinuous r hr.1
      rcases hne.lt_or_gt with hrt | htr
      · have heq : (fun t ↦ qcut t r) =ᶠ[𝓝[Set.Icc a b] t₀]
            (fun t ↦ q t r) := by
          filter_upwards [
            mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hrt)
          ] with t (ht : r < t)
          dsimp [qcut]
          rw [Set.indicator_of_mem (show r ∈ Set.Iic t from ht.le)]
        apply hqr.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq
        dsimp [qcut]
        rw [Set.indicator_of_mem (show r ∈ Set.Iic t₀ from hrt.le)]
      · have heq : (fun t ↦ qcut t r) =ᶠ[𝓝[Set.Icc a b] t₀]
            (fun _ : ℝ ↦ (0 : BUC)) := by
          filter_upwards [
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htr)
          ] with t (ht : t < r)
          dsimp [qcut]
          rw [Set.indicator_of_notMem
            (show r ∉ Set.Iic t from not_le.mpr ht)]
        apply continuousWithinAt_const.congr_of_eventuallyEq heq
        dsimp [qcut]
        rw [Set.indicator_of_notMem
          (show r ∉ Set.Iic t₀ from not_le.mpr htr)]
  have hcut (t : ℝ) (ht : t ∈ Set.Icc a b) :
      (∫ r : ℝ in (0 : ℝ)..b, qcut t r) =
        ∫ r : ℝ in (0 : ℝ)..t, q t r := by
    have ht0b : t ∈ Set.Icc (0 : ℝ) b :=
      ⟨ha.le.trans ht.1, ht.2⟩
    simpa only [qcut] using
      (intervalIntegral.integral_indicator
        (μ := volume) (f := q t) ht0b)
  have hchange (t : ℝ) :
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
          (G s - G t)) =
        ∫ r : ℝ in (0 : ℝ)..t, q t r := by
    simpa [q] using
      (intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := t) (f := q t) t)
  have hresidual : ContinuousOn
      (fun t ↦ ∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
          (G s - G t))
      (Set.Icc a b) := by
    apply hfixed.congr
    intro t ht
    exact ((hcut t ht).trans (hchange t).symm).symm
  have hbase : Continuous (fun t ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t (G t) - G t) :=
    (continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F) continuous_id hG).sub hG
  simpa only [heatDuhamelBUCGeneratorValue] using
    hbase.continuousOn.add hresidual

end Poincare
