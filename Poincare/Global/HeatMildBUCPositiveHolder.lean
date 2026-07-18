import Poincare.Global.HeatDuhamelBUCGeneratorDini
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive-time Hölder regularity of bounded-forcing heat mild paths

For arbitrary `BUC` initial data there is no power-rate claim at time zero.
On every compact interval `[a,b]` with `a > 0`, however, the homogeneous heat
orbit is Lipschitz.  The Duhamel term with bounded continuous forcing is
Hölder of every exponent `α ∈ (0,1)`.

The key estimate interpolates two bounds for a heat-semigroup increment:

* generator smoothing gives `O(h/q)` after a positive elapsed time `q`;
* contractivity gives the uniform bound `2`.

Their interpolation is `O((h/q)^α)`.  Since `q ^ (-α)` is integrable at zero
exactly when `α < 1`, this controls the full Duhamel increment without making
any endpoint-zero regularity assumption on the initial datum.
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

/-- The heat Duhamel value for an arbitrary all-real forcing path. -/
def heatDuhamelBUCValue (G : ℝ → BUC) (t : ℝ) : BUC :=
  ∫ s : ℝ in (0 : ℝ)..t,
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s)

/-- Homogeneous heat orbit plus the arbitrary-forcing Duhamel value. -/
def heatMildBUCValue (u₀ : BUC) (G : ℝ → BUC) (t : ℝ) : BUC :=
  vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ +
    heatDuhamelBUCValue (E := E) (F := F) G t

/-- Contractivity of the extended heat operator on each datum. -/
theorem norm_vectorHeatSemigroupBUCExtended_apply_le
    (t : ℝ) (f : BUC) :
    ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t f‖ ≤ ‖f‖ := by
  calc
    ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t f‖ ≤
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_vectorHeatSemigroupBUCExtended_le_one (E := E) (F := F) t)
      (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-- Nonnegativity of the time-one differentiated-Gaussian `L¹` norm. -/
theorem heatKernelTimeDerivativeL1Norm_one_nonneg :
    0 ≤ heatKernelTimeDerivativeL1Norm (E := E) 1 := by
  exact integral_nonneg fun _ ↦ abs_nonneg _

/-- After positive elapsed time `q`, a further heat time `h` changes the orbit
by at most `h` times the smoothed generator norm. -/
theorem norm_vectorHeatSemigroupBUCExtended_add_sub_le_generator
    {q h : ℝ} (hq : 0 < q) (hh : 0 ≤ h) (f : BUC) :
    ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
        vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
      h * ((heatKernelTimeDerivativeL1Norm (E := E) 1 / q) * ‖f‖) := by
  let Af : BUC := vectorHeatTimeDerivativeBUC (E := E) (F := F) q f
  have hgraph :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) hq f
  have hid := hgraph.integral_semigroup_eq_sub hh
  have hsemigroup :
      vectorHeatSemigroupBUCExtended (E := E) (F := F) h
          (vectorHeatSemigroupBUCExtended (E := E) (F := F) q f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f := by
    rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) hh hq.le f]
    congr 2
    ring
  rw [hsemigroup] at hid
  have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) h,
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) s Af‖ ≤ ‖Af‖ := by
    intro s _hs
    exact norm_vectorHeatSemigroupBUCExtended_apply_le
      (E := E) (F := F) s Af
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hnorm' :
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
        h * ‖Af‖ := by
    rw [← hid]
    simpa only [Af, sub_zero, abs_of_nonneg hh, mul_comm] using hnorm
  have hAf := norm_vectorHeatTimeDerivativeBUC_le_inv
    (E := E) (F := F) hq f
  exact hnorm'.trans
    (mul_le_mul_of_nonneg_left (by simpa only [Af] using hAf) hh)

/-- Interpolated positive-time heat increment bound.  It combines the
generator estimate when `h ≤ q` with contractivity when `q ≤ h`. -/
theorem norm_vectorHeatSemigroupBUCExtended_add_sub_le_rpow
    {q h α : ℝ} (hq : 0 < q) (hh : 0 ≤ h)
    (hα0 : 0 < α) (hα1 : α < 1) (f : BUC) :
    ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
        vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
      (heatKernelTimeDerivativeL1Norm (E := E) 1 + 2) *
        (h ^ α * q ^ (-α)) * ‖f‖ := by
  let C : ℝ := heatKernelTimeDerivativeL1Norm (E := E) 1
  have hC : 0 ≤ C := heatKernelTimeDerivativeL1Norm_one_nonneg (E := E)
  rcases hh.eq_or_lt with rfl | hhpos
  · simp [Real.zero_rpow hα0.ne']
  have hxpos : 0 < h / q := div_pos hhpos hq
  have hxpow : (h / q) ^ α = h ^ α * q ^ (-α) := by
    rw [Real.div_rpow hh hq.le, div_eq_mul_inv,
      ← Real.rpow_neg hq.le α]
  rcases le_total h q with hhq | hqh
  · have hxle : h / q ≤ (h / q) ^ α :=
      Real.self_le_rpow_of_le_one hxpos.le
        ((div_le_one hq).2 hhq) hα1.le
    have hgen :=
      norm_vectorHeatSemigroupBUCExtended_add_sub_le_generator
        (E := E) (F := F) hq hh f
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
          h * ((C / q) * ‖f‖) := by simpa only [C] using hgen
      _ = C * (h / q) * ‖f‖ := by ring
      _ ≤ C * (h / q) ^ α * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxle hC) (norm_nonneg f)
      _ ≤ (C + 2) * (h / q) ^ α * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
        exact mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hxpos.le α)
      _ = (C + 2) * (h ^ α * q ^ (-α)) * ‖f‖ := by rw [hxpow]
  · have hcontract :
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
            vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
          2 * ‖f‖ := by
      calc
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
            vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
            ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f‖ +
              ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ :=
          norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add
          (norm_vectorHeatSemigroupBUCExtended_apply_le
            (E := E) (F := F) (q + h) f)
          (norm_vectorHeatSemigroupBUCExtended_apply_le
            (E := E) (F := F) q f)
        _ = 2 * ‖f‖ := by ring
    have hxone : 1 ≤ (h / q) ^ α :=
      Real.one_le_rpow ((le_div_iff₀ hq).2 (by simpa using hqh)) hα0.le
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (q + h) f -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) q f‖ ≤
          2 * ‖f‖ := hcontract
      _ ≤ (C + 2) * 1 * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
        nlinarith
      _ ≤ (C + 2) * (h / q) ^ α * ‖f‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
        exact mul_le_mul_of_nonneg_left hxone (by linarith)
      _ = (C + 2) * (h ^ α * q ^ (-α)) * ‖f‖ := by rw [hxpow]

/-- Integral of the translated endpoint singularity used in the Duhamel
estimate. -/
theorem integral_sub_rpow_neg
    {r α : ℝ} (hα1 : α < 1) :
    (∫ s : ℝ in (0 : ℝ)..r, (r - s) ^ (-α)) =
      r ^ (1 - α) / (1 - α) := by
  have hchange := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := r) (fun q : ℝ ↦ q ^ (-α)) r
  calc
    (∫ s : ℝ in (0 : ℝ)..r, (r - s) ^ (-α)) =
        ∫ q : ℝ in (0 : ℝ)..r, q ^ (-α) := by
      simpa only [sub_self, sub_zero] using hchange
    _ = r ^ (1 - α) / (1 - α) := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.zero_rpow (by linarith : -α + 1 ≠ 0)]
      congr 1 <;> ring_nf

/-- Ordered-time Duhamel increment estimate. -/
theorem norm_heatDuhamelBUCValue_sub_le_of_le
    {G : ℝ → BUC} (hG : Continuous G) {r t b M α : ℝ}
    (hr : 0 < r) (hrt : r ≤ t) (htb : t ≤ b)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hGbound : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G s‖ ≤ M) :
    ‖heatDuhamelBUCValue (E := E) (F := F) G t -
        heatDuhamelBUCValue (E := E) (F := F) G r‖ ≤
      M * (t - r) +
        ((heatKernelTimeDerivativeL1Norm (E := E) 1 + 2) * M) *
          (t - r) ^ α * r ^ (1 - α) / (1 - α) := by
  let C : ℝ := heatKernelTimeDerivativeL1Norm (E := E) 1
  let h : ℝ := t - r
  let Ft : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s)
  let Fr : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (r - s) (G s)
  let old : ℝ → BUC := fun s ↦ Ft s - Fr s
  have hh : 0 ≤ h := sub_nonneg.mpr hrt
  have hFt : Continuous Ft := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hG
  have hFr : Continuous Fr := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hG
  have hdecomp :
      heatDuhamelBUCValue (E := E) (F := F) G t -
          heatDuhamelBUCValue (E := E) (F := F) G r =
        (∫ s : ℝ in (0 : ℝ)..r, old s) +
          ∫ s : ℝ in r..t, Ft s := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hFt.intervalIntegrable (μ := volume) (0 : ℝ) r)
      (hFt.intervalIntegrable (μ := volume) r t)
    have hsub := intervalIntegral.integral_sub
      (hFt.intervalIntegrable (μ := volume) (0 : ℝ) r)
      (hFr.intervalIntegrable (μ := volume) (0 : ℝ) r)
    change (∫ s : ℝ in (0 : ℝ)..t, Ft s) -
        (∫ s : ℝ in (0 : ℝ)..r, Fr s) =
      (∫ s : ℝ in (0 : ℝ)..r, old s) +
        ∫ s : ℝ in r..t, Ft s
    calc
      (∫ s : ℝ in (0 : ℝ)..t, Ft s) -
          (∫ s : ℝ in (0 : ℝ)..r, Fr s) =
        ((∫ s : ℝ in (0 : ℝ)..r, Ft s) -
          ∫ s : ℝ in (0 : ℝ)..r, Fr s) +
            ∫ s : ℝ in r..t, Ft s := by
          rw [← hadd]
          abel
      _ = (∫ s : ℝ in (0 : ℝ)..r, old s) +
          ∫ s : ℝ in r..t, Ft s := by
        congr 1
        simpa only [old] using hsub.symm
  have hpow : IntervalIntegrable (fun q : ℝ ↦ q ^ (-α)) volume 0 r := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).2
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff hr).2 (by linarith)
  have hpowSub : IntervalIntegrable (fun s : ℝ ↦ (r - s) ^ (-α))
      volume 0 r := by
    simpa only [sub_self, sub_zero] using (hpow.comp_sub_left r).symm
  let coeff : ℝ := (C + 2) * M * h ^ α
  have hmajorant : IntervalIntegrable
      (fun s : ℝ ↦ coeff * (r - s) ^ (-α)) volume 0 r :=
    hpowSub.const_mul coeff
  have holdNorm : ‖∫ s : ℝ in (0 : ℝ)..r, old s‖ ≤
      coeff * (r ^ (1 - α) / (1 - α)) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hr.le
      ((MeasureTheory.volume.ae_ne r).mono fun s hsrne hs ↦ by
        have hsr : s < r := lt_of_le_of_ne hs.2 hsrne
        have hq : 0 < r - s := sub_pos.mpr hsr
        have hsB : s ∈ Set.Icc (0 : ℝ) b :=
          ⟨hs.1.le, (hs.2.trans hrt).trans htb⟩
        have hinc :=
          norm_vectorHeatSemigroupBUCExtended_add_sub_le_rpow
            (E := E) (F := F) hq hh hα0 hα1 (G s)
        have hinc' : ‖old s‖ ≤
            (C + 2) * (h ^ α * (r - s) ^ (-α)) * ‖G s‖ := by
          have htime : t - s = (r - s) + h := by
            dsimp only [h]
            ring
          dsimp only [old, Ft, Fr]
          rw [htime]
          simpa only [C] using hinc
        calc
          ‖old s‖ ≤ (C + 2) * (h ^ α * (r - s) ^ (-α)) * ‖G s‖ := hinc'
          _ ≤ (C + 2) * (h ^ α * (r - s) ^ (-α)) * M := by
            apply mul_le_mul_of_nonneg_left (hGbound s hsB)
            exact mul_nonneg
              (add_nonneg
                (heatKernelTimeDerivativeL1Norm_one_nonneg (E := E))
                (by norm_num))
              (mul_nonneg (Real.rpow_nonneg hh _)
                (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
          _ = coeff * (r - s) ^ (-α) := by ring)
      hmajorant
    calc
      ‖∫ s : ℝ in (0 : ℝ)..r, old s‖ ≤
          ∫ s : ℝ in (0 : ℝ)..r, coeff * (r - s) ^ (-α) := hnorm
      _ = coeff * ∫ s : ℝ in (0 : ℝ)..r, (r - s) ^ (-α) := by
        rw [intervalIntegral.integral_const_mul]
      _ = coeff * (r ^ (1 - α) / (1 - α)) := by
        rw [integral_sub_rpow_neg hα1]
  have htailNorm : ‖∫ s : ℝ in r..t, Ft s‖ ≤ M * (t - r) := by
    have hpoint : ∀ s ∈ Set.uIoc r t, ‖Ft s‖ ≤ M := by
      intro s hs
      rw [Set.uIoc_of_le hrt] at hs
      exact (norm_vectorHeatSemigroupBUCExtended_apply_le
        (E := E) (F := F) (t - s) (G s)).trans
          (hGbound s ⟨hr.le.trans hs.1.le, hs.2.trans htb⟩)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa only [abs_of_nonneg (sub_nonneg.mpr hrt)] using hnorm
  rw [hdecomp]
  calc
    ‖(∫ s : ℝ in (0 : ℝ)..r, old s) + ∫ s : ℝ in r..t, Ft s‖ ≤
        ‖∫ s : ℝ in (0 : ℝ)..r, old s‖ + ‖∫ s : ℝ in r..t, Ft s‖ :=
      norm_add_le _ _
    _ ≤ coeff * (r ^ (1 - α) / (1 - α)) + M * (t - r) :=
      add_le_add holdNorm htailNorm
    _ = M * (t - r) + ((C + 2) * M) *
        (t - r) ^ α * r ^ (1 - α) / (1 - α) := by
      dsimp only [coeff, C, h]
      ring

/-- The elementary conversion from a first-order increment to an `α`-power
increment on a bounded interval. -/
theorem sub_le_rpow_mul_of_le
    {r t b α : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htb : t ≤ b)
    (hα0 : 0 < α) (hα1 : α < 1) :
    t - r ≤ b ^ (1 - α) * (t - r) ^ α := by
  have hh : 0 ≤ t - r := sub_nonneg.mpr hrt
  have hhb : t - r ≤ b := by linarith
  rcases hh.eq_or_lt with hzero | hhpos
  · have htr : t = r := by linarith
    subst t
    simp [hα0.ne']
  have hb : 0 < b := hhpos.trans_le hhb
  calc
    t - r = (t - r) ^ (1 - α) * (t - r) ^ α := by
      calc
        t - r = (t - r) ^ (1 : ℝ) := (Real.rpow_one (t - r)).symm
        _ = (t - r) ^ ((1 - α) + α) := by
          congr 1
          ring
        _ = (t - r) ^ (1 - α) * (t - r) ^ α :=
          Real.rpow_add hhpos (1 - α) α
    _ ≤ b ^ (1 - α) * (t - r) ^ α := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hh hhb (by linarith))
        (Real.rpow_nonneg hh α)

/-- Explicit ordered-time Hölder estimate for a bounded-forcing mild path on
a compact interval separated from zero. -/
theorem norm_heatMildBUCValue_sub_le_rpow_of_le
    (u₀ : BUC) {G : ℝ → BUC} (hG : Continuous G)
    {a b M α r t : ℝ} (ha : 0 < a) (hr : r ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) (hrt : r ≤ t)
    (hM : 0 ≤ M) (hα0 : 0 < α) (hα1 : α < 1)
    (hGbound : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G s‖ ≤ M) :
    ‖heatMildBUCValue (E := E) (F := F) u₀ G t -
        heatMildBUCValue (E := E) (F := F) u₀ G r‖ ≤
      (b ^ (1 - α) *
        ((heatKernelTimeDerivativeL1Norm (E := E) 1 / a) * ‖u₀‖ + M +
          ((heatKernelTimeDerivativeL1Norm (E := E) 1 + 2) * M) /
            (1 - α))) *
        (t - r) ^ α := by
  let C : ℝ := heatKernelTimeDerivativeL1Norm (E := E) 1
  have hC : 0 ≤ C := heatKernelTimeDerivativeL1Norm_one_nonneg (E := E)
  have hrpos : 0 < r := ha.trans_le hr.1
  have hh : 0 ≤ t - r := sub_nonneg.mpr hrt
  have hhpow : t - r ≤ b ^ (1 - α) * (t - r) ^ α :=
    sub_le_rpow_mul_of_le hrpos.le hrt ht.2 hα0 hα1
  have hrpow : r ^ (1 - α) ≤ b ^ (1 - α) :=
    Real.rpow_le_rpow hrpos.le hr.2 (by linarith)
  have hlinear0 :=
    norm_vectorHeatSemigroupBUCExtended_add_sub_le_generator
      (E := E) (F := F) hrpos hh u₀
  have hlinear :
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀‖ ≤
        b ^ (1 - α) * ((C / a) * ‖u₀‖) * (t - r) ^ α := by
    have hdiv : C / r ≤ C / a := by
      exact div_le_div_of_nonneg_left hC ha hr.1
    have htime : r + (t - r) = t := by ring
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀‖ ≤
          (t - r) * ((C / r) * ‖u₀‖) := by
        simpa only [C, htime] using hlinear0
      _ ≤ (t - r) * ((C / a) * ‖u₀‖) := by gcongr
      _ ≤ (b ^ (1 - α) * (t - r) ^ α) * ((C / a) * ‖u₀‖) := by
        gcongr
      _ = b ^ (1 - α) * ((C / a) * ‖u₀‖) * (t - r) ^ α := by ring
  have hduhamel0 := norm_heatDuhamelBUCValue_sub_le_of_le
    (E := E) (F := F) hG hrpos hrt ht.2 hα0 hα1 hGbound
  have hdenom : 0 ≤ 1 - α := by linarith
  have hduhamelLinear : M * (t - r) ≤
      M * (b ^ (1 - α) * (t - r) ^ α) :=
    mul_le_mul_of_nonneg_left hhpow hM
  have hduhamelSingular :
      ((C + 2) * M) * (t - r) ^ α * r ^ (1 - α) / (1 - α) ≤
        ((C + 2) * M) * (t - r) ^ α * b ^ (1 - α) / (1 - α) := by
    apply div_le_div_of_nonneg_right _ hdenom
    apply mul_le_mul_of_nonneg_left hrpow
    exact mul_nonneg
      (mul_nonneg (add_nonneg hC (by norm_num)) hM)
      (Real.rpow_nonneg hh α)
  have hduhamel :
      ‖heatDuhamelBUCValue (E := E) (F := F) G t -
          heatDuhamelBUCValue (E := E) (F := F) G r‖ ≤
        b ^ (1 - α) *
          (M + ((C + 2) * M) / (1 - α)) * (t - r) ^ α := by
    calc
      ‖heatDuhamelBUCValue (E := E) (F := F) G t -
          heatDuhamelBUCValue (E := E) (F := F) G r‖ ≤
          M * (t - r) + ((C + 2) * M) *
            (t - r) ^ α * r ^ (1 - α) / (1 - α) := by
        simpa only [C] using hduhamel0
      _ ≤ M * (b ^ (1 - α) * (t - r) ^ α) +
          ((C + 2) * M) * (t - r) ^ α * b ^ (1 - α) / (1 - α) := by
        exact add_le_add hduhamelLinear hduhamelSingular
      _ = b ^ (1 - α) *
          (M + ((C + 2) * M) / (1 - α)) * (t - r) ^ α := by ring
  change ‖(vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ +
      heatDuhamelBUCValue (E := E) (F := F) G t) -
    (vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀ +
      heatDuhamelBUCValue (E := E) (F := F) G r)‖ ≤ _
  calc
    ‖(vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ +
        heatDuhamelBUCValue (E := E) (F := F) G t) -
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀ +
        heatDuhamelBUCValue (E := E) (F := F) G r)‖ ≤
        ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀‖ +
        ‖heatDuhamelBUCValue (E := E) (F := F) G t -
          heatDuhamelBUCValue (E := E) (F := F) G r‖ := by
      rw [show (vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ +
          heatDuhamelBUCValue (E := E) (F := F) G t) -
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀ +
          heatDuhamelBUCValue (E := E) (F := F) G r) =
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ -
          vectorHeatSemigroupBUCExtended (E := E) (F := F) r u₀) +
        (heatDuhamelBUCValue (E := E) (F := F) G t -
          heatDuhamelBUCValue (E := E) (F := F) G r) by abel]
      exact norm_add_le _ _
    _ ≤ b ^ (1 - α) * ((C / a) * ‖u₀‖) * (t - r) ^ α +
        b ^ (1 - α) *
          (M + ((C + 2) * M) / (1 - α)) * (t - r) ^ α :=
      add_le_add hlinear hduhamel
    _ = (b ^ (1 - α) *
        ((C / a) * ‖u₀‖ + M + ((C + 2) * M) / (1 - α))) *
        (t - r) ^ α := by ring

/-- Symmetric positive-window Hölder estimate for the mild path. -/
theorem norm_heatMildBUCValue_sub_le_rpow
    (u₀ : BUC) {G : ℝ → BUC} (hG : Continuous G)
    {a b M α : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hα0 : 0 < α) (hα1 : α < 1)
    (hGbound : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G s‖ ≤ M) :
    ∀ r ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖heatMildBUCValue (E := E) (F := F) u₀ G t -
          heatMildBUCValue (E := E) (F := F) u₀ G r‖ ≤
        (b ^ (1 - α) *
          ((heatKernelTimeDerivativeL1Norm (E := E) 1 / a) * ‖u₀‖ + M +
            ((heatKernelTimeDerivativeL1Norm (E := E) 1 + 2) * M) /
              (1 - α))) *
          |t - r| ^ α := by
  intro r hr t ht
  rcases le_total r t with hrt | htr
  · simpa [abs_of_nonneg (sub_nonneg.mpr hrt)] using
      norm_heatMildBUCValue_sub_le_rpow_of_le
        (E := E) (F := F) u₀ hG ha hr ht hrt hM hα0 hα1 hGbound
  · have h := norm_heatMildBUCValue_sub_le_rpow_of_le
      (E := E) (F := F) u₀ hG ha ht hr htr hM hα0 hα1 hGbound
    simpa [norm_sub_rev, abs_of_nonneg (sub_nonneg.mpr htr), abs_sub_comm] using h

/-- Every continuous bounded-forcing mild path is Hölder of each exponent
strictly below one on compact positive-time intervals.  The Hölder constant is
obtained from compactness of the forcing range. -/
theorem exists_positiveHolderConstant_heatMildBUCValue
    (u₀ : BUC) {G : ℝ → BUC} (hG : Continuous G)
    {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ r ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖heatMildBUCValue (E := E) (F := F) u₀ G t -
            heatMildBUCValue (E := E) (F := F) u₀ G r‖ ≤
          K * |t - r| ^ α := by
  have hb : 0 ≤ b := ha.le.trans hab
  obtain ⟨M, hMbound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  let M₀ : ℝ := max 0 M
  have hM₀ : 0 ≤ M₀ := le_max_left 0 M
  have hGbound : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G s‖ ≤ M₀ := by
    intro s hs
    exact (hMbound s hs).trans (le_max_right 0 M)
  let K₀ : ℝ := b ^ (1 - α) *
    ((heatKernelTimeDerivativeL1Norm (E := E) 1 / a) * ‖u₀‖ + M₀ +
      ((heatKernelTimeDerivativeL1Norm (E := E) 1 + 2) * M₀) / (1 - α))
  have hC : 0 ≤ heatKernelTimeDerivativeL1Norm (E := E) 1 :=
    heatKernelTimeDerivativeL1Norm_one_nonneg (E := E)
  have hdenom : 0 ≤ 1 - α := by linarith
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    apply mul_nonneg (Real.rpow_nonneg hb (1 - α))
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (div_nonneg hC ha.le) (norm_nonneg u₀)
      · exact hM₀
    · exact div_nonneg
        (mul_nonneg (add_nonneg hC (by norm_num)) hM₀) hdenom
  refine ⟨K₀, hK₀, ?_⟩
  intro r hr t ht
  exact norm_heatMildBUCValue_sub_le_rpow
    (E := E) (F := F) u₀ hG ha hM₀ hα0 hα1 hGbound r hr t ht

end Poincare
