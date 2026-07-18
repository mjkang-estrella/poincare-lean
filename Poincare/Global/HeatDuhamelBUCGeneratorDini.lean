import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Dini regularity for heat Duhamel terms in `BUC`

Positive-time heat smoothing alone has the sharp operator bound
`‖A H_r‖ = O(r⁻¹)`.  Consequently, continuity of a time-dependent forcing
does not by itself put its Duhamel convolution in the strong generator
domain.  The exact endpoint condition is integrability of the cancellation

`A H_{t-s} (G(s) - G(t))`.

This file records that operator-Dini condition and proves the corresponding
strong-generator theorem.  The proof splits off the constant endpoint value,
whose convolution is an integrated heat orbit, and obtains the cancelling
remainder as a closed-graph limit of positive-time truncated integrals.
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

/-- The exact operator-Dini condition at a terminal time `t`.  The endpoint
value is subtracted before the singular positive-time generator is applied.
Since interval integrability is insensitive to the value at `s = t`, no
convention for the formal expression `A H₀` is required. -/
def HasBUCHeatGeneratorDiniControlAt (G : ℝ → BUC) (t : ℝ) : Prop :=
  IntervalIntegrable
    (fun s : ℝ ↦ vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
      (G s - G t)) volume 0 t

/-- Scalar Dini condition at `t`.  The inverse-time weight is exactly the
one dictated by the proved Gaussian estimate for `‖A H_r‖`. -/
def HasBUCScalarDiniControlAt (G : ℝ → BUC) (t : ℝ) : Prop :=
  IntervalIntegrable
    (fun s : ℝ ↦ (t - s)⁻¹ * ‖G s - G t‖) volume 0 t

/-- The scalar `ω(r)/r` condition implies the exact operator-Dini condition.
The only constant used is `‖∂ₜK₁‖_{L¹}` from
`norm_vectorHeatTimeDerivativeBUC_le_inv`. -/
theorem hasBUCHeatGeneratorDiniControlAt_of_scalar
    {G : ℝ → BUC} (hG : Continuous G) {t : ℝ} (ht : 0 < t)
    (hscalar : HasBUCScalarDiniControlAt G t) :
    HasBUCHeatGeneratorDiniControlAt (E := E) (F := F) G t := by
  let Aq : ℝ → BUC := fun s ↦
    vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
      (G s - G t)
  have hAcont : ContinuousOn Aq (Set.Iio t) := by
    have hjoint := continuousOn_vectorHeatTimeDerivativeBUC_prod_Ioi
      (E := E) (F := F)
    have hmap : Continuous (fun s : ℝ ↦ (t - s, G s - G t)) :=
      (continuous_const.sub continuous_id).prodMk
        (hG.sub continuous_const)
    apply hjoint.comp hmap.continuousOn
    intro s hs
    constructor
    · change 0 < t - s
      exact sub_pos.mpr hs
    · exact Set.mem_univ _
  have hAmeas : AEStronglyMeasurable Aq (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [Set.uIoc_of_le ht.le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hAcont.mono fun _ hs ↦ hs.2).aestronglyMeasurable measurableSet_Ioo
  let C : ℝ := heatKernelTimeDerivativeL1Norm (E := E) 1
  have hbound : IntervalIntegrable
      (fun s : ℝ ↦ C * ((t - s)⁻¹ * ‖G s - G t‖)) volume 0 t := by
    simpa only [HasBUCScalarDiniControlAt, C] using
      hscalar.const_mul (heatKernelTimeDerivativeL1Norm (E := E) 1)
  apply hbound.mono_fun' hAmeas
  rw [Set.uIoc_of_le ht.le,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
  have hts : 0 < t - s := sub_pos.mpr hs.2
  simpa only [Aq, C, div_eq_mul_inv, mul_assoc] using
    norm_vectorHeatTimeDerivativeBUC_le_inv
      (E := E) (F := F) hts (G s - G t)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- A positive Hölder modulus at the terminal endpoint implies the scalar
Dini condition.  This is stated with an explicit pointwise power bound, so it
does not hide a choice of Hölder seminorm convention. -/
theorem hasBUCScalarDiniControlAt_of_holder
    {G : ℝ → BUC} (hG : Continuous G) {t K α : ℝ}
    (ht : 0 < t) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖G s - G t‖ ≤ K * |t - s| ^ α) :
    HasBUCScalarDiniControlAt G t := by
  let g : ℝ → ℝ := fun s ↦ (t - s)⁻¹ * ‖G s - G t‖
  have hgcont : ContinuousOn g (Set.Iio t) := by
    have hden : ContinuousOn (fun s : ℝ ↦ t - s) (Set.Iio t) :=
      (continuous_const.sub continuous_id).continuousOn
    have hinv : ContinuousOn (fun s : ℝ ↦ (t - s)⁻¹) (Set.Iio t) :=
      hden.inv₀ fun s hs ↦ (sub_ne_zero.mpr hs.ne')
    exact hinv.mul (hG.sub continuous_const).norm.continuousOn
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [Set.uIoc_of_le ht.le,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hgcont.mono fun _ hs ↦ hs.2).aestronglyMeasurable measurableSet_Ioo
  have hpowOn : IntegrableOn (fun r : ℝ ↦ r ^ (α - 1))
      (Set.Ioo (0 : ℝ) t) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ht).2 (by linarith)
  have hpow : IntervalIntegrable (fun r : ℝ ↦ r ^ (α - 1))
      volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).2 hpowOn
  have hpowSub : IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ (α - 1))
      volume 0 t := by
    simpa only [sub_zero, sub_self] using (hpow.comp_sub_left t).symm
  have hmajorant : IntervalIntegrable
      (fun s : ℝ ↦ |K| * (t - s) ^ (α - 1)) volume 0 t :=
    hpowSub.const_mul |K|
  change IntervalIntegrable g volume 0 t
  apply hmajorant.mono_fun' hgmeas
  rw [Set.uIoc_of_le ht.le,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with s hs
  have hts : 0 < t - s := sub_pos.mpr hs.2
  have hmod := hholder s ⟨hs.1.le, hs.2.le⟩
  rw [abs_of_pos hts] at hmod
  calc
    ‖g s‖ = (t - s)⁻¹ * ‖G s - G t‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (inv_nonneg.mpr hts.le) (norm_nonneg _))]
    _ ≤ (t - s)⁻¹ * (K * (t - s) ^ α) :=
      mul_le_mul_of_nonneg_left hmod (inv_nonneg.mpr hts.le)
    _ = |K| * (t - s) ^ (α - 1) := by
      rw [abs_of_nonneg hK]
      rw [Real.rpow_sub_one hts.ne' α]
      field_simp [hts.ne']

/-- The generator value selected by the operator-Dini condition. -/
def heatDuhamelBUCGeneratorValue (G : ℝ → BUC) (t : ℝ) : BUC :=
  vectorHeatSemigroupBUCExtended (E := E) (F := F) t (G t) - G t +
    ∫ s : ℝ in (0 : ℝ)..t,
      vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
        (G s - G t)

/-- Interval integration preserves the closed strong-generator graph when
both components are interval integrable and the pointwise graph relation
holds throughout the unoriented interval. -/
theorem intervalIntegral_mem_bucHeatGeneratorGraph
    {u Au : ℝ → BUC} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hAu : IntervalIntegrable Au volume a b)
    (hgraph : ∀ s ∈ Set.uIcc a b,
      IsInBUCHeatGeneratorDomain (E := E) (F := F) (u s) (Au s)) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in a..b, u s) (∫ s : ℝ in a..b, Au s) := by
  apply isInBUCHeatGeneratorDomain_of_integral_semigroup_eq_sub
    (E := E) (F := F)
  intro τ hτ
  let ε : ℝ≥0 := ⟨τ, hτ⟩
  let J : BUC →L[ℝ] BUC :=
    integratedHeatOrbitBUCCLM (E := E) (F := F) ε
  let Hτ : BUC →L[ℝ] BUC :=
    vectorHeatSemigroupBUCExtended (E := E) (F := F) τ
  change integratedHeatOrbitBUC (E := E) (F := F) ε
      (∫ s : ℝ in a..b, Au s) =
    Hτ (∫ s : ℝ in a..b, u s) - ∫ s : ℝ in a..b, u s
  rw [← integratedHeatOrbitBUCCLM_apply (E := E) (F := F)]
  calc
    J (∫ s : ℝ in a..b, Au s) =
        ∫ s : ℝ in a..b, J (Au s) :=
      (J.intervalIntegral_comp_comm hAu).symm
    _ = ∫ s : ℝ in a..b, (Hτ (u s) - u s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have h := (hgraph s hs).integral_semigroup_eq_sub hτ
      simpa [J, Hτ, ε, integratedHeatOrbitBUCCLM_apply,
        integratedHeatOrbitBUC] using h
    _ = (∫ s : ℝ in a..b, Hτ (u s)) - ∫ s : ℝ in a..b, u s := by
      have hHu : IntervalIntegrable (fun s : ℝ ↦ Hτ (u s)) volume a b :=
        ⟨by simpa [Function.comp_def] using Hτ.integrableOn_comp hu.1,
         by simpa [Function.comp_def] using Hτ.integrableOn_comp hu.2⟩
      exact intervalIntegral.integral_sub hHu hu
    _ = Hτ (∫ s : ℝ in a..b, u s) - ∫ s : ℝ in a..b, u s := by
      rw [Hτ.intervalIntegral_comp_comm hu]

/-- The cancelling Duhamel remainder belongs to the strong generator graph.
The proof takes terminal cutoffs `c ↑ t`; the state and proposed generator
both converge by continuity of interval primitives, and the generator graph
is closed. -/
theorem heatDuhamelBUCResidual_mem_heatGeneratorDomain_of_dini
    {G : ℝ → BUC} (hG : Continuous G) {t : ℝ} (ht : 0 < t)
    (hDini : HasBUCHeatGeneratorDiniControlAt
      (E := E) (F := F) G t) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
          (G s - G t))
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
          (G s - G t)) := by
  let q : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
      (G s - G t)
  let Aq : ℝ → BUC := fun s ↦
    vectorHeatTimeDerivativeBUC (E := E) (F := F) (t - s)
      (G s - G t)
  have hqcont : Continuous q := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hG.sub continuous_const
  have hqint : IntervalIntegrable q volume 0 t :=
    hqcont.intervalIntegrable _ _
  have hAqint : IntervalIntegrable Aq volume 0 t := by
    simpa only [HasBUCHeatGeneratorDiniControlAt, Aq] using hDini
  let P : ℝ → BUC × BUC := fun c ↦
    ((∫ s : ℝ in (0 : ℝ)..c, q s), ∫ s : ℝ in (0 : ℝ)..c, Aq s)
  have hleft : Tendsto (fun c : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..c, q s)
      (𝓝[<] t) (𝓝 (∫ s : ℝ in (0 : ℝ)..t, q s)) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval'
      hqint (a := (0 : ℝ)) Set.left_mem_uIcc
    exact (hcont t Set.right_mem_uIcc).mono_left
      (nhdsWithin_le_iff.mpr (by
        simpa [Set.uIcc_of_le ht.le] using Icc_mem_nhdsLT ht))
  have hright : Tendsto (fun c : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..c, Aq s)
      (𝓝[<] t) (𝓝 (∫ s : ℝ in (0 : ℝ)..t, Aq s)) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval'
      hAqint (a := (0 : ℝ)) Set.left_mem_uIcc
    exact (hcont t Set.right_mem_uIcc).mono_left
      (nhdsWithin_le_iff.mpr (by
        simpa [Set.uIcc_of_le ht.le] using Icc_mem_nhdsLT ht))
  have hP : Tendsto P (𝓝[<] t)
      (𝓝 ((∫ s : ℝ in (0 : ℝ)..t, q s),
        ∫ s : ℝ in (0 : ℝ)..t, Aq s)) := by
    exact hleft.prodMk_nhds hright
  have hPgraph : ∀ᶠ c : ℝ in 𝓝[<] t,
      P c ∈ bucHeatGeneratorGraph (E := E) (F := F) := by
    filter_upwards [Icc_mem_nhdsLT ht, self_mem_nhdsWithin] with c hc hct
    have hsub : Set.uIcc (0 : ℝ) c ⊆ Set.uIcc (0 : ℝ) t := by
      simpa [Set.uIcc_of_le hc.1, Set.uIcc_of_le ht.le] using
        (Set.Icc_subset_Icc le_rfl hc.2)
    have hqc : IntervalIntegrable q volume 0 c := hqint.mono_set hsub
    have hAqc : IntervalIntegrable Aq volume 0 c := hAqint.mono_set hsub
    change IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in (0 : ℝ)..c, q s) (∫ s : ℝ in (0 : ℝ)..c, Aq s)
    apply intervalIntegral_mem_bucHeatGeneratorGraph
      (E := E) (F := F) hqc hAqc
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) c := by
      simpa [Set.uIcc_of_le hc.1] using hs
    have hts : 0 < t - s := sub_pos.mpr (hsIcc.2.trans_lt hct)
    exact vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) hts (G s - G t)
  have hclosed := isClosed_bucHeatGeneratorGraph (E := E) (F := F)
  have hlimit := hclosed.mem_of_tendsto hP hPgraph
  simpa only [q, Aq, bucHeatGeneratorGraph] using hlimit

/-- A continuous forcing satisfying the exact endpoint operator-Dini
condition has a positive-time Duhamel value in the strong heat-generator
domain, with the displayed generator value. -/
theorem heatDuhamelBUC_mem_heatGeneratorDomain_of_dini
    {G : ℝ → BUC} (hG : Continuous G) {t : ℝ} (ht : 0 < t)
    (hDini : HasBUCHeatGeneratorDiniControlAt
      (E := E) (F := F) G t) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s))
      (heatDuhamelBUCGeneratorValue (E := E) (F := F) G t) := by
  let ε : ℝ≥0 := ⟨t, ht.le⟩
  let q : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
      (G s - G t)
  let q₀ : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G t)
  have hqcont : Continuous q := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hG.sub continuous_const
  have hq₀cont : Continuous q₀ := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact continuous_const
  have hqint : IntervalIntegrable q volume 0 t :=
    hqcont.intervalIntegrable _ _
  have hq₀int : IntervalIntegrable q₀ volume 0 t :=
    hq₀cont.intervalIntegrable _ _
  have hq₀eq : (∫ s : ℝ in (0 : ℝ)..t, q₀ s) =
      integratedHeatOrbitBUC (E := E) (F := F) ε (G t) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t)
      (fun r : ℝ ↦ vectorHeatSemigroupBUCExtended
        (E := E) (F := F) r (G t)) t
    simpa [q₀, integratedHeatOrbitBUC, ε] using hchange
  have hsplit :
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s)) =
      integratedHeatOrbitBUC (E := E) (F := F) ε (G t) +
        ∫ s : ℝ in (0 : ℝ)..t, q s := by
    calc
      (∫ s : ℝ in (0 : ℝ)..t,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s)) =
          ∫ s : ℝ in (0 : ℝ)..t, (q₀ s + q s) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        dsimp [q, q₀]
        rw [← (vectorHeatSemigroupBUCExtended
          (E := E) (F := F) (t - s)).map_add]
        simp
      _ = (∫ s : ℝ in (0 : ℝ)..t, q₀ s) +
          ∫ s : ℝ in (0 : ℝ)..t, q s :=
        intervalIntegral.integral_add hq₀int hqint
      _ = integratedHeatOrbitBUC (E := E) (F := F) ε (G t) +
          ∫ s : ℝ in (0 : ℝ)..t, q s := by rw [hq₀eq]
  have hbase := integratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε (G t)
  have hres := heatDuhamelBUCResidual_mem_heatGeneratorDomain_of_dini
    (E := E) (F := F) hG ht hDini
  rw [hsplit]
  simpa only [heatDuhamelBUCGeneratorValue, q,
    IsInBUCHeatGeneratorDomain, map_add] using hbase.add hres

/-- Scalar-Dini version of positive-time Duhamel generator membership. -/
theorem heatDuhamelBUC_mem_heatGeneratorDomain_of_scalarDini
    {G : ℝ → BUC} (hG : Continuous G) {t : ℝ} (ht : 0 < t)
    (hscalar : HasBUCScalarDiniControlAt G t) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s))
      (heatDuhamelBUCGeneratorValue (E := E) (F := F) G t) := by
  apply heatDuhamelBUC_mem_heatGeneratorDomain_of_dini
    (E := E) (F := F) hG ht
  exact hasBUCHeatGeneratorDiniControlAt_of_scalar
    (E := E) (F := F) hG ht hscalar

/-- Explicit locally Hölder endpoint criterion for positive-time Duhamel
generator membership. -/
theorem heatDuhamelBUC_mem_heatGeneratorDomain_of_holder
    {G : ℝ → BUC} (hG : Continuous G) {t K α : ℝ}
    (ht : 0 < t) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖G s - G t‖ ≤ K * |t - s| ^ α) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s) (G s))
      (heatDuhamelBUCGeneratorValue (E := E) (F := F) G t) := by
  apply heatDuhamelBUC_mem_heatGeneratorDomain_of_scalarDini
    (E := E) (F := F) hG ht
  exact hasBUCScalarDiniControlAt_of_holder hG ht hK hα hholder

end Poincare
