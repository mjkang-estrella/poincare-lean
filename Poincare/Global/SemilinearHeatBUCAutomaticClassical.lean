import Poincare.Global.HeatMildBUCPositiveHolder
import Poincare.Global.SemilinearHeatBUCHolderClassical

/-!
# Automatic positive-time classicality for semilinear heat mild paths

An arbitrary `BUC` initial datum need not have a power-rate heat orbit at time
zero.  This file therefore never asserts Hölder regularity on all of `[0,b]`.
Instead, fix `0 < c < a ≤ b`.  The mild path is Hölder on `[c,b]`; a
nonlinearity that is Lipschitz on the range of that path preserves this
estimate.  For an endpoint `t ∈ [a,b]`, the remaining early times `s < c` are
separated from `t` by the positive gap `a-c`, so compact boundedness supplies
the required endpoint estimate.

This is exactly the one-sided-in-time Hölder premise consumed by the Duhamel
generator construction and yields an ordinary derivative at every time in
`(a,b)`.
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

/-- A semilinear fixed point is the abstract mild path introduced in
`HeatMildBUCPositiveHolder`, with its projected forcing. -/
theorem semilinearHeatBUCFixedPoint_eq_heatMildBUCValue
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
    u (Set.projIcc 0 (T : ℝ) T.property t) =
      heatMildBUCValue (E := E) (F := F) u₀
        (semilinearHeatBUCProjectedForcing T N u) t := by
  let τ : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, ht⟩
  have hproj : Set.projIcc 0 (T : ℝ) T.property t = τ :=
    Set.projIcc_of_mem T.property ht
  have hmild := congrArg (fun w : DuhamelPath T BUC ↦ w τ) hu
  rw [hproj]
  simpa only [τ, semilinearHeatBUCPicard_apply,
    heatMildBUCValue, heatDuhamelBUCValue,
    semilinearHeatBUCProjectedForcing] using hmild.symm

/-- Lipschitz control of the nonlinearity on the mild-path range produces the
uniform endpoint Hölder estimate needed on every positive target window.

No estimate between two arbitrary times near zero is claimed. -/
theorem exists_endpointHolderConstant_semilinearHeatBUCProjectedForcing
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (L : ℝ≥0) (hNLipschitz : LipschitzOnWith L N (Set.range u))
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖semilinearHeatBUCProjectedForcing T N u s -
            semilinearHeatBUCProjectedForcing T N u t‖ ≤
          K * |t - s| ^ α := by
  let G : ℝ → BUC := semilinearHeatBUCProjectedForcing T N u
  have hG : Continuous G := by
    exact continuous_semilinearHeatBUCProjectedForcing T N hN u
  have hcb : c ≤ b := hca.le.trans hab
  obtain ⟨Kpath, hKpath, hpath⟩ :=
    exists_positiveHolderConstant_heatMildBUCValue
      (E := E) (F := F) u₀ hG hc hcb hα0 hα1
  obtain ⟨M, hMbound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  let M₀ : ℝ := max 0 M
  have hM₀ : 0 ≤ M₀ := le_max_left 0 M
  have hGbound : ∀ s ∈ Set.Icc (0 : ℝ) b, ‖G s‖ ≤ M₀ := by
    intro s hs
    exact (hMbound s hs).trans (le_max_right 0 M)
  let δ : ℝ := a - c
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact sub_pos.mpr hca
  have hδpow : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  let Knear : ℝ := (L : ℝ) * Kpath
  let Kfar : ℝ := (2 * M₀) / δ ^ α
  let K : ℝ := max Knear Kfar
  have hKnear : 0 ≤ Knear := by
    exact mul_nonneg (NNReal.coe_nonneg L) hKpath
  have hKfar : 0 ≤ Kfar := by
    exact div_nonneg (mul_nonneg (by norm_num) hM₀) hδpow.le
  have hK : 0 ≤ K := hKnear.trans (le_max_left Knear Kfar)
  refine ⟨K, hK, ?_⟩
  intro t ht s hs
  have htcb : t ∈ Set.Icc c b := ⟨hca.le.trans ht.1, ht.2⟩
  have ht0T : t ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨hc.le.trans htcb.1, ht.2.trans hbT⟩
  by_cases hcs : c ≤ s
  · have hscb : s ∈ Set.Icc c b :=
      ⟨hcs, hs.2.trans ht.2⟩
    have hs0T : s ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨hc.le.trans hscb.1, hscb.2.trans hbT⟩
    have hpathBound := hpath s hscb t htcb
    have hstateS := semilinearHeatBUCFixedPoint_eq_heatMildBUCValue
      (E := E) (F := F) T u₀ N hN u hu hs0T
    have hstateT := semilinearHeatBUCFixedPoint_eq_heatMildBUCValue
      (E := E) (F := F) T u₀ N hN u hu ht0T
    have hpathBound' :
        ‖u (Set.projIcc 0 (T : ℝ) T.property s) -
            u (Set.projIcc 0 (T : ℝ) T.property t)‖ ≤
          Kpath * |t - s| ^ α := by
      rw [hstateS, hstateT]
      simpa only [G, norm_sub_rev] using hpathBound
    have hLip := hNLipschitz.dist_le_mul
      (u (Set.projIcc 0 (T : ℝ) T.property s))
      ⟨Set.projIcc 0 (T : ℝ) T.property s, rfl⟩
      (u (Set.projIcc 0 (T : ℝ) T.property t))
      ⟨Set.projIcc 0 (T : ℝ) T.property t, rfl⟩
    have hforce : ‖G s - G t‖ ≤
        (L : ℝ) *
          ‖u (Set.projIcc 0 (T : ℝ) T.property s) -
            u (Set.projIcc 0 (T : ℝ) T.property t)‖ := by
      simpa only [G, semilinearHeatBUCProjectedForcing, dist_eq_norm] using hLip
    calc
      ‖semilinearHeatBUCProjectedForcing T N u s -
          semilinearHeatBUCProjectedForcing T N u t‖ = ‖G s - G t‖ := rfl
      _ ≤ (L : ℝ) *
          ‖u (Set.projIcc 0 (T : ℝ) T.property s) -
            u (Set.projIcc 0 (T : ℝ) T.property t)‖ := hforce
      _ ≤ (L : ℝ) * (Kpath * |t - s| ^ α) :=
        mul_le_mul_of_nonneg_left hpathBound' (NNReal.coe_nonneg L)
      _ = Knear * |t - s| ^ α := by
        dsimp only [Knear]
        ring
      _ ≤ K * |t - s| ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left Knear Kfar)
          (Real.rpow_nonneg (abs_nonneg _) α)
  · have hsc : s < c := lt_of_not_ge hcs
    have hgap : δ ≤ t - s := by
      dsimp only [δ]
      linarith [ht.1]
    have hgapNonneg : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hpowGap : δ ^ α ≤ |t - s| ^ α := by
      rw [abs_of_nonneg hgapNonneg]
      exact Real.rpow_le_rpow hδ.le hgap hα0.le
    have hs0b : s ∈ Set.Icc (0 : ℝ) b :=
      ⟨hs.1, hs.2.trans ht.2⟩
    have ht0b : t ∈ Set.Icc (0 : ℝ) b :=
      ⟨hc.le.trans htcb.1, ht.2⟩
    have hforceBound : ‖G s - G t‖ ≤ 2 * M₀ := by
      calc
        ‖G s - G t‖ ≤ ‖G s‖ + ‖G t‖ := norm_sub_le _ _
        _ ≤ M₀ + M₀ := add_le_add (hGbound s hs0b) (hGbound t ht0b)
        _ = 2 * M₀ := by ring
    calc
      ‖semilinearHeatBUCProjectedForcing T N u s -
          semilinearHeatBUCProjectedForcing T N u t‖ = ‖G s - G t‖ := rfl
      _ ≤ 2 * M₀ := hforceBound
      _ = Kfar * δ ^ α := by
        dsimp only [Kfar]
        exact (div_mul_cancel₀ (2 * M₀) hδpow.ne').symm
      _ ≤ Kfar * |t - s| ^ α :=
        mul_le_mul_of_nonneg_left hpowGap hKfar
      _ ≤ K * |t - s| ^ α :=
        mul_le_mul_of_nonneg_right (le_max_right Knear Kfar)
          (Real.rpow_nonneg (abs_nonneg _) α)

/-- Every semilinear mild fixed point whose nonlinearity is Lipschitz on the
path range is an ordinary classical solution at all positive interior times.
The auxiliary cutoff `c` is strictly positive and strictly earlier than the
target window, so no endpoint-zero regularity is assumed. -/
theorem semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitzOn_range
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (L : ℝ≥0) (hNLipschitz : LipschitzOnWith L N (Set.range u))
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) T u₀ N u t +
          semilinearHeatBUCProjectedForcing T N u t) t := by
  obtain ⟨K, hK, hholder⟩ :=
    exists_endpointHolderConstant_semilinearHeatBUCProjectedForcing
      (E := E) (F := F) T u₀ N hN u hu L hNLipschitz
      hc hca hab hbT hα0 hα1
  exact semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_uniformHolder_forcing
    (E := E) (F := F) T u₀ N hN u hu
    (ha := hc.trans hca) (hab := hab) (hbT := hbT)
    (hK := hK) (hα := hα0) hholder

/-- Global Lipschitz control is a convenient sufficient condition for the
range-local premise of automatic positive-time classicality. -/
theorem semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitz
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (L : ℝ≥0)
    (hN : LipschitzWith L N) (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN.continuous u = u)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) T u₀ N u t +
          semilinearHeatBUCProjectedForcing T N u t) t := by
  exact semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitzOn_range
    (E := E) (F := F) T u₀ N hN.continuous u hu L
    hN.lipschitzOnWith hc hca hab hbT hα0 hα1

/-- The canonical contraction-constructed semilinear heat solution is
classical at every positive interior time. -/
theorem semilinearHeatBUCSolution_hasDerivAt_interior
    (T L : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (hN : LipschitzWith L N) (hsmall : T * L < 1)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ semilinearHeatBUCSolution T L u₀ N hN hsmall
          (Set.projIcc 0 (T : ℝ) T.property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) T u₀ N
            (semilinearHeatBUCSolution T L u₀ N hN hsmall) t +
          semilinearHeatBUCProjectedForcing T N
            (semilinearHeatBUCSolution T L u₀ N hN hsmall) t) t := by
  exact semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_lipschitz
    (E := E) (F := F) T u₀ N L hN
    (semilinearHeatBUCSolution T L u₀ N hN hsmall)
    (semilinearHeatBUCSolution_isFixedPt
      (E := E) (F := F) T L u₀ N hN hsmall)
    hc hca hab hbT hα0 hα1

end Poincare
