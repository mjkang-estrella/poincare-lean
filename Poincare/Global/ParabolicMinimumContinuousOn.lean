import Poincare.Global.ScalarEvolution

/-!
# Parabolic minimum principles from slab continuity

The existing compact parabolic minimum principles assume continuity on all of
`\mathbb R \times M`, although their conclusions and differential hypotheses
only concern the closed slab `[0,T] \times M`.  This file proves the matching
slab-local forms.

The only extra device is the continuous retraction `projIcc 0 T`: it extends
the restriction of the evolving function continuously off the slab solely for
the purpose of proving continuity of the timewise spatial minimum.  All values,
derivatives, and Laplacian inequalities in the argument remain those of the
original function on `[0,T]`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Poincare

universe u

variable {M : Type u} [TopologicalSpace M]

omit [TopologicalSpace M] in
/-- The image defining the timewise infimum is unchanged by retracting a time
which already lies in the closed interval. -/
private theorem image_iccExtend_eq_of_mem
    {a b t : ℝ} (hab : a ≤ b) (u : ℝ → M → ℝ)
    (ht : t ∈ Set.Icc a b) :
    (fun x : M ↦ u (Set.projIcc a b hab t) x) '' (Set.univ : Set M) =
      u t '' (Set.univ : Set M) := by
  rw [Set.projIcc_of_mem hab ht]

/-- On a nonempty time interval, slab continuity makes the timewise spatial
infimum continuous on that interval. -/
theorem continuousOn_sInf_image_univ_of_continuousOn_slab
    [CompactSpace M] [Nonempty M]
    {u : ℝ → M → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn (Function.uncurry u)
      (Set.Icc a b ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun t ↦ sInf (u t '' (Set.univ : Set M)))
      (Set.Icc a b) := by
  let uIcc : Set.Icc a b → M → ℝ := fun t x ↦ u t x
  have huIcc : Continuous (Function.uncurry uIcc) := by
    have hpair : Continuous
        (fun p : Set.Icc a b × M ↦ ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    simpa [uIcc, Function.uncurry] using
      hu.comp_continuous hpair (fun p ↦ ⟨p.1.property, Set.mem_univ p.2⟩)
  let uExt : ℝ → M → ℝ := fun t x ↦ u (Set.projIcc a b hab t) x
  have huExt : Continuous (Function.uncurry uExt) := by
    have hpair : Continuous
        (fun p : ℝ × M ↦ (Set.projIcc a b hab p.1, p.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    simpa [uExt, uIcc, Function.uncurry] using huIcc.comp hpair
  let mExt : ℝ → ℝ := fun t ↦ sInf (uExt t '' (Set.univ : Set M))
  have hmExt : Continuous mExt := by
    exact (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sInf huExt
  apply hmExt.continuousOn.congr
  intro t ht
  dsimp only [mExt, uExt]
  rw [image_iccExtend_eq_of_mem hab u ht]

/-- Strict compact parabolic minimum principle assuming continuity only on the
closed time slab used by the argument. -/
theorem closed_parabolic_min_principle_strict_var_continuousOn
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T : ℝ}
    (hT0 : 0 ≤ T)
    (hu_cont : ContinuousOn (Function.uncurry u)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hud : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hsuper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x < u' t x)
    (hmin_lap : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 < u 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, 0 < u t x := by
  by_contra hviol
  push Not at hviol
  obtain ⟨t₁, ht₁, x₁, hux₁⟩ := hviol
  let m : ℝ → ℝ := fun t ↦ sInf (u t '' (Set.univ : Set M))
  have hmcont : ContinuousOn m (Set.Icc (0 : ℝ) T) := by
    exact continuousOn_sInf_image_univ_of_continuousOn_slab
      hT0 hu_cont
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (u t) := by
    intro t ht
    have hpair : Continuous (fun x : M ↦ (t, x)) :=
      continuous_const.prodMk continuous_id
    simpa [Function.uncurry] using
      hu_cont.comp_continuous hpair
        (fun x ↦ ⟨ht, Set.mem_univ x⟩)
  have hattain : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ x : M, IsMinOn (u t) Set.univ x ∧ m t = u t x := by
    intro t ht
    obtain ⟨x, hxK, hxmin⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
        (Set.univ_nonempty) (hslice t ht).continuousOn
    refine ⟨x, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le
        ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf
        ((Set.univ_nonempty : (Set.univ : Set M).Nonempty).image (u t))
        fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz
  have hmle : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, m t ≤ u t x := by
    intro t ht x
    exact csInf_le
      ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
        obtain ⟨x', hmin', hmx'⟩ := hattain t ht
        rw [← hzy, hmx']
        exact hmin' hz⟩
      ⟨x, trivial, rfl⟩
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, _, hmx⟩ := hattain 0 hzeroMem
    rw [hmx]
    exact h0 x
  have hmbad : ∃ t ∈ Set.Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ ht₁ x₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    RicciFlow.exists_first_zero hmcont hm0 hmbad
  have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀min, hmx₀⟩ := hattain t₀ ht₀Icc
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ t₀ ht₀Icc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀),
        s ∈ Set.Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push Not at hge
      have : u s x₀ / (s - t₀) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hge (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have hmles := hmle s
      ⟨le_of_lt hsIoo.1, le_of_lt (hsIoo.2.trans_le ht₀.2)⟩ x₀
    linarith
  have hsup := hsuper t₀ ht₀Icc x₀
  have hlap := hmin_lap t₀ ht₀Icc x₀ hx₀min
  rw [hux₀] at hsup
  simp only [mul_zero] at hsup
  linarith

/-- Non-strict compact parabolic comparison with continuity required only on
the closed slab `[0,T] × M`. -/
theorem closed_parabolic_min_principle_var_continuousOn
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T M₀ : ℝ}
    (hT0 : 0 ≤ T)
    (hcM : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, c t x ≤ M₀)
    (hu_cont : ContinuousOn (Function.uncurry u)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hud : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hlap_add_const : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y : M ↦ u t y + k) x = lap t (u t) x)
    (hsuper : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x ≤ u' t x)
    (hmin_lap : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 ≤ u 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, 0 ≤ u t x := by
  intro t ht x
  by_contra hneg
  push Not at hneg
  let M' : ℝ := max M₀ 0 + 1
  let epsilon : ℝ := -u t x / (2 * Real.exp (M' * t))
  have hexp : (0 : ℝ) < Real.exp (M' * t) := Real.exp_pos _
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    apply div_pos (by linarith) (by positivity)
  have hvpos := closed_parabolic_min_principle_strict_var_continuousOn
    (M := M) (lap := lap)
    (u := fun s y ↦ u s y + epsilon * Real.exp (M' * s))
    (u' := fun s y ↦ u' s y + epsilon * M' * Real.exp (M' * s))
    (c := c) (T := T) hT0
    (by
      apply ContinuousOn.add hu_cont
      exact ((continuous_const.mul
        ((continuous_const.mul continuous_fst).rexp)).comp
          continuous_id).continuousOn)
    (by
      intro y s hs
      have h1 := hud y s hs
      have h2 : HasDerivAt (fun r ↦ epsilon * Real.exp (M' * r))
          (epsilon * M' * Real.exp (M' * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M').exp).const_mul epsilon
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa using h1.add h2)
    (by
      intro s hs y
      have hsup := hsuper s hs y
      have hlap : lap s (fun z : M ↦ u s z +
          epsilon * Real.exp (M' * s)) y = lap s (u s) y :=
        hlap_add_const s hs (epsilon * Real.exp (M' * s)) y
      simp only
      rw [hlap]
      have hcy := hcM s hs y
      have hM1 : c s y < M' := by
        dsimp only [M']
        have : M₀ ≤ max M₀ 0 := le_max_left M₀ 0
        linarith
      have heps : 0 < epsilon * Real.exp (M' * s) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hM1 heps])
    (by
      intro s hs y hminv
      have hminu : IsMinOn (u s) Set.univ y := by
        intro z hz
        have := hminv hz
        simpa using this
      have hlapu := hmin_lap s hs y hminu
      rwa [hlap_add_const s hs (epsilon * Real.exp (M' * s)) y])
    (by
      intro y
      have := h0 y
      positivity)
  have := hvpos t ht x
  simp only at this
  dsimp only [epsilon] at this
  have hne : Real.exp (M' * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith

/-- Strict compact parabolic minimum principle with slab continuity and all
differential hypotheses restricted to strict positive time. -/
theorem closed_parabolic_min_principle_strict_var_Ioc_continuousOn
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T : ℝ}
    (hT0 : 0 ≤ T)
    (hu_cont : ContinuousOn (Function.uncurry u)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hud : ∀ x : M, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hsuper : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x < u' t x)
    (hmin_lap : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 < u 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, 0 < u t x := by
  by_contra hviol
  push Not at hviol
  obtain ⟨t₁, ht₁, x₁, hux₁⟩ := hviol
  let m : ℝ → ℝ := fun t ↦ sInf (u t '' (Set.univ : Set M))
  have hmcont : ContinuousOn m (Set.Icc (0 : ℝ) T) :=
    continuousOn_sInf_image_univ_of_continuousOn_slab hT0 hu_cont
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (u t) := by
    intro t ht
    have hpair : Continuous (fun x : M ↦ (t, x)) :=
      continuous_const.prodMk continuous_id
    simpa [Function.uncurry] using
      hu_cont.comp_continuous hpair
        (fun x ↦ ⟨ht, Set.mem_univ x⟩)
  have hattain : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ x : M, IsMinOn (u t) Set.univ x ∧ m t = u t x := by
    intro t ht
    obtain ⟨x, hxK, hxmin⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
        Set.univ_nonempty (hslice t ht).continuousOn
    refine ⟨x, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le
        ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf
        ((Set.univ_nonempty : (Set.univ : Set M).Nonempty).image (u t))
        fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz
  have hmle : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, m t ≤ u t x := by
    intro t ht x
    exact csInf_le
      ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
        obtain ⟨x', hmin', hmx'⟩ := hattain t ht
        rw [← hzy, hmx']
        exact hmin' hz⟩
      ⟨x, trivial, rfl⟩
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, _, hmx⟩ := hattain 0 hzeroMem
    rw [hmx]
    exact h0 x
  have hmbad : ∃ t ∈ Set.Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ ht₁ x₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    RicciFlow.exists_first_zero hmcont hm0 hmbad
  have ht₀Ioc : t₀ ∈ Set.Ioc (0 : ℝ) T := ⟨ht₀.1, ht₀.2⟩
  have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀.1.le, ht₀.2⟩
  obtain ⟨x₀, hx₀min, hmx₀⟩ := hattain t₀ ht₀Icc
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ t₀ ht₀Ioc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Set.Iio t₀),
        s ∈ Set.Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push Not at hge
      have : u s x₀ / (s - t₀) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hge (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have hmles := hmle s
      ⟨le_of_lt hsIoo.1, le_of_lt (hsIoo.2.trans_le ht₀.2)⟩ x₀
    linarith
  have hsup := hsuper t₀ ht₀Ioc x₀
  have hlap := hmin_lap t₀ ht₀Ioc x₀ hx₀min
  rw [hux₀] at hsup
  simp only [mul_zero] at hsup
  linarith

/-- Non-strict slab-local compact parabolic comparison whose differential
hypotheses start strictly after time zero. -/
theorem closed_parabolic_min_principle_var_Ioc_continuousOn
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T M₀ : ℝ}
    (hT0 : 0 ≤ T)
    (hcM : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M, c t x ≤ M₀)
    (hu_cont : ContinuousOn (Function.uncurry u)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hud : ∀ x : M, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hlap_add_const : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y : M ↦ u t y + k) x = lap t (u t) x)
    (hsuper : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x ≤ u' t x)
    (hmin_lap : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 ≤ u 0 x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, 0 ≤ u t x := by
  intro t ht x
  by_contra hneg
  push Not at hneg
  let M' : ℝ := max M₀ 0 + 1
  let epsilon : ℝ := -u t x / (2 * Real.exp (M' * t))
  have hexp : (0 : ℝ) < Real.exp (M' * t) := Real.exp_pos _
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    apply div_pos (by linarith) (by positivity)
  have hvpos := closed_parabolic_min_principle_strict_var_Ioc_continuousOn
    (M := M) (lap := lap)
    (u := fun s y ↦ u s y + epsilon * Real.exp (M' * s))
    (u' := fun s y ↦ u' s y + epsilon * M' * Real.exp (M' * s))
    (c := c) (T := T) hT0
    (by
      apply ContinuousOn.add hu_cont
      exact ((continuous_const.mul
        ((continuous_const.mul continuous_fst).rexp)).comp
          continuous_id).continuousOn)
    (by
      intro y s hs
      have h1 := hud y s hs
      have h2 : HasDerivAt (fun r ↦ epsilon * Real.exp (M' * r))
          (epsilon * M' * Real.exp (M' * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M').exp).const_mul epsilon
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa using h1.add h2)
    (by
      intro s hs y
      have hsup := hsuper s hs y
      have hlap : lap s (fun z : M ↦ u s z +
          epsilon * Real.exp (M' * s)) y = lap s (u s) y :=
        hlap_add_const s hs (epsilon * Real.exp (M' * s)) y
      simp only
      rw [hlap]
      have hcy := hcM s hs y
      have hM1 : c s y < M' := by
        dsimp only [M']
        have : M₀ ≤ max M₀ 0 := le_max_left M₀ 0
        linarith
      have heps : 0 < epsilon * Real.exp (M' * s) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hM1 heps])
    (by
      intro s hs y hminv
      have hminu : IsMinOn (u s) Set.univ y := by
        intro z hz
        have := hminv hz
        simpa using this
      have hlapu := hmin_lap s hs y hminu
      rwa [hlap_add_const s hs (epsilon * Real.exp (M' * s)) y])
    (by
      intro y
      have := h0 y
      positivity)
  have := hvpos t ht x
  simp only at this
  dsimp only [epsilon] at this
  have hne : Real.exp (M' * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith

end Poincare
