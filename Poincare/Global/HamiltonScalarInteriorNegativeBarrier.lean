import Poincare.Global.HamiltonScalarNegativeBarrier
import Poincare.Global.ParabolicMinimumContinuousOn

/-!
# Hamilton's scalar barrier from strict positive-time evolution

The reconstructed Ricci--DeTurck path naturally supplies a one-sided equation
at its initial endpoint and a genuine two-sided Hamilton scalar equation only
at strict positive times.  This file records the matching parabolic comparison:
the time derivative and supersolution hypotheses are required on `Ioc 0 T`,
while continuity and the initial lower bound propagate the conclusion across
the omitted left endpoint.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

omit [T2Space M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] in
/-- Strict compact parabolic minimum principle whose differential hypotheses
start strictly after time zero.  In the first-zero argument, strict positivity
of the initial slice forces the first zero to occur in `Ioc 0 T`, so no
two-sided derivative at the initial endpoint is used. -/
theorem closed_parabolic_min_principle_strict_var_Ioc
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T : ℝ}
    (hu_cont : Continuous ↿ u)
    (hud : ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hsuper : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x < u' t x)
    (hmin_lap : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 < u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, 0 < u t x := by
  by_contra hviol
  push Not at hviol
  obtain ⟨t₁, ht₁, x₁, hux₁⟩ := hviol
  set m : ℝ → ℝ := fun t ↦ sInf (u t '' (Set.univ : Set M)) with hm
  have hmcont : Continuous m :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sInf hu_cont
  have hattain : ∀ t, ∃ x : M, IsMinOn (u t) Set.univ x ∧ m t = u t x := by
    intro t
    obtain ⟨x, hxK, hxmin⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
        (Set.univ_nonempty)
        ((hu_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine ⟨x, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le
        ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf
        ((Set.univ_nonempty : (Set.univ : Set M).Nonempty).image (u t))
        fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz
  have hmle : ∀ t (x : M), m t ≤ u t x := by
    intro t x
    exact csInf_le
      ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
        obtain ⟨x', hmin', hmx'⟩ := hattain t
        rw [← hzy, hmx']
        exact hmin' hz⟩
      ⟨x, trivial, rfl⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, _, hmx⟩ := hattain 0
    rw [hmx]
    exact h0 x
  have hmbad : ∃ t ∈ Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ x₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    RicciFlow.exists_first_zero (hmcont.continuousOn) hm0 hmbad
  have ht₀Ioc : t₀ ∈ Ioc (0 : ℝ) T := ⟨ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀min, hmx₀⟩ := hattain t₀
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ t₀ ht₀Ioc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Iio t₀), s ∈ Ioo (0 : ℝ) t₀ :=
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
    have := hmle s x₀
    linarith
  have hsup := hsuper t₀ ht₀Ioc x₀
  have hlap := hmin_lap t₀ ht₀Ioc x₀ hx₀min
  rw [hux₀] at hsup
  simp only [mul_zero] at hsup
  linarith

omit [T2Space M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] in
/-- Non-strict compact parabolic comparison with all differential hypotheses
restricted to strict positive time. -/
theorem closed_parabolic_min_principle_var_Ioc
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T M₀ : ℝ}
    (hcM : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M, c t x ≤ M₀)
    (hu_cont : Continuous ↿ u)
    (hud : ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hlap_add_const : ∀ t ∈ Ioc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y : M ↦ u t y + k) x = lap t (u t) x)
    (hsuper : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x ≤ u' t x)
    (hmin_lap : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 ≤ u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, 0 ≤ u t x := by
  intro t ht x
  by_contra hneg
  push Not at hneg
  set M' : ℝ := max M₀ 0 + 1 with hM'
  set ε : ℝ := -u t x / (2 * Real.exp (M' * t)) with hε
  have hexp : (0 : ℝ) < Real.exp (M' * t) := Real.exp_pos _
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by positivity)
  have hvpos := closed_parabolic_min_principle_strict_var_Ioc
    (lap := lap)
    (u := fun s y ↦ u s y + ε * Real.exp (M' * s))
    (u' := fun s y ↦ u' s y + ε * M' * Real.exp (M' * s))
    (c := c) (T := T)
    (by
      apply Continuous.add hu_cont
      exact (continuous_const.mul ((continuous_const.mul
        continuous_fst).rexp)).comp continuous_id)
    (by
      intro y s hs
      have h1 := hud y s hs
      have h2 : HasDerivAt (fun r ↦ ε * Real.exp (M' * r))
          (ε * M' * Real.exp (M' * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M').exp).const_mul ε
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa using h1.add h2)
    (by
      intro s hs y
      have hsup := hsuper s hs y
      have hlap : lap s (fun z : M ↦ u s z + ε * Real.exp (M' * s)) y =
          lap s (u s) y :=
        hlap_add_const s hs (ε * Real.exp (M' * s)) y
      simp only
      rw [hlap]
      have hcy := hcM s hs y
      have hM1 : c s y < M' := by
        rw [hM']
        have : M₀ ≤ max M₀ 0 := le_max_left M₀ 0
        linarith
      have heps : 0 < ε * Real.exp (M' * s) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hM1 heps])
    (by
      intro s hs y hminv
      have hminu : IsMinOn (u s) Set.univ y := by
        intro z hz
        have := hminv hz
        simpa using this
      have hlapu := hmin_lap s hs y hminu
      rwa [hlap_add_const s hs (ε * Real.exp (M' * s)) y])
    (by
      intro y
      have := h0 y
      positivity)
  have := hvpos t ht x
  simp only at this
  rw [hε] at this
  have hne : Real.exp (M' * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith

/-- Hamilton's three-dimensional negative scalar barrier assuming the scalar
evolution equation only at strict positive times relative to the initial
slice. -/
theorem hamilton_scalar_negative_lower_bound_Ioc_continuousOn
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ T c B : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : c < 0) (hT0 : 0 ≤ T)
    (hR_cont : ContinuousOn
      (fun p : ℝ × M ↦ (gt (t₀ + p.1)).scalarAt p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hHam : ∀ τ ∈ Ioc (0 : ℝ) T, ∀ x : M,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x)
    (hScalar₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x)
    (hRB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).scalarAt x ≤ B)
    (h0 : c ≤ scalarMinimumTrack gt t₀ 0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      c / (1 - ((2 : ℝ) / 3) * c * τ) ≤
        (gt (t₀ + τ)).scalarAt x := by
  let a : ℝ := 2 / 3
  let R : ℝ → M → ℝ := fun τ x ↦ (gt (t₀ + τ)).scalarAt x
  let R' : ℝ → M → ℝ := fun τ x ↦
    (gt (t₀ + τ)).laplacianAt (R τ) x +
      2 * (gt (t₀ + τ)).ricciNormSqAt x
  have ha : 0 < a := by norm_num [a]
  have hRd : ∀ x : M, ∀ τ ∈ Ioc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' τ x) τ := by
    intro x τ hτ
    have hbase :
        HasDerivAt (fun t ↦ (gt t).scalarAt x) (R' τ x) (t₀ + τ) := by
      simpa [SatisfiesHamiltonScalarEvolutionAt, R, R'] using hHam τ hτ x
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [R] using hbase.comp τ hshift
  have hevol : ∀ τ ∈ Ioc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤
        R' τ x := by
    intro τ hτ x
    have hreact := hamilton_scalar_reaction_bound_at
      (g := gt (t₀ + τ)) (x := x) (show 0 < (3 : ℝ) by norm_num)
    dsimp [a, R, R']
    linarith
  have hscalar0 : ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).scalarAt y) x := by
    intro x
    simpa using hScalar₂ 0 ⟨le_refl 0, hT0⟩ x
  have h0point : ∀ x : M, c ≤ R 0 x := by
    intro x
    have hminle := scalarMinimumAt_le_scalarAt (g := gt t₀) hscalar0 x
    exact le_trans h0
      (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
  let φ : ℝ → ℝ := fun t ↦ c / max (1 - a * c * t) (1 / 2 : ℝ)
  have hden_one : ∀ t ∈ Icc (0 : ℝ) T, 1 ≤ 1 - a * c * t := by
    intro t ht
    have hac : a * c < 0 := mul_neg_of_pos_of_neg ha hc
    have : a * c * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hac) ht.1
    linarith
  have hφeq : ∀ t ∈ Icc (0 : ℝ) T,
      φ t = c / (1 - a * c * t) := by
    intro t ht
    simp only [φ]
    congr 1
    apply max_eq_left
    have hone := hden_one t ht
    norm_num at hone ⊢
    linarith
  have hden : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 - a * c * t := by
    intro t ht
    linarith [hden_one t ht]
  have hφd : ∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivAt φ (a * (φ t) ^ 2) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    have hd := hden t ht'
    have hf : HasDerivAt (fun s ↦ 1 - a * c * s) (-(a * c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (a * c)).const_sub 1
    have hinv : HasDerivAt (fun s ↦ (1 - a * c * s)⁻¹)
        (a * c / (1 - a * c * t) ^ 2) t := by
      have h2 := hf.inv (ne_of_gt hd)
      convert h2 using 1
      field_simp
    have hexact := hinv.const_mul c
    have hopen : ∀ᶠ s in nhds t,
        φ s = c * (1 - a * c * s)⁻¹ := by
      have hcont : Continuous (fun s ↦ 1 - a * c * s) := by continuity
      have hhalf : (1 / 2 : ℝ) < 1 - a * c * t := by
        have hhalf_one : (1 / 2 : ℝ) < 1 := by norm_num
        exact hhalf_one.trans_le (hden_one t ht')
      have hev : ∀ᶠ s in nhds t, (1 / 2 : ℝ) < 1 - a * c * s :=
        hcont.continuousAt.eventually_const_lt hhalf
      filter_upwards [hev] with s hs
      simp only [φ]
      rw [max_eq_left (le_of_lt hs), div_eq_mul_inv]
    have hres : HasDerivAt φ
        (c * (a * c / (1 - a * c * t) ^ 2)) t :=
      hexact.congr_of_eventuallyEq hopen
    convert hres using 1
    rw [hφeq t ht']
    field_simp
  have hφmono : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ φ T := by
    intro t ht
    rw [hφeq t ht, hφeq T ⟨hT0, le_refl T⟩]
    rw [div_le_div_iff₀ (hden t ht) (hden T ⟨hT0, le_refl T⟩)]
    have hac : a * c < 0 := mul_neg_of_pos_of_neg ha hc
    have hprod : a * c * T ≤ a * c * t :=
      mul_le_mul_of_nonpos_left ht.2 (le_of_lt hac)
    nlinarith
  have hkey := closed_parabolic_min_principle_var_Ioc_continuousOn
    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
    (u := fun τ x ↦ R τ x - φ τ)
    (u' := fun τ x ↦ R' τ x - a * (φ τ) ^ 2)
    (c := fun τ x ↦ a * (R τ x + φ τ))
    (T := T) (M₀ := a * (B + φ T)) hT0
    (by
      intro τ hτ x
      have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
      have h1 := hRB τ hτ' x
      have h2 := hφmono τ hτ'
      dsimp [R]
      nlinarith)
    (by
      apply ContinuousOn.sub hR_cont
      have hφcont : Continuous φ := by
        simp only [φ]
        apply Continuous.div continuous_const
        · exact Continuous.max (by continuity) continuous_const
        · intro s
          have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          have hle : (1 / 2 : ℝ) ≤ max (1 - a * c * s) (1 / 2 : ℝ) :=
            le_max_right _ _
          intro hzero
          rw [hzero] at hle
          linarith
      exact (hφcont.comp continuous_fst).continuousOn)
    (by
      intro x τ hτ
      exact (hRd x τ hτ).sub (hφd τ hτ))
    (by
      intro τ hτ k x
      have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun z : M ↦ R τ z - φ τ) y := by
        intro y
        exact (hScalar₂ τ hτ' y).sub contMDiffAt_const
      have hk : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
        fun _ ↦ contMDiffAt_const
      change (gt (t₀ + τ)).laplacianAt
          (fun y : M ↦ R τ y - φ τ + k) x =
        (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
      rw [show (fun y : M ↦ R τ y - φ τ + k) =
          (fun z : M ↦ R τ z - φ τ) + fun _ : M ↦ k from by rfl]
      rw [(gt (t₀ + τ)).laplacianAt_add'
        (f := fun z : M ↦ R τ z - φ τ) (h := fun _ : M ↦ k)
        (x := x) hf hk]
      rw [(gt (t₀ + τ)).laplacianAt_const k x]
      ring)
    (by
      intro τ hτ x
      have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
      have hev := hevol τ hτ x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (R τ) y :=
        fun y ↦ hScalar₂ τ hτ' y
      have hconst : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun _ : M ↦ -(φ τ)) y := fun _ ↦ contMDiffAt_const
      have hlap :
          (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x =
            (gt (t₀ + τ)).laplacianAt (R τ) x := by
        rw [show (fun y : M ↦ R τ y - φ τ) =
            (fun y : M ↦ R τ y) + fun _ : M ↦ -(φ τ) from by
              funext y
              rw [sub_eq_add_neg]
              rfl]
        rw [(gt (t₀ + τ)).laplacianAt_add'
          (f := R τ) (h := fun _ : M ↦ -(φ τ)) (x := x) hf hconst]
        rw [(gt (t₀ + τ)).laplacianAt_const (-φ τ) x]
        ring
      change (gt (t₀ + τ)).laplacianAt
          (fun y : M ↦ R τ y - φ τ) x +
          a * (R τ x + φ τ) * (R τ x - φ τ) ≤
        R' τ x - a * φ τ ^ 2
      rw [hlap]
      nlinarith [hev])
    (by
      intro τ hτ x hmin
      have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2⟩
      have hf : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ R τ y - φ τ) x :=
        (hScalar₂ τ hτ' x).sub contMDiffAt_const
      exact laplacianAt_nonneg_of_isLocalMin
        (g := gt (t₀ + τ))
        (f := fun y : M ↦ R τ y - φ τ)
        (x := x) hf ((gt (t₀ + τ)).mdifferentiableAt_gradient hf)
        (hmin.isLocalMin Filter.univ_mem))
    (by
      intro x
      have h00 := h0point x
      have hφ0 : φ 0 = c := by
        rw [hφeq 0 ⟨le_refl 0, hT0⟩]
        simp
      simp only
      rw [hφ0]
      exact sub_nonneg.mpr h00)
  intro τ hτ x
  have hfin := hkey τ hτ x
  simp only at hfin
  have hφle : φ τ ≤ R τ x := by linarith
  rw [hφeq τ hτ] at hφle
  simpa [a, R] using hφle

/-- Compatibility form of the interior Hamilton barrier for callers that have
global joint scalar continuity. -/
theorem hamilton_scalar_negative_lower_bound_Ioc
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ T c B : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : c < 0) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿(fun τ (x : M) ↦ (gt (t₀ + τ)).scalarAt x))
    (hHam : ∀ τ ∈ Ioc (0 : ℝ) T, ∀ x : M,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x)
    (hScalar₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x)
    (hRB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).scalarAt x ≤ B)
    (h0 : c ≤ scalarMinimumTrack gt t₀ 0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      c / (1 - ((2 : ℝ) / 3) * c * τ) ≤
        (gt (t₀ + τ)).scalarAt x :=
  hamilton_scalar_negative_lower_bound_Ioc_continuousOn
    hc hT0 hR_cont.continuousOn hHam hScalar₂ hRB h0

/-- Type-changing segmented Hamilton barrier whose scalar evolution premise
starts strictly after each surgery time.  The initial scalar floor and joint
continuity carry the estimate across the omitted segment starts. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family_Ioc_continuousOn
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C : ℝ} (hC : 0 < C)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      ContinuousOn
        (fun p : ℝ × X k ↦
          (g k (start k + p.1)).scalarAt p.2)
        (Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ
          (Set.univ : Set (X k))))
    (hHam : ∀ k,
      ∀ τ ∈ Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B k)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : X k,
      -(3 / (2 * (C + t))) ≤ (g k t).scalarAt x := by
  have hstart_nonneg : ∀ k, 0 ≤ start k := by
    intro k
    induction k with
    | zero => simp [hstart0]
    | succ k ih => exact ih.trans (hmono k)
  let cseg : ℕ → ℝ := fun k ↦ -(3 / (2 * (C + start k)))
  have hcseg_neg : ∀ k, cseg k < 0 := by
    intro k
    have hden : 0 < C + start k := by linarith [hstart_nonneg k]
    dsimp [cseg]
    exact neg_lt_zero.mpr
      (div_pos (by norm_num) (mul_pos (by norm_num) hden))
  have hfloor : ∀ k, cseg k ≤ scalarMinimumAt (g k (start k)) := by
    intro k
    induction k with
    | zero =>
        simpa [cseg, hstart0] using hInitial
    | succ k ih =>
        have hT0 : 0 ≤ start (k + 1) - start k := sub_nonneg.mpr (hmono k)
        have hsegment := hamilton_scalar_negative_lower_bound_Ioc_continuousOn
          (M := X k) (gt := g k) (t₀ := start k)
          (T := start (k + 1) - start k) (c := cseg k) (B := B k)
          (hcseg_neg k) hT0 (hRCont k) (hHam k) (hScalar₂ k) (hRB k)
          (by simpa [scalarMinimumTrack] using ih)
        have hτend : start (k + 1) - start k ∈
            Icc (0 : ℝ) (start (k + 1) - start k) :=
          ⟨hT0, le_refl _⟩
        have hslice₂ : ∀ x : X k,
            ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
              (fun y : X k ↦ (g k (start (k + 1))).scalarAt y) x := by
          intro x
          simpa [add_sub_cancel_left] using hScalar₂ k
            (start (k + 1) - start k) hτend x
        obtain ⟨xmin, hxmin⟩ :=
          exists_scalarAt_isMinOn (g := g k (start (k + 1))) hslice₂
        have hend := hsegment (start (k + 1) - start k) hτend xmin
        have hrestart :
            cseg (k + 1) =
              cseg k /
                (1 - ((2 : ℝ) / 3) * cseg k *
                  (start (k + 1) - start k)) := by
          symm
          simpa [cseg] using
            (three_dimensional_negative_scalar_barrier_restart
              (C := C) (s := start k) (t := start (k + 1))
              (by linarith [hstart_nonneg k]) (hmono k))
        have hold :
            cseg (k + 1) ≤ scalarMinimumAt (g k (start (k + 1))) := by
          rw [scalarMinimumAt_eq_of_isMinOn
            (g := g k (start (k + 1))) hxmin]
          rw [hrestart]
          simpa [add_sub_cancel_left] using hend
        exact hold.trans (hSurgery k)
  intro k t ht x
  have hT0 : 0 ≤ start (k + 1) - start k := sub_nonneg.mpr (hmono k)
  have hτ : t - start k ∈ Icc (0 : ℝ) (start (k + 1) - start k) := by
    constructor <;> linarith [ht.1, ht.2]
  have hsegment := hamilton_scalar_negative_lower_bound_Ioc_continuousOn
    (M := X k) (gt := g k) (t₀ := start k)
    (T := start (k + 1) - start k) (c := cseg k) (B := B k)
    (hcseg_neg k) hT0 (hRCont k) (hHam k) (hScalar₂ k) (hRB k)
    (by simpa [scalarMinimumTrack] using hfloor k)
  have hpoint := hsegment (t - start k) hτ x
  have hrestart := three_dimensional_negative_scalar_barrier_restart
    (C := C) (s := start k) (t := t)
    (by linarith [hstart_nonneg k]) ht.1
  rw [← hrestart]
  simpa [cseg, add_sub_cancel_left] using hpoint

/-- Compatibility form of the segmented interior Hamilton barrier for callers
that have global joint scalar continuity on every segment. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family_Ioc
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C : ℝ} (hC : 0 < C)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k,
      ∀ τ ∈ Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B k)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : X k,
      -(3 / (2 * (C + t))) ≤ (g k t).scalarAt x :=
  hamilton_scalar_segmented_negative_lower_bound_family_Ioc_continuousOn
    hC g start B hstart0 hmono (fun k ↦ (hRCont k).continuousOn)
      hHam hScalar₂ hRB hSurgery hInitial

/-- Compactness-derived type-changing segmented barrier with Hamilton scalar
evolution required only on `Ioc` after each segment start. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family_compact_Ioc_continuousOn
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C : ℝ} (hC : 0 < C)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      ContinuousOn
        (fun p : ℝ × X k ↦
          (g k (start k + p.1)).scalarAt p.2)
        (Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ
          (Set.univ : Set (X k))))
    (hHam : ∀ k,
      ∀ τ ∈ Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : X k,
      -(3 / (2 * (C + t))) ≤ (g k t).scalarAt x := by
  classical
  have hBound : ∀ k, ∃ B : ℝ,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B := by
    intro k
    let f : ℝ × X k → ℝ := fun p ↦ (g k (start k + p.1)).scalarAt p.2
    let K : Set (ℝ × X k) :=
      Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ (Set.univ : Set (X k))
    have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
    have hf : ContinuousOn f K := by simpa [f, K] using hRCont k
    obtain ⟨B, hB⟩ := hK.bddAbove_image hf
    refine ⟨B, ?_⟩
    intro τ hτ x
    have hmem : f (τ, x) ∈ f '' K :=
      mem_image_of_mem f (show (τ, x) ∈ K by exact ⟨hτ, Set.mem_univ x⟩)
    simpa [f] using hB hmem
  let B : ℕ → ℝ := fun k ↦ Classical.choose (hBound k)
  exact hamilton_scalar_segmented_negative_lower_bound_family_Ioc_continuousOn
    hC g start B hstart0 hmono hRCont hHam hScalar₂
      (fun k ↦ by simpa [B] using Classical.choose_spec (hBound k))
      hSurgery hInitial

/-- Compatibility form of the compact segmented interior Hamilton barrier for
callers that have global joint scalar continuity on every segment. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family_compact_Ioc
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C : ℝ} (hC : 0 < C)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k,
      ∀ τ ∈ Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : X k,
      -(3 / (2 * (C + t))) ≤ (g k t).scalarAt x :=
  hamilton_scalar_segmented_negative_lower_bound_family_compact_Ioc_continuousOn
    hC g start hstart0 hmono (fun k ↦ (hRCont k).continuousOn)
      hHam hScalar₂ hSurgery hInitial

end Poincare
