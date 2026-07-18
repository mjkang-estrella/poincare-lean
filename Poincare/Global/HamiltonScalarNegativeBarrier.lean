import Poincare.Global.ScalarEvolution

/-!
# Hamilton's negative scalar-curvature barrier

This file proves the compact closed-manifold lower barrier needed by the
finite-extinction width argument.  Unlike a scalar-minimum ODE formulation,
the proof works directly with Hamilton's pointwise scalar evolution and the
closed parabolic minimum principle, so no differentiable choice of minimizing
point is required.
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

/-- Hamilton's scalar lower bound for a negative initial floor.

If `c < 0` is a pointwise lower bound at time `t₀`, then on every compact
time interval the scalar curvature stays above

`c / (1 - (2/3) c τ)`.

The argument is the genuine compact-manifold parabolic comparison for
`R - φ`, where `φ` is the displayed Riccati solution. -/
theorem hamilton_scalar_negative_lower_bound
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ T c B : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : c < 0) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿(fun τ (x : M) ↦ (gt (t₀ + τ)).scalarAt x))
    (hHam : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
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
  have ha : 0 < a := by
    norm_num [a]
  have hRd : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' τ x) τ := by
    intro x τ hτ
    have hbase :
        HasDerivAt (fun t ↦ (gt t).scalarAt x) (R' τ x) (t₀ + τ) := by
      simpa [SatisfiesHamiltonScalarEvolutionAt, R, R'] using hHam τ hτ x
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [R] using hbase.comp τ hshift
  have hevol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤
        R' τ x := by
    intro τ hτ x
    have hreact := hamilton_scalar_reaction_bound_at
      (g := gt (t₀ + τ)) (x := x) (show 0 < (3 : ℝ) by norm_num)
    dsimp [a, R, R']
    linarith
  have hscalar0 :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
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
  have hφd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt φ (a * (φ t) ^ 2) t := by
    intro t ht
    have hd := hden t ht
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
      have hcont : Continuous (fun s ↦ 1 - a * c * s) := by
        continuity
      have hhalf : (1 / 2 : ℝ) < 1 - a * c * t := by
        have hhalf_one : (1 / 2 : ℝ) < 1 := by norm_num
        exact hhalf_one.trans_le (hden_one t ht)
      have hev : ∀ᶠ s in nhds t, (1 / 2 : ℝ) < 1 - a * c * s :=
        hcont.continuousAt.eventually_const_lt hhalf
      filter_upwards [hev] with s hs
      simp only [φ]
      rw [max_eq_left (le_of_lt hs), div_eq_mul_inv]
    have hres : HasDerivAt φ
        (c * (a * c / (1 - a * c * t) ^ 2)) t :=
      hexact.congr_of_eventuallyEq hopen
    convert hres using 1
    rw [hφeq t ht]
    field_simp
  have hφmono : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ φ T := by
    intro t ht
    rw [hφeq t ht, hφeq T ⟨hT0, le_refl T⟩]
    rw [div_le_div_iff₀ (hden t ht) (hden T ⟨hT0, le_refl T⟩)]
    have hac : a * c < 0 := mul_neg_of_pos_of_neg ha hc
    have hprod : a * c * T ≤ a * c * t :=
      mul_le_mul_of_nonpos_left ht.2 (le_of_lt hac)
    nlinarith
  have hkey := closed_parabolic_min_principle_var
    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
    (u := fun τ x ↦ R τ x - φ τ)
    (u' := fun τ x ↦ R' τ x - a * (φ τ) ^ 2)
    (c := fun τ x ↦ a * (R τ x + φ τ))
    (T := T) (M₀ := a * (B + φ T))
    (by
      intro τ hτ x
      have h1 := hRB τ hτ x
      have h2 := hφmono τ hτ
      dsimp [R]
      nlinarith)
    (by
      apply Continuous.sub hR_cont
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
      exact hφcont.comp continuous_fst)
    (by
      intro x τ hτ
      exact (hRd x τ hτ).sub (hφd τ hτ))
    (by
      intro τ hτ k x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun z : M ↦ R τ z - φ τ) y := by
        intro y
        exact (hScalar₂ τ hτ y).sub contMDiffAt_const
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
      have hev := hevol τ hτ x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (R τ) y :=
        fun y ↦ hScalar₂ τ hτ y
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
        rw [(gt (t₀ + τ)).laplacianAt_const (-(φ τ)) x]
        ring
      change (gt (t₀ + τ)).laplacianAt
          (fun y : M ↦ R τ y - φ τ) x +
          a * (R τ x + φ τ) * (R τ x - φ τ) ≤
        R' τ x - a * φ τ ^ 2
      rw [hlap]
      nlinarith [hev])
    (by
      intro τ hτ x hmin
      have hf : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ R τ y - φ τ) x :=
        (hScalar₂ τ hτ x).sub contMDiffAt_const
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

/-- Compactness supplies the scalar upper bound needed internally by the
variable-coefficient parabolic comparison, so callers need only joint
continuity of scalar curvature. -/
theorem hamilton_scalar_negative_lower_bound_compact
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ T c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : c < 0) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿(fun τ (x : M) ↦ (gt (t₀ + τ)).scalarAt x))
    (hHam : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x)
    (hScalar₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x)
    (h0 : c ≤ scalarMinimumTrack gt t₀ 0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      c / (1 - ((2 : ℝ) / 3) * c * τ) ≤
        (gt (t₀ + τ)).scalarAt x := by
  let f : ℝ × M → ℝ := fun p ↦ (gt (t₀ + p.1)).scalarAt p.2
  let K : Set (ℝ × M) := Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hf : Continuous f := by simpa [f] using hR_cont
  obtain ⟨B, hB⟩ := hK.bddAbove_image hf.continuousOn
  have hRB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).scalarAt x ≤ B := by
    intro τ hτ x
    have hmem : f (τ, x) ∈ f '' K :=
      mem_image_of_mem f (show (τ, x) ∈ K by exact ⟨hτ, Set.mem_univ x⟩)
    simpa [f] using hB hmem
  exact hamilton_scalar_negative_lower_bound
    (gt := gt) (t₀ := t₀) (T := T) (c := c) (B := B)
      hc hT0 hR_cont hHam hScalar₂ hRB h0

/-- Restart identity for the three-dimensional negative Riccati barrier. -/
theorem three_dimensional_negative_scalar_barrier_restart
    {C s t : ℝ} (hCs : 0 < C + s) (hst : s ≤ t) :
    (-(3 / (2 * (C + s)))) /
        (1 - ((2 : ℝ) / 3) * (-(3 / (2 * (C + s)))) * (t - s)) =
      -(3 / (2 * (C + t))) := by
  have hCt : 0 < C + t := by linarith
  have hdenom :
      1 - ((2 : ℝ) / 3) * (-(3 / (2 * (C + s)))) * (t - s) =
        (C + t) / (C + s) := by
    field_simp [ne_of_gt hCs]
    ring
  rw [hdenom]
  field_simp [ne_of_gt hCs, ne_of_gt hCt]

/-- Segmentwise Hamilton evolution plus scalar-nondecreasing surgery preserves
the standard three-dimensional lower barrier on every smooth segment.

This theorem applies the pointwise parabolic comparison on each segment and
restarts its exact Riccati solution at every surgery time.  It does not choose
or differentiate a scalar-minimizing point. -/
theorem hamilton_scalar_segmented_negative_lower_bound
    [CompactSpace M] [Nonempty M]
    {C : ℝ} (hC : 0 < C)
    (g : ℕ → ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : M) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M, (g k (start k + τ)).scalarAt x ≤ B k)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : M,
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
        have hsegment := hamilton_scalar_negative_lower_bound
          (gt := g k) (t₀ := start k)
          (T := start (k + 1) - start k) (c := cseg k) (B := B k)
          (hcseg_neg k) hT0 (hRCont k) (hHam k) (hScalar₂ k) (hRB k)
          (by simpa [scalarMinimumTrack] using ih)
        have hτend : start (k + 1) - start k ∈
            Icc (0 : ℝ) (start (k + 1) - start k) :=
          ⟨hT0, le_refl _⟩
        have hslice₂ : ∀ x : M,
            ContMDiffAt I 𝓘(ℝ) 2
              (fun y : M ↦ (g k (start (k + 1))).scalarAt y) x := by
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
  have hsegment := hamilton_scalar_negative_lower_bound
    (gt := g k) (t₀ := start k)
    (T := start (k + 1) - start k) (c := cseg k) (B := B k)
    (hcseg_neg k) hT0 (hRCont k) (hHam k) (hScalar₂ k) (hRB k)
    (by simpa [scalarMinimumTrack] using hfloor k)
  have hpoint := hsegment (t - start k) hτ x
  have hrestart := three_dimensional_negative_scalar_barrier_restart
    (C := C) (s := start k) (t := t)
    (by linarith [hstart_nonneg k]) ht.1
  rw [← hrestart]
  simpa [cseg, add_sub_cancel_left] using hpoint

/-- Compactness-derived version of the fixed-manifold segmented barrier; no
separate scalar upper-bound function is required. -/
theorem hamilton_scalar_segmented_negative_lower_bound_compact
    [CompactSpace M] [Nonempty M]
    {C : ℝ} (hC : 0 < C)
    (g : ℕ → ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : M) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (g k (start k + τ)).scalarAt y) x)
    (hSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hInitial : -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0))) :
    ∀ k, ∀ t ∈ Icc (start k) (start (k + 1)), ∀ x : M,
      -(3 / (2 * (C + t))) ≤ (g k t).scalarAt x := by
  classical
  have hBound : ∀ k, ∃ B : ℝ,
      ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : M,
        (g k (start k + τ)).scalarAt x ≤ B := by
    intro k
    let f : ℝ × M → ℝ := fun p ↦ (g k (start k + p.1)).scalarAt p.2
    let K : Set (ℝ × M) :=
      Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ (Set.univ : Set M)
    have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
    have hf : Continuous f := by simpa [f] using hRCont k
    obtain ⟨B, hB⟩ := hK.bddAbove_image hf.continuousOn
    refine ⟨B, ?_⟩
    intro τ hτ x
    have hmem : f (τ, x) ∈ f '' K :=
      mem_image_of_mem f (show (τ, x) ∈ K by exact ⟨hτ, Set.mem_univ x⟩)
    simpa [f] using hB hmem
  let B : ℕ → ℝ := fun k ↦ Classical.choose (hBound k)
  exact hamilton_scalar_segmented_negative_lower_bound
    hC g start B hstart0 hmono hRCont hHam hScalar₂
      (fun k ↦ by simpa [B] using Classical.choose_spec (hBound k))
      hSurgery hInitial

/-- Type-changing version of the segmented Hamilton barrier.

Every smooth segment may live on a different closed three-manifold.  The
surgery interface is therefore only the geometrically meaningful real-valued
comparison of scalar minima across the pre- and post-surgery slices. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family
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
    (hHam : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : X k, (g k (start k + τ)).scalarAt x ≤ B k)
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
        have hsegment := hamilton_scalar_negative_lower_bound
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
  have hsegment := hamilton_scalar_negative_lower_bound
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

/-- Compactness-derived type-changing segmented Hamilton barrier. -/
theorem hamilton_scalar_segmented_negative_lower_bound_family_compact
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
    (hHam : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, ∀ τ ∈ Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : X k,
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
    have hf : Continuous f := by simpa [f] using hRCont k
    obtain ⟨B, hB⟩ := hK.bddAbove_image hf.continuousOn
    refine ⟨B, ?_⟩
    intro τ hτ x
    have hmem : f (τ, x) ∈ f '' K :=
      mem_image_of_mem f (show (τ, x) ∈ K by exact ⟨hτ, Set.mem_univ x⟩)
    simpa [f] using hB hmem
  let B : ℕ → ℝ := fun k ↦ Classical.choose (hBound k)
  exact hamilton_scalar_segmented_negative_lower_bound_family
    hC g start B hstart0 hmono hRCont hHam hScalar₂
      (fun k ↦ by simpa [B] using Classical.choose_spec (hBound k))
      hSurgery hInitial

end Poincare
