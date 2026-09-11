import Poincare.Global.ParabolicHolderSpace
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.TransferInstance

/-! The zero initial trace space of genuine parabolic derivative graphs. -/

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace Poincare.ParabolicSolutionGraph

open Set Filter
open scoped Topology
open ParabolicHolder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Graph (α T : ℝ) where
  u : Y (E := E) α T ℝ
  ut : Y (E := E) α T ℝ
  du : Y (E := E) α T (E →L[ℝ] ℝ)
  ddu : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)
  zero_trace : ∀ x : E, u (0, x) = 0
  hasFDeriv : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x
  hasFDeriv_du : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x
  hasDeriv_time : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t

abbrev Ambient (α T : ℝ) :=
  WithLp 1 (WithLp 1 (Y (E := E) α T ℝ × Y (E := E) α T ℝ) ×
    WithLp 1 (Y (E := E) α T (E →L[ℝ] ℝ) ×
      Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)))

def graphSubmodule (α T : ℝ) : Submodule ℝ (Ambient (E := E) α T) where
  carrier := {v | (∀ x : E, v.fst.fst (0, x) = 0) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => v.fst.fst (t, z)) (v.snd.fst (t, x)) x) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => v.snd.fst (t, z)) (v.snd.snd (t, x)) x) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun s : ℝ => v.fst.fst (s, x)) (v.fst.snd (t, x)) (Icc 0 T) t)}
  zero_mem' := by
    refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
    · intro t ht x; exact hasFDerivAt_const (0 : ℝ) x
    · intro t ht x; exact hasFDerivAt_const (0 : E →L[ℝ] ℝ) x
    · intro t ht x; exact hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)
  add_mem' := by
    intro v w hv hw
    exact ⟨fun x => by change v.fst.fst (0,x) + w.fst.fst (0,x) = 0; rw [hv.1, hw.1, add_zero],
      fun t ht x => (hv.2.1 t ht x).add (hw.2.1 t ht x),
      fun t ht x => (hv.2.2.1 t ht x).add (hw.2.2.1 t ht x),
      fun t ht x => (hv.2.2.2 t ht x).add (hw.2.2.2 t ht x)⟩
  smul_mem' := by
    intro c v hv
    exact ⟨fun x => by change c • v.fst.fst (0,x) = 0; rw [hv.1, smul_zero],
      fun t ht x => (hv.2.1 t ht x).const_smul c,
      fun t ht x => (hv.2.2.1 t ht x).const_smul c,
      fun t ht x => (hv.2.2.2 t ht x).const_smul c⟩

variable {α T : ℝ}

def graphEquiv : Graph (E := E) α T ≃ ↥(graphSubmodule (E := E) α T) where
  toFun g := ⟨WithLp.toLp 1 (WithLp.toLp 1 (g.u, g.ut), WithLp.toLp 1 (g.du, g.ddu)),
    g.zero_trace, g.hasFDeriv, g.hasFDeriv_du, g.hasDeriv_time⟩
  invFun v := ⟨v.val.fst.fst, v.val.fst.snd, v.val.snd.fst, v.val.snd.snd,
    v.property.1, v.property.2.1, v.property.2.2.1, v.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instNormedAddCommGroup : NormedAddCommGroup (Graph (E := E) α T) :=
  graphEquiv.normedAddCommGroup

instance instModule : Module ℝ (Graph (E := E) α T) := graphEquiv.module ℝ

instance instNormedSpace : NormedSpace ℝ (Graph (E := E) α T) := by
  letI : NormedSpace ℝ (Ambient (E := E) α T) := inferInstance
  exact graphEquiv.normedSpace ℝ

theorem norm_eq (g : Graph (E := E) α T) :
    ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ := by
  change ‖(graphEquiv g).val‖ = _
  simp only [WithLp.prod_norm_eq_of_L1]
  exact (add_assoc _ _ _).symm

theorem norm_u_le (g : Graph (E := E) α T) : ‖g.u‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_ut_le (g : Graph (E := E) α T) : ‖g.ut‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_du_le (g : Graph (E := E) α T) : ‖g.du‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem sup_u_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.u p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)

theorem holder_u_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.u p - g.u q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.u hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_u_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

theorem sup_ut_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.ut p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.ut p).trans (norm_ut_le g)

theorem holder_ut_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.ut p - g.ut q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.ut hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_ut_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

theorem sup_du_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.du p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.du p).trans (norm_du_le g)

theorem holder_du_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.du p - g.du q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.du hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_du_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

theorem sup_ddu_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.ddu p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.ddu p).trans (norm_ddu_le g)

theorem holder_ddu_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.ddu p - g.ddu q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.ddu hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_ddu_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

theorem time_bound (g : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : E) : ‖g.u (t, x)‖ ≤ t * ‖g.ut‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => g.hasDeriv_time s hs x)
    (fun s _ => ParabolicHolder.norm_le g.ut (s, x)) (convex_Icc (0 : ℝ) T)
    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
  simpa [g.zero_trace x, Real.norm_of_nonneg ht.1, mul_comm] using h

/-- Bundle four supported bounded Hölder functions with exactly the derivative relations. -/
def ofDerivatives
    (u : ℝ × E → ℝ)
    (ut : ℝ × E → ℝ)
    (du : ℝ × E → E →L[ℝ] ℝ)
    (ddu : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (hu_off : ∀ p, p ∉ cylinder T → u p = 0)
    (hu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖u p‖ ≤ M)
    (hu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) u K)
    (hut_off : ∀ p, p ∉ cylinder T → ut p = 0)
    (hut_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖ut p‖ ≤ M)
    (hut_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) ut K)
    (hdu_off : ∀ p, p ∉ cylinder T → du p = 0)
    (hdu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖du p‖ ≤ M)
    (hdu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) du K)
    (hddu_off : ∀ p, p ∉ cylinder T → ddu p = 0)
    (hddu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖ddu p‖ ≤ M)
    (hddu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) ddu K)
    (hzero : ∀ x : E, u (0, x) = 0)
    (hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x)
    (hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x)
    (hut : ∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t) :
    Graph (E := E) α T where
  u := ofFunction u hu_off hu_bound hu_holder
  ut := ofFunction ut hut_off hut_bound hut_holder
  du := ofFunction du hdu_off hdu_bound hdu_holder
  ddu := ofFunction ddu hddu_off hddu_bound hddu_holder
  zero_trace := hzero
  hasFDeriv := hdu
  hasFDeriv_du := hddu
  hasDeriv_time := hut

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem holder_tendstoUniformly {v : ℕ → Y (E := E) α T F} {w : Y (E := E) α T F}
    (h : Tendsto v atTop (𝓝 w)) : TendstoUniformly (fun n p => v n p) w atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.1 h) ε hε] with n hn p
  have hb := Poincare.ParabolicHolder.norm_le (w - v n) p
  change ‖w p - v n p‖ ≤ ‖w - v n‖ at hb
  rw [dist_eq_norm]
  exact hb.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn)

/-- Uniform convergence of the derivatives closes the derivative relation on a convex set. -/
theorem closed_time_derivative {f d : ℕ → ℝ → ℝ} {g e : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ∀ n t, t ∈ s → HasDerivWithinAt (f n) (d n t) s t)
    (hfg : ∀ t ∈ s, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hde : TendstoUniformlyOn d e atTop s) {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt g (e x) s x := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hde) _ hε4)
  have hnear (n : ℕ) (hn : N ≤ n) (y : ℝ) (hy : y ∈ s) :
      ‖d n y - e y‖ ≤ ε / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn y hy).le
  have hdiff (y : ℝ) (hy : y ∈ s) :
      ‖(g y - f N y) - (g x - f N x)‖ ≤ (ε / 2) * ‖y - x‖ := by
    apply le_of_tendsto (((hfg y hy).sub tendsto_const_nhds).sub
      ((hfg x hx).sub tendsto_const_nhds)).norm
    filter_upwards [eventually_ge_atTop N] with n hn
    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hf n z hz).sub (hf N z hz)) _ hs hx hy
    intro z hz
    calc
      ‖d n z - d N z‖ ≤ ‖d n z - e z‖ + ‖e z - d N z‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ ε / 2 := by rw [norm_sub_rev (e z)]; linarith [hnear n hn z hz, hnear N le_rfl z hz]
  filter_upwards [(hf N x hx).isLittleO.bound hε4, self_mem_nhdsWithin] with y hy hys
  have hlast : ‖(y - x) * (d N x - e x)‖ ≤ (ε / 4) * ‖y - x‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hnear N le_rfl x hx) (norm_nonneg _)
  calc
    ‖g y - g x - (y - x) • e x‖ =
        ‖((g y - f N y) - (g x - f N x)) +
          (f N y - f N x - (y - x) • d N x) + (y - x) * (d N x - e x)‖ := by
      congr 1
      simp only [smul_eq_mul]
      ring
    _ ≤ ‖(g y - f N y) - (g x - f N x)‖ +
        ‖f N y - f N x - (y - x) • d N x‖ + ‖(y - x) * (d N x - e x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε * ‖y - x‖ := by linarith [hdiff y hys]

/-- All three derivative relations and the initial trace are closed in the jet norm. -/
theorem isClosed_graphSubmodule :
    IsClosed (graphSubmodule (E := E) α T : Set (Ambient (E := E) α T)) := by
  apply isSeqClosed_iff_isClosed.1
  intro v w hv hw
  have cu : Continuous (fun z : Ambient (E := E) α T => z.fst.fst) :=
    (WithLp.continuous_fst ..).comp (WithLp.continuous_fst ..)
  have ct : Continuous (fun z : Ambient (E := E) α T => z.fst.snd) :=
    (WithLp.continuous_snd ..).comp (WithLp.continuous_fst ..)
  have cd : Continuous (fun z : Ambient (E := E) α T => z.snd.fst) :=
    (WithLp.continuous_fst ..).comp (WithLp.continuous_snd ..)
  have cdd : Continuous (fun z : Ambient (E := E) α T => z.snd.snd) :=
    (WithLp.continuous_snd ..).comp (WithLp.continuous_snd ..)
  have hu := holder_tendstoUniformly ((cu.tendsto w).comp hw)
  have ht := holder_tendstoUniformly ((ct.tendsto w).comp hw)
  have hd := holder_tendstoUniformly ((cd.tendsto w).comp hw)
  have hdd := holder_tendstoUniformly ((cdd.tendsto w).comp hw)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    apply tendsto_nhds_unique (hu.tendsto_at (0, x))
    have heq : (fun n => (v n).fst.fst (0, x)) = fun _ : ℕ => (0 : ℝ) :=
      funext fun n => (hv n).1 x
    change Tendsto (fun n => (v n).fst.fst (0, x)) atTop (𝓝 0)
    rw [heq]
    exact tendsto_const_nhds
  · intro t ht' x
    exact hasFDerivAt_of_tendstoUniformly (hd.comp (fun z : E => (t, z)))
      (fun n z => (hv n).2.1 t ht' z) (fun z => hu.tendsto_at (t, z)) x
  · intro t ht' x
    exact hasFDerivAt_of_tendstoUniformly (hdd.comp (fun z : E => (t, z)))
      (fun n z => (hv n).2.2.1 t ht' z) (fun z => hd.tendsto_at (t, z)) x
  · intro t ht' x
    exact closed_time_derivative (convex_Icc 0 T)
      (fun n s hs => (hv n).2.2.2 s hs x) (fun s _ => hu.tendsto_at (s, x))
      (ht.comp (fun s : ℝ => (s, x))).tendstoUniformlyOn ht'

end Poincare.ParabolicSolutionGraph
