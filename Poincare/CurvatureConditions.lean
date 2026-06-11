/-
Curvature conditions.

With the genuine Ricci tensor and scalar curvature available, the classical
curvature hypotheses of geometric analysis (Einstein metrics, Ricci
positivity, positive scalar curvature) become stateable with content.  The
flat model realizes the degenerate cases.
-/

import Poincare.EuclideanLeviCivitaCheck

noncomputable section

open Bundle CovariantDerivative Filter FiberBundle Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable [ContMDiffCovariantDerivative cov 1]
variable (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)

/-- The Einstein condition at a point: `Ric = λ g`. -/
def IsEinsteinAt (lam : ℝ) (x : M) : Prop :=
  ∀ u w : TangentSpace I x, ricciBilinearAt cov x u w = lam * g x u w

/-- Nonnegative Ricci curvature at a point. -/
def HasNonnegRicciAt (x : M) : Prop :=
  ∀ u : TangentSpace I x, 0 ≤ ricciBilinearAt cov x u u

/-- Positive Ricci curvature at a point. -/
def HasPosRicciAt (x : M) : Prop :=
  ∀ u : TangentSpace I x, u ≠ 0 → 0 < ricciBilinearAt cov x u u

/--
**Scalar curvature of an Einstein connection**: if `Ric = lam g` at `x`,
the scalar curvature with respect to the matching bilinear form is
`lam * dim`.
-/
theorem scalarCurvatureAt_of_einstein {lam : ℝ} {x : M}
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    (hbg : ∀ v w : TangentSpace I x, b v w = g x v w)
    (hEin : IsEinsteinAt cov g lam x) :
    scalarCurvatureAt cov x b hb = lam * Module.finrank ℝ E := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := ‹FiniteDimensional ℝ E›
  have hcomp : (LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
      ricciDualAt cov x = lam • LinearMap.id := by
    apply LinearMap.ext
    intro u
    have hdual : ricciDualAt cov x u =
        lam • (LinearMap.BilinForm.toDual b hb) u := by
      apply LinearMap.ext
      intro w
      simp only [ricciDualAt, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hEin u w, ← hbg]
      rw [LinearMap.BilinForm.toDual_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hdual, map_smul,
      LinearEquiv.symm_apply_apply, LinearMap.smul_apply, LinearMap.id_apply]
  unfold scalarCurvatureAt
  rw [hcomp, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  rw [hr]

/-! ## Ricci agreement for coincident connections -/

section RicciAgree

variable {cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}

/--
Two connections that agree on differentiable fields at every point have the
same curvature on `C²` data, hence the same Ricci trace.
-/
theorem ricciTraceAt_eq_of_agree
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    {Z : Π y : M, TangentSpace I y} {x : M} (hZ : CMDiffAt 2 (T% Z) x)
    (hreg : DerivRegularAt cov Z x) (hreg' : DerivRegularAt cov' Z x)
    (u : TangentSpace I x) :
    ricciTraceAt cov hreg u = ricciTraceAt cov' hreg' u := by
  unfold ricciTraceAt
  congr 1
  apply LinearMap.ext
  intro v
  rw [curvatureEndAt_apply, curvatureEndAt_apply]
  unfold curvatureTensorAt
  rw [TensorialAt.mkHom₂_apply_eq_extend, TensorialAt.mkHom₂_apply_eq_extend]
  -- Differentiability of Z near x.
  have hZd : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := by
    obtain ⟨v', hv', hZv⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
    filter_upwards [interior_mem_nhds.mpr hv'] with y hy
    exact (((hZv.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  -- The inner sections agree near x.
  have hinner : ∀ (W : Π y : M, TangentSpace I y),
      (fun y ↦ cov Z y (W y)) =ᶠ[𝓝 x] fun y ↦ cov' Z y (W y) := by
    intro W
    filter_upwards [hZd] with y hy
    rw [hagree y Z hy]
  -- Outer derivatives coincide at x.
  have houter : ∀ (W : Π y : M, TangentSpace I y), MDiffAt (T% W) x →
      cov (fun y ↦ cov Z y (W y)) x = cov' (fun y ↦ cov' Z y (W y)) x := by
    intro W hW
    have hA : MDiffAt (T% (fun y ↦ cov Z y (W y))) x :=
      mdiffAt_cov_section_of_contMDiffAt cov hZ hW
    have hA' : MDiffAt (T% (fun y ↦ cov' Z y (W y))) x := by
      refine hA.congr_of_eventuallyEq ?_
      filter_upwards [hinner W] with y hy
      rw [Bundle.TotalSpace.mk_inj]
      exact hy.symm
    calc cov (fun y ↦ cov Z y (W y)) x
        = cov (fun y ↦ cov' Z y (W y)) x :=
          cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hA hA'
            univ_mem (hinner W)
      _ = cov' (fun y ↦ cov' Z y (W y)) x := hagree x _ hA'
  rw [curvatureOp_apply, curvatureOp_apply,
    houter (extend E u) (mdifferentiableAt_extend ..),
    houter (extend E v) (mdifferentiableAt_extend ..),
    hagree x Z hZx]

/--
Connections agreeing on differentiable fields have equal canonical Ricci
forms.
-/
theorem ricciBilinearAt_eq_of_agree [CompleteSpace E]
    [ContMDiffCovariantDerivative cov' 1]
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    (x : M) (u w : TangentSpace I x) :
    ricciBilinearAt cov x u w = ricciBilinearAt cov' x u w :=
  ricciTraceAt_eq_of_agree cov hagree
    (FiberBundle.contMDiffAt_extend' (k := 2) I E w)
    (derivRegularAt_extend cov w) (derivRegularAt_extend cov' w) u

/-- Ricci nonnegativity transfers along connection agreement. -/
theorem HasNonnegRicciAt.of_agree [CompleteSpace E]
    [ContMDiffCovariantDerivative cov' 1]
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    {x : M} (h : HasNonnegRicciAt cov x) : HasNonnegRicciAt cov' x :=
  fun u ↦ (ricciBilinearAt_eq_of_agree cov hagree x u u) ▸ h u

/-- Ricci positivity transfers along connection agreement. -/
theorem HasPosRicciAt.of_agree [CompleteSpace E]
    [ContMDiffCovariantDerivative cov' 1]
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    {x : M} (h : HasPosRicciAt cov x) : HasPosRicciAt cov' x :=
  fun u hu ↦ (ricciBilinearAt_eq_of_agree cov hagree x u u) ▸ h u hu

/-- The Einstein condition transfers along connection agreement. -/
theorem IsEinsteinAt.of_agree [CompleteSpace E]
    [ContMDiffCovariantDerivative cov' 1]
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {lam : ℝ}
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    {x : M} (h : IsEinsteinAt cov g lam x) : IsEinsteinAt cov' g lam x :=
  fun u w ↦ (ricciBilinearAt_eq_of_agree cov hagree x u w) ▸ h u w

/-- Scalar curvature transfers along connection agreement. -/
theorem scalarCurvatureAt_eq_of_agree [CompleteSpace E]
    [ContMDiffCovariantDerivative cov' 1]
    (hagree : ∀ (y : M) (Y : Π z : M, TangentSpace I z),
      MDiffAt (T% Y) y → cov Y y = cov' Y y)
    (x : M) (b : LinearMap.BilinForm ℝ (TangentSpace I x))
    (hb : b.Nondegenerate) :
    scalarCurvatureAt cov x b hb = scalarCurvatureAt cov' x b hb := by
  unfold scalarCurvatureAt
  congr 1
  apply LinearMap.ext
  intro u
  simp only [LinearMap.comp_apply]
  congr 1
  apply LinearMap.ext
  intro w
  exact ricciBilinearAt_eq_of_agree cov hagree x u w

end RicciAgree

end CovariantDerivative

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- **Euclidean space is Ricci-flat**: the flat connection is Einstein with
constant `0` for the Euclidean metric. -/
theorem flat_isEinsteinAt_zero (x : F) :
    IsEinsteinAt (flatCovariantDerivative ℝ F)
      (euclideanBundleMetric (F := F)) 0 x := by
  intro u w
  rw [flat_ricciBilinearAt_eq_zero]
  ring

/-- Euclidean space has (trivially) nonnegative Ricci curvature. -/
theorem flat_hasNonnegRicciAt (x : F) :
    HasNonnegRicciAt (flatCovariantDerivative ℝ F) x := by
  intro u
  rw [flat_ricciBilinearAt_eq_zero]

end CovariantDerivative

/-! ## Einstein metrics flow by scaling -/

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  {g₀ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- Metric compatibility is preserved by constant scaling of the metric. -/
theorem MetricCompatibleAt.const_smul {x : M} (c : ℝ)
    (hc : MetricCompatibleAt g₀ cov x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g₀ y (A y) (B y)) x) :
    MetricCompatibleAt (fun y ↦ c • g₀ y) cov x := by
  intro Y Z hY hZ v
  have hfun : (fun y ↦ (c • g₀ y) (Y y) (Z y)) =
      (fun _ : M ↦ c) * fun y ↦ g₀ y (Y y) (Z y) := by
    funext y
    simp [smul_eq_mul]
  rw [hfun, extDerivFun_mul mdifferentiableAt_const (hP Y Z hY hZ)]
  have h0 : extDerivFun (I := I) (fun _ : M ↦ c) x v = 0 := by
    unfold extDerivFun
    rw [(hasMFDerivAt_const c x).mfderiv]
    simp
  rw [h0, hc hY hZ v]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ E]

/--
**Einstein metrics flow by linear scaling**: if `cov` is Levi-Civita for
`g₀` at `x` and Einstein in trace form with constant `lam`, then the family
`g(t) = (1 - 2 lam t) g₀` with the fixed connection is a Ricci flow
solution at every time and the point `x`.
-/
theorem einstein_isRicciFlowSolutionAt (lam : ℝ) {x : M}
    (hLC : IsLeviCivitaAt g₀ cov x)
    (hP : ∀ (A B : Π y : M, TangentSpace I y), MDiffAt (T% A) x →
      MDiffAt (T% B) x → MDiffAt (fun y ↦ g₀ y (A y) (B y)) x)
    (hEin : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 2 (T% Z) →
      ∀ (hreg : DerivRegularAt cov Z x) (w : TangentSpace I x),
        ricciTraceAt cov hreg w = lam * g₀ x (Z x) w)
    (t₀ : ℝ) :
    IsRicciFlowSolutionAt
      (fun t ↦ fun y ↦ (1 - 2 * lam * t) • g₀ y) (fun _ ↦ cov) t₀ x where
  leviCivita t :=
    ⟨MetricCompatibleAt.const_smul (1 - 2 * lam * t) hLC.1 hP, hLC.2⟩
  flow {Z} hZ hreg w := by
    have hC : (fun t ↦ ((1 - 2 * lam * t) • g₀ x) (Z x) w) =
        fun t ↦ g₀ x (Z x) w - (2 * lam * (g₀ x (Z x) w)) * t := by
      funext t
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hC]
    have hder : HasDerivAt
        (fun t : ℝ ↦ g₀ x (Z x) w - (2 * lam * (g₀ x (Z x) w)) * t)
        (-(2 * lam * (g₀ x (Z x) w))) t₀ := by
      simpa using (hasDerivAt_const t₀ (g₀ x (Z x) w)).sub
        ((hasDerivAt_id t₀).const_mul (2 * lam * (g₀ x (Z x) w)))
    rw [hder.deriv, hEin hZ hreg w]
    ring

end CovariantDerivative

/-! ## Scale invariance of the Levi-Civita connection -/

section ScaleInvariance

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [I.Boundaryless]
variable {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
theorem scaled_symm
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (c : ℝ) (y : M) (v w : TangentSpace I y) :
    (c • g y) v w = (c • g y) w v := by
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hgsymm y v w]

theorem scaled_nondegenerate
    (hgnd : ∀ (y : M) (v : TangentSpace I y), (∀ w, g y v w = 0) → v = 0)
    {c : ℝ} (hc : c ≠ 0) (y : M)
    (v : TangentSpace I y) (hv : ∀ w, (c • g y) v w = 0) : v = 0 := by
  refine hgnd y v fun w ↦ ?_
  have h := hv w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hc

theorem scaled_pairing_mdiff
    (hP : ∀ (x : M) (A B : Π y : M, TangentSpace I y),
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ g y (A y) (B y)) x)
    (c : ℝ) (x : M)
    (A B : Π y : M, TangentSpace I y)
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    MDiffAt (fun y ↦ (c • g y) (A y) (B y)) x := by
  have h : (fun y ↦ (c • g y) (A y) (B y)) =
      fun y ↦ c * g y (A y) (B y) := by
    funext y
    simp
  rw [h]
  exact (hP x A B hA hB).const_smul c

/--
**Scale invariance of the Levi-Civita connection**: the canonical connection
of `c • g` agrees with that of `g` on differentiable fields, for `c ≠ 0`.
-/
theorem leviCivitaConnection_const_smul
    (hgsymm : ∀ (y : M) (v w : TangentSpace I y), g y v w = g y w v)
    (hgnd : ∀ (y : M) (v : TangentSpace I y), (∀ w, g y v w = 0) → v = 0)
    (hP : ∀ (x : M) (A B : Π y : M, TangentSpace I y),
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ g y (A y) (B y)) x)
    {c : ℝ} (hc : c ≠ 0)
    {Y : Π y : M, TangentSpace I y} {x : M} (hY : MDiffAt (T% Y) x) :
    leviCivitaConnection (fun y ↦ c • g y) (scaled_symm hgsymm c)
        (scaled_nondegenerate hgnd hc) (scaled_pairing_mdiff hP c) Y x =
      leviCivitaConnection g hgsymm hgnd hP Y x :=
  leviCivitaConnection_eq_of_isLeviCivita (fun y ↦ c • g y)
    (scaled_symm hgsymm c) (scaled_nondegenerate hgnd hc)
    (scaled_pairing_mdiff hP c)
    (leviCivitaConnection g hgsymm hgnd hP)
    (fun y ↦ MetricCompatibleAt.const_smul c
      (leviCivitaConnection_metricCompatibleAt g hgsymm hgnd hP y)
      (hP y))
    (fun y ↦ leviCivitaConnection_torsionFreeAt g hgsymm hgnd hP y) hY

end ScaleInvariance

/-! ## Extinction time of the shrinking Einstein family -/

namespace CovariantDerivative

/-- The extinction time of the Einstein scaling family `(1 - 2 lam t) g₀`. -/
noncomputable def einsteinExtinctionTime (lam : ℝ) : ℝ := 1 / (2 * lam)

theorem einstein_scaling_vanishes_at_extinctionTime {lam : ℝ}
    (hlam : lam ≠ 0) :
    1 - 2 * lam * einsteinExtinctionTime lam = 0 := by
  unfold einsteinExtinctionTime
  field_simp
  ring

/-- At the extinction time, the scaled Einstein metric vanishes
identically. -/
theorem einstein_scaling_metric_extinct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (g₀ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    {lam : ℝ} (hlam : lam ≠ 0) (x : M) (u w : TangentSpace I x) :
    ((1 - 2 * lam * einsteinExtinctionTime lam) • g₀ x) u w = 0 := by
  rw [einstein_scaling_vanishes_at_extinctionTime hlam]
  simp

/-- Past the extinction time of a shrinking (`lam > 0`) Einstein family,
the scaled form is negative on directions of positive length: the metric
property is destroyed in finite time. -/
theorem einstein_scaling_negative_past_extinction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (g₀ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    {lam t : ℝ} (hlam : 0 < lam)
    (ht : einsteinExtinctionTime lam < t)
    (x : M) {u : TangentSpace I x} (hu : 0 < g₀ x u u) :
    ((1 - 2 * lam * t) • g₀ x) u u < 0 := by
  have hfac : 1 - 2 * lam * t < 0 := by
    have h2 : 0 < 2 * lam := by linarith
    have ht' : 1 / (2 * lam) < t := ht
    have := (div_lt_iff₀ h2).mp ht'
    nlinarith
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact mul_neg_of_neg_of_pos hfac hu

end CovariantDerivative

/-! ## Parabolic rescaling of Ricci flow solutions -/

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/--
**Parabolic rescaling**: if `g(t)` is a Ricci flow solution then so is
`c · g(t/c)`, at the rescaled time — the fundamental symmetry behind
blow-up analysis of singularities.
-/
theorem IsRicciFlowSolutionAt.parabolic_rescale
    {g : ℝ → Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {covt : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
    {t₀ : ℝ} {x : M}
    (sol : IsRicciFlowSolutionAt g covt t₀ x) {c : ℝ} (hc : c ≠ 0)
    (hP : ∀ (t : ℝ) (A B : Π y : M, TangentSpace I y),
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ g t y (A y) (B y)) x) :
    IsRicciFlowSolutionAt (fun t ↦ fun y ↦ c • g (c⁻¹ * t) y)
      (fun t ↦ covt (c⁻¹ * t)) (c * t₀) x := by
  constructor
  · intro t
    exact ⟨MetricCompatibleAt.const_smul c
        (sol.leviCivita (c⁻¹ * t)).1
        (fun A B hA hB ↦ hP (c⁻¹ * t) A B hA hB),
      (sol.leviCivita (c⁻¹ * t)).2⟩
  · intro Z hZ
    rw [show c⁻¹ * (c * t₀) = t₀ from by field_simp]
    intro hreg w
    have hfun : (fun t ↦ ((fun y ↦ c • g (c⁻¹ * t) y) x) (Z x) w) =
        fun t ↦ c * ((fun s ↦ g s x (Z x) w) (c⁻¹ * t)) := by
      funext t
      simp
    rw [hfun, deriv_const_mul_field,
      deriv_comp_mul_left (f := fun s ↦ g s x (Z x) w) (c := c⁻¹),
      show c⁻¹ * (c * t₀) = t₀ from by field_simp, smul_eq_mul,
      show c * (c⁻¹ * deriv (fun s ↦ g s x (Z x) w) t₀) =
        deriv (fun s ↦ g s x (Z x) w) t₀ from by field_simp]
    exact sol.flow hZ hreg w


/--
**Static solutions are Ricci-flat**: a time-constant Ricci flow solution
has vanishing Ricci trace on `C²` admissible fields.
-/
theorem ricciTraceAt_eq_zero_of_static
    {g₀ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {t₀ : ℝ} {x : M}
    (sol : IsRicciFlowSolutionAt (fun _ ↦ g₀) (fun _ ↦ cov) t₀ x)
    {Z : Π y : M, TangentSpace I y} (hZ : CMDiff 2 (T% Z))
    (hreg : DerivRegularAt cov Z x) (w : TangentSpace I x) :
    ricciTraceAt cov hreg w = 0 := by
  have h := sol.flow hZ hreg w
  rw [deriv_const] at h
  linarith

/--
**Ricci-flat connections give static solutions**: a Levi-Civita connection
with vanishing Ricci trace makes the constant family a Ricci flow solution.
-/
theorem isRicciFlowSolutionAt_const_of_ricciFlat
    {g₀ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)} {x : M}
    (hLC : IsLeviCivitaAt g₀ cov x)
    (hric : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 2 (T% Z) →
      ∀ (hreg : DerivRegularAt cov Z x) (w : TangentSpace I x),
        ricciTraceAt cov hreg w = 0)
    (t₀ : ℝ) :
    IsRicciFlowSolutionAt (fun _ ↦ g₀) (fun _ ↦ cov) t₀ x where
  leviCivita _ := hLC
  flow hZ hreg w := by
    rw [deriv_const, hric hZ hreg w]
    ring


variable [T2Space M] [IsManifold I ∞ M] [I.Boundaryless]

/--
Scalar curvature scales inversely with the metric: with respect to `c • b`
the scalar curvature is `c⁻¹` times that with respect to `b`.
-/
theorem scalarCurvatureAt_const_smul
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1] {x : M}
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    {c : ℝ} (hc : c ≠ 0) (hb' : (c • b).Nondegenerate) :
    scalarCurvatureAt cov x (c • b) hb' =
      c⁻¹ * scalarCurvatureAt cov x b hb := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := ‹FiniteDimensional ℝ E›
  have hsymm : ∀ ψ : Module.Dual ℝ (TangentSpace I x),
      (LinearMap.BilinForm.toDual (c • b) hb').symm ψ =
        c⁻¹ • (LinearMap.BilinForm.toDual b hb).symm ψ := by
    intro ψ
    rw [LinearEquiv.symm_apply_eq]
    apply LinearMap.ext
    intro w
    rw [LinearMap.BilinForm.toDual_def]
    simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
    have hbw : b ((LinearMap.BilinForm.toDual b hb).symm ψ) w = ψ w := by
      have := LinearEquiv.apply_symm_apply
        (LinearMap.BilinForm.toDual b hb) ψ
      have h2 := congrArg (fun L ↦ L w) this
      simpa [LinearMap.BilinForm.toDual_def] using h2
    rw [hbw]
    field_simp
  have hcomp : (LinearMap.BilinForm.toDual (c • b) hb').symm.toLinearMap ∘ₗ
      ricciDualAt cov x =
      c⁻¹ • ((LinearMap.BilinForm.toDual b hb).symm.toLinearMap ∘ₗ
        ricciDualAt cov x) := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.smul_apply]
    exact hsymm (ricciDualAt cov x u)
  unfold scalarCurvatureAt
  rw [hcomp, map_smul, smul_eq_mul]


/--
The scalar curvature of the shrinking Einstein family at time `t`:
`Scal(t) = (1 - 2 lam t)⁻¹ * lam * dim`.
-/
theorem einstein_scaled_scalarCurvature
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1] {x : M}
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {lam : ℝ}
    (b : LinearMap.BilinForm ℝ (TangentSpace I x)) (hb : b.Nondegenerate)
    (hbg : ∀ v w : TangentSpace I x, b v w = g x v w)
    (hEin : IsEinsteinAt cov g lam x) {t : ℝ} (ht : 1 - 2 * lam * t ≠ 0)
    (hb' : ((1 - 2 * lam * t) • b).Nondegenerate) :
    scalarCurvatureAt cov x ((1 - 2 * lam * t) • b) hb' =
      (1 - 2 * lam * t)⁻¹ * (lam * Module.finrank ℝ E) := by
  rw [scalarCurvatureAt_const_smul b hb ht hb',
    scalarCurvatureAt_of_einstein cov g b hb hbg hEin]

/--
**Scalar curvature blows up at the extinction time**: for a shrinking
(`lam > 0`) Einstein family on a nontrivial space, the time-scalar
`(1 - 2 lam t)⁻¹ lam n` tends to `+∞` as `t` approaches the extinction
time from below.
-/
theorem einstein_scalar_tendsto_atTop [Nontrivial E] {lam : ℝ}
    (hlam : 0 < lam) :
    Filter.Tendsto
      (fun t : ℝ ↦ (1 - 2 * lam * t)⁻¹ * (lam * (Module.finrank ℝ E : ℝ)))
      (nhdsWithin (einsteinExtinctionTime lam)
        (Set.Iio (einsteinExtinctionTime lam))) Filter.atTop := by
  have hn : (0 : ℝ) < lam * (Module.finrank ℝ E : ℝ) := by
    have : 0 < Module.finrank ℝ E := Module.finrank_pos
    positivity
  have h1 : Filter.Tendsto (fun t : ℝ ↦ 1 - 2 * lam * t)
      (nhdsWithin (einsteinExtinctionTime lam)
        (Set.Iio (einsteinExtinctionTime lam)))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Filter.Tendsto (fun t : ℝ ↦ 1 - 2 * lam * t)
          (nhds (einsteinExtinctionTime lam))
          (nhds (1 - 2 * lam * einsteinExtinctionTime lam)) :=
        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
      rw [einstein_scaling_vanishes_at_extinctionTime (ne_of_gt hlam)] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : t < einsteinExtinctionTime lam := ht
      have h2 : 0 < 2 * lam := by linarith
      have ht2 : t < 1 / (2 * lam) := this
      have h3 := (lt_div_iff₀ h2).mp ht2
      simp only [Set.mem_Ioi]
      nlinarith
  exact (tendsto_inv_nhdsGT_zero.comp h1).atTop_mul_const hn


/--
A shrinking Einstein connection on a positive-definite metric has positive
Ricci curvature.
-/
theorem IsEinsteinAt.hasPosRicciAt
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1] {x : M}
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {lam : ℝ} (hEin : IsEinsteinAt cov g lam x) (hlam : 0 < lam)
    (hgpos : ∀ u : TangentSpace I x, u ≠ 0 → 0 < g x u u) :
    HasPosRicciAt cov x := by
  intro u hu
  rw [hEin u u]
  exact mul_pos hlam (hgpos u hu)


/-- The Einstein condition rescales: `Ric = lam g` gives
`Ric = (lam/c) (c g)`. -/
theorem IsEinsteinAt.const_smul
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1] {x : M}
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {lam : ℝ} (hEin : IsEinsteinAt cov g lam x) {c : ℝ} (hc : c ≠ 0) :
    IsEinsteinAt cov (fun y ↦ c • g y) (lam / c) x := by
  intro u w
  rw [hEin u w]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp

/--
**The Einstein condition propagates along the Einstein flow**: at time `t`
before extinction, the evolved metric `(1 - 2 lam t) g` is Einstein with
constant `lam / (1 - 2 lam t)` for the same connection.
-/
theorem IsEinsteinAt.flow_evolution
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1] {x : M}
    {g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {lam : ℝ} (hEin : IsEinsteinAt cov g lam x) {t : ℝ}
    (ht : 1 - 2 * lam * t ≠ 0) :
    IsEinsteinAt cov (fun y ↦ (1 - 2 * lam * t) • g y)
      (lam / (1 - 2 * lam * t)) x :=
  hEin.const_smul ht

/--
**The full affine symmetry of the Ricci flow**: composing time translation
and parabolic rescaling, every affine reparametrization `t ↦ c⁻¹ t + s` of a
solution (with metric scaled by `c`) is a solution.
-/
theorem IsRicciFlowSolutionAt.parabolic_reparam
    {g : ℝ → Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    {covt : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
    {t₀ : ℝ} {x : M}
    (sol : IsRicciFlowSolutionAt g covt t₀ x) {c : ℝ} (hc : c ≠ 0) (s : ℝ)
    (hP : ∀ (t : ℝ) (A B : Π y : M, TangentSpace I y),
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ g t y (A y) (B y)) x) :
    IsRicciFlowSolutionAt (fun t ↦ fun y ↦ c • g (c⁻¹ * t + s) y)
      (fun t ↦ covt (c⁻¹ * t + s)) (c * (t₀ - s)) x :=
  (sol.time_shift s).parabolic_rescale hc
    (fun t A B hA hB ↦ hP (t + s) A B hA hB)

end CovariantDerivative
