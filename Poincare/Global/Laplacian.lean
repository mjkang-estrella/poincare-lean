import Poincare.Global.Curvature
import Poincare.ModelLaplacian

/-!
# Scalar gradients, Hessians, and Laplacians on closed smooth manifolds

This module specializes the scalar Laplacian infrastructure to a
`ClosedSmoothRiemannianMetric`.  It mirrors the trace pattern used for scalar
curvature: build a dual-valued Hessian, raise the dual index with the metric,
and take the trace.

The Hessian is defined as `g(∇ grad f, ·)` using the canonical
`g.leviCivita`.  Linearity theorems carry explicit differentiability
hypotheses for the gradient fields.  Ledger task `M1-lc-regularity` is
responsible for discharging those hypotheses from smoothness of `f` and the
canonical Levi-Civita construction.
-/

noncomputable section

open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u

namespace Poincare
namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

@[reducible] private def tangentFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TM x) :=
  (inferInstance : FiniteDimensional ℝ E)

@[reducible] private def tangentT2Space (x : M) :
    T2Space (TM x) :=
  (inferInstance : T2Space E)

omit [T2Space M] [IsManifold I ∞ M] in
private theorem extDerivFun_const (c : ℝ) (x : M) :
    (extDerivFun (fun _ : M ↦ c) x : TM x →L[ℝ] ℝ) = 0 := by
  unfold extDerivFun
  rw [(hasMFDerivAt_const c x).mfderiv]
  ext v
  simp

omit [T2Space M] in
private theorem extDerivFun_const_smul {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) :
    (extDerivFun (c • f) x : TM x →L[ℝ] ℝ) =
      c • (extDerivFun f x : TM x →L[ℝ] ℝ) := by
  ext v
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun _ : M ↦ c) (q := f) (x := x) mdifferentiableAt_const hf v
  simp [Pi.smul_apply, smul_eq_mul, extDerivFun_const] at hmul ⊢
  exact hmul

/-- The Riemannian gradient at a point, obtained by raising `df` with `g`. -/
noncomputable def gradientAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) : TM x :=
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  (LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)).symm
    (LinearMap.toContinuousLinearMap.symm
      (extDerivFun f x : TM x →L[ℝ] ℝ))

/-- The gradient vector field of a scalar function. -/
noncomputable def gradient (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) : ∀ x : M, TM x :=
  fun x ↦ g.gradientAt f x

/-- The defining property of `gradientAt`: pairing with the metric recovers `df`. -/
theorem inner_gradientAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (w : TM x) :
    g.inner x (g.gradientAt f x) w = extDerivFun f x w := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  unfold gradientAt
  let A :=
    LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)
  let ψ : Module.Dual ℝ (TM x) :=
    LinearMap.toContinuousLinearMap.symm
      (extDerivFun f x : TM x →L[ℝ] ℝ)
  have h : A (A.symm ψ) = ψ := LinearEquiv.apply_symm_apply A ψ
  have hw : (A (A.symm ψ)) w = ψ w :=
    congrArg (fun φ : Module.Dual ℝ (TM x) ↦ φ w) h
  change (g.metricBilinAt x) (A.symm ψ) w =
    (extDerivFun f x : TM x →L[ℝ] ℝ) w
  change (A (A.symm ψ)) w = ψ w
  exact hw

theorem gradientAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hEq : f =ᶠ[𝓝 x] h) :
    g.gradientAt f x = g.gradientAt h x := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  have hdf :
      (extDerivFun f x : TM x →L[ℝ] ℝ) =
        (extDerivFun h x : TM x →L[ℝ] ℝ) :=
    CovariantDerivative.extDerivFun_congr hEq
  unfold gradientAt
  rw [hdf]

theorem gradientAt_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    g.gradientAt (f + h) x = g.gradientAt f x + g.gradientAt h x := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  have hdf :
      (extDerivFun (f + h) x : TM x →L[ℝ] ℝ) =
        (extDerivFun f x : TM x →L[ℝ] ℝ) + extDerivFun h x := by
    simpa using (extDerivFun_add hf hh :
      extDerivFun (f + h) x = extDerivFun f x + extDerivFun h x)
  unfold gradientAt
  rw [hdf]
  simp

theorem gradient_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ}
    (hf : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) h x) :
    g.gradient (f + h) = g.gradient f + g.gradient h := by
  funext x
  exact g.gradientAt_add (hf x) (hh x)

theorem gradientAt_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    g.gradientAt (f * h) x =
      f x • g.gradientAt h x + h x • g.gradientAt f x := by
  apply sub_eq_zero.mp
  refine LeviCivitaExistence.metric_nondegenerate g x _ ?_
  intro w
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := f) (q := h) (x := x) hf hh w
  simp [map_sub, map_add, map_smul, inner_gradientAt, hmul, smul_eq_mul]
  ring

theorem gradient_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ}
    (hf : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) f x)
    (hh : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) h x) :
    g.gradient (f * h) = f • g.gradient h + h • g.gradient f := by
  funext x
  exact g.gradientAt_mul (hf x) (hh x)

theorem gradientAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    g.gradientAt (c • f) x = c • g.gradientAt f x := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  have hdf :
      (extDerivFun (c • f) x : TM x →L[ℝ] ℝ) =
        c • (extDerivFun f x : TM x →L[ℝ] ℝ) :=
    extDerivFun_const_smul hf c
  unfold gradientAt
  rw [hdf]
  simp

theorem gradient_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} (c : ℝ)
    (hf : ∀ x : M, MDifferentiableAt I 𝓘(ℝ) f x) :
    g.gradient (c • f) = c • g.gradient f := by
  funext x
  exact g.gradientAt_const_smul c (hf x)

theorem gradientAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) :
    g.gradientAt (fun _ : M ↦ c) x = 0 := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  unfold gradientAt
  rw [extDerivFun_const c x]
  simp

theorem gradient_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) :
    g.gradient (fun _ : M ↦ c) = 0 := by
  funext x
  exact g.gradientAt_const c x

/-- The pointwise squared norm of the scalar-curvature gradient. -/
noncomputable def scalarGradNormSqAt (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : ℝ :=
  g.inner x (g.gradientAt (fun y ↦ g.scalarAt y) x)
    (g.gradientAt (fun y ↦ g.scalarAt y) x)

/--
The metric gradient is differentiable at `x` whenever `f` is `C²` there.

In a chart around `x`, the gradient is the model field
`(Ghat z)⁻¹ (df_z)` for the smoothly blended chart metric `Ghat`.  This
model field is differentiable by smoothness of operator inversion and of
`df`, and the pulled-back field agrees locally with the intrinsic gradient by
the defining metric-duality property.
-/
theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
  haveI : ModelWithCorners.Boundaryless I := by infer_instance
  let G₀ : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v := by
    intro v hv
    change 0 < ((innerSL ℝ) v) v
    rw [innerSL_apply_apply]
    exact (real_inner_self_pos).2 hv
  obtain ⟨χ, hχ, hχ0, hχ1, hχsupp, hχone, _hχcanonical⟩ :=
    @CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x
  have hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm)
        (Set.range I) z).IsInvertible := by
    intro z hz
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hz)))
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  let Ghat : E → E →L[ℝ] E →L[ℝ] ℝ :=
    CovariantDerivative.blendedChartMetric χ G₀ g.inner x
  have hGhat : ContDiff ℝ 2 Ghat := by
    simpa [Ghat] using
      CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x
        htwo_add_one_le_top hχ hχsupp hg2
  have hGhatInv : ∀ z : E, (Ghat z).IsInvertible := by
    intro z
    exact CovariantDerivative.metric_isInvertible Ghat
      (CovariantDerivative.chartBilin χ G₀ g.inner x z)
      (CovariantDerivative.chartBilin_nondegenerate χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x hχ0 hχ1 hsupp z)
      (by intro v w; rfl)
  let F : E → ℝ := f ∘ (extChartAt I x).symm
  have hF : ContDiffAt ℝ 2 F (extChartAt I x x) := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [ModelWithCorners.range_eq_univ I, contDiffWithinAt_univ] at h
    have heq :
        (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I x).symm =
          f ∘ (extChartAt I x).symm := by
      funext z
      simp
    rw [heq] at h
    simpa [F] using h
  let V : ∀ z : E, TangentSpace 𝓘(ℝ, E) z :=
    fun z ↦ RicciFlow.RicciFlow.coordGradient Ghat F z
  have hVdiff : DifferentiableAt ℝ V (extChartAt I x x) := by
    have hInvDiff :
        DifferentiableAt ℝ (fun z : E => (Ghat z).inverse)
          (extChartAt I x x) :=
      (((hGhatInv (extChartAt I x x)).contDiffAt_map_inverse (n := 1)).differentiableAt
          one_ne_zero).comp (extChartAt I x x)
        ((hGhat.contDiffAt).differentiableAt (by norm_num))
    have hdfd : DifferentiableAt ℝ (fderiv ℝ F) (extChartAt I x x) :=
      ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    simpa [V, RicciFlow.RicciFlow.coordGradient] using hInvDiff.clm_apply hdfd
  have hVmdiff :
      MDifferentiableAt 𝓘(ℝ, E) ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (T% V)
        (extChartAt I x x) :=
    mdiffAt_vectorSpace_iff_differentiableAt.mpr hVdiff
  let W : ∀ y : M, TM y :=
    VectorField.mpullback I 𝓘(ℝ, E)
      ((extChartAt I x : PartialEquiv M E) : M → E) V
  have hChart :
      ContMDiffAt I 𝓘(ℝ, E) 2
        ((extChartAt I x : PartialEquiv M E) : M → E) x := by
    simpa only using (contMDiffAt_extChartAt :
      ContMDiffAt I 𝓘(ℝ, E) 2
        ((extChartAt I x : PartialEquiv M E) : M → E) x)
  have hChartInv :
      (mfderiv I 𝓘(ℝ, E)
        ((extChartAt I x : PartialEquiv M E) : M → E) x).IsInvertible := by
    exact (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x) :
      (mfderiv I 𝓘(ℝ, E)
        ((extChartAt I x : PartialEquiv M E) : M → E) x).IsInvertible)
  have hW :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% W) x := by
    simpa [W] using
      hVmdiff.mpullback_vectorField
        (f := ((extChartAt I x : PartialEquiv M E) : M → E))
        hChart hChartInv (by norm_num)
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ (extChartAt I x).source :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  have hχpre : ∀ᶠ y in 𝓝 x, χ (extChartAt I x y) = 1 :=
    (continuousAt_extChartAt x).eventually hχone
  have hf1 : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ) f y := by
    obtain ⟨u, hu, hfu⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hf
    filter_upwards [interior_mem_nhds.mpr hu] with y hy
    exact (((hfu.mono interior_subset) y hy).contMDiffAt
      (isOpen_interior.mem_nhds hy)).mdifferentiableAt two_ne_zero
  have hev : (T% (g.gradient f)) =ᶠ[𝓝 x] (T% W) := by
    filter_upwards [hsource, hχpre, hf1] with y hy hχy hfy
    have hgrad_eq : g.gradient f y = W y := by
      have hzero :
          g.gradient f y - W y = 0 :=
        LeviCivitaExistence.metric_nondegenerate g y
          (g.gradient f y - W y) (by
            intro w
            have hleft :
                g.inner y (g.gradient f y) w = extDerivFun f y w := by
              simpa [gradient] using g.inner_gradientAt f y w
            have hA :
                (mfderiv I 𝓘(ℝ, E)
                  ((extChartAt I x : PartialEquiv M E) : M → E) y)
                    (W y) = V (extChartAt I x y) := by
              have hInv :=
                isInvertible_mfderiv_extChartAt hy
              change
                (mfderiv I 𝓘(ℝ, E)
                    ((extChartAt I x : PartialEquiv M E) : M → E) y)
                  ((mfderiv I 𝓘(ℝ, E)
                    ((extChartAt I x : PartialEquiv M E) : M → E) y).inverse
                    (V (extChartAt I x y))) =
                  V (extChartAt I x y)
              exact hInv.self_apply_inverse _
            have hmetric :
                g.inner y (W y) w =
                  CovariantDerivative.chartMetric g.inner x
                    (extChartAt I x y) (V (extChartAt I x y))
                    ((mfderiv I 𝓘(ℝ, E)
                      ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := by
              have hchart := CovariantDerivative.chartMetric_apply_chart
                g.inner x hy (W y) w
              rw [← hchart, hA]
            have hGchart :
                Ghat (extChartAt I x y) =
                  CovariantDerivative.chartMetric g.inner x (extChartAt I x y) :=
              CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
                χ G₀ g.inner x hχy
            have hmodel :
                Ghat (extChartAt I x y) (V (extChartAt I x y))
                  ((mfderiv I 𝓘(ℝ, E)
                    ((extChartAt I x : PartialEquiv M E) : M → E) y) w) =
                    fderiv ℝ F (extChartAt I x y)
                      ((mfderiv I 𝓘(ℝ, E)
                        ((extChartAt I x : PartialEquiv M E) : M → E) y) w) :=
              RicciFlow.RicciFlow.g_coordGradient Ghat hGhatInv F (extChartAt I x y)
                ((mfderiv I 𝓘(ℝ, E)
                  ((extChartAt I x : PartialEquiv M E) : M → E) y) w)
            have hright :
                g.inner y (W y) w = extDerivFun f y w := by
              calc
                g.inner y (W y) w
                    = CovariantDerivative.chartMetric g.inner x
                        (extChartAt I x y) (V (extChartAt I x y))
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := hmetric
                _ = Ghat (extChartAt I x y) (V (extChartAt I x y))
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := by
                    rw [hGchart]
                _ = fderiv ℝ F (extChartAt I x y)
                        ((mfderiv I 𝓘(ℝ, E)
                          ((extChartAt I x : PartialEquiv M E) : M → E) y) w) := hmodel
                _ = extDerivFun f y w := by
                    symm
                    simpa [F] using
                      extDerivFun_apply_fixed_chart hy hfy w
            calc
              g.inner y (g.gradient f y - W y) w
                  = g.inner y (g.gradient f y) w - g.inner y (W y) w := by
                    simp only [map_sub, ContinuousLinearMap.sub_apply]
              _ = 0 := by rw [hleft, hright, sub_self])
      simpa using (sub_eq_zero.mp hzero)
    rw [hgrad_eq]
  exact hW.congr_of_eventuallyEq hev

/--
The covariant Hessian of a scalar function at `x`:
`Hess f(v,w) = g(∇_v grad f, w)`.
-/
noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (v w : TM x) : ℝ :=
  g.inner x (g.leviCivita (g.gradient f) x v) w

theorem hessianAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hEq : f =ᶠ[𝓝 x] h)
    (hgradf :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x)
    (v w : TM x) :
    g.hessianAt f x v w = g.hessianAt h x v w := by
  have hgradEq : ∀ᶠ y in 𝓝 x, g.gradient f y = g.gradient h y := by
    filter_upwards [hEq.eventually_nhds] with y hy
    exact g.gradientAt_congr_of_eventuallyEq hy
  have hcov :
    g.leviCivita (g.gradient f) x =
        g.leviCivita (g.gradient h) x :=
    g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgradf hgradh univ_mem hgradEq
  unfold hessianAt
  rw [hcov]

/-- The Hessian at `x` as a dual-valued linear map. -/
noncomputable def hessianDualAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) : TM x →ₗ[ℝ] Module.Dual ℝ (TM x) where
  toFun v :=
    { toFun := fun w ↦ g.hessianAt f x v w
      map_add' := by
        intro w w'
        simp [hessianAt]
      map_smul' := by
        intro c w
        simp [hessianAt, smul_eq_mul] }
  map_add' := by
    intro v v'
    ext w
    simp [hessianAt]
  map_smul' := by
    intro c v
    ext w
    simp [hessianAt, smul_eq_mul]

@[simp]
theorem hessianDualAt_apply (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (v w : TM x) :
    g.hessianDualAt f x v w = g.hessianAt f x v w :=
  rfl

/-- The Hessian at `x` as a continuous bilinear map on the tangent fiber. -/
noncomputable def hessianContinuousAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap :
        (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap) ∘ₗ
      g.hessianDualAt f x)

@[simp]
theorem hessianContinuousAt_apply (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (v w : TM x) :
    g.hessianContinuousAt f x v w = g.hessianAt f x v w := by
  simp [hessianContinuousAt]

theorem hessianDualAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hEq : f =ᶠ[𝓝 x] h)
    (hgradf :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.hessianDualAt f x = g.hessianDualAt h x := by
  ext v w
  exact g.hessianAt_congr_of_eventuallyEq hEq hgradf hgradh v w

/--
The scalar Laplacian at a point, defined as the metric trace of the covariant
Hessian.
-/
noncomputable def laplacianAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  LinearMap.trace ℝ (TM x)
    (((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm.toLinearMap) ∘ₗ
      g.hessianDualAt f x)

/--
The algebraic-dual Laplacian trace is the same trace obtained by converting the
continuous-bilinear Hessian back to algebraic duals.
-/
theorem laplacianAt_eq_trace_hessianContinuousAt
    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M) :
    g.laplacianAt f x =
      (letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
       letI : T2Space (TM x) := tangentT2Space x
       LinearMap.trace ℝ (TM x)
          (((LinearMap.BilinForm.toDual (g.metricBilinAt x)
              (g.metricBilinAt_nondegenerate x)).symm.toLinearMap) ∘ₗ
            (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
              ((g.hessianContinuousAt f x).toLinearMap)))) := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  unfold laplacianAt hessianContinuousAt
  congr 1

theorem laplacianAt_congr_of_eventuallyEq
    (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hEq : f =ᶠ[𝓝 x] h)
    (hgradf :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.laplacianAt f x = g.laplacianAt h x := by
  unfold laplacianAt
  rw [g.hessianDualAt_congr_of_eventuallyEq hEq hgradf hgradh]

/-- Leibniz rule for multiplying a vector field by a scalar function. -/
theorem leviCivita_smul_function (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {X : ∀ y : M, TM y} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hX : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% X) x)
    (v : TM x) :
    g.leviCivita (f • X) x v =
      f x • g.leviCivita X x v + extDerivFun f x v • X x := by
  have h := g.leviCivita.isCovariantDerivativeOnUniv.leibniz hX hf
  have hv := congrArg (fun L : TM x →L[ℝ] TM x ↦ L v) h
  simpa [ContinuousLinearMap.smulRight_apply] using hv

/--
Additivity of the Hessian in the scalar function.

The hypotheses `h∇f` and `h∇h` are carried for ledger task
`M1-lc-regularity`: smooth scalar functions should eventually provide the
needed differentiability of their metric-gradient vector fields.
-/
theorem hessianAt_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x)
    (v w : TM x) :
    g.hessianAt (f + h) x v w =
      g.hessianAt f x v w + g.hessianAt h x v w := by
  have hgrad : g.gradient (f + h) = g.gradient f + g.gradient h :=
    g.gradient_add hf hh
  unfold hessianAt
  rw [hgrad, g.leviCivita.isCovariantDerivativeOnUniv.add hgradf hgradh]
  simp

/--
Homogeneity of the Hessian in the scalar function.

The hypothesis `h∇f` is carried for ledger task `M1-lc-regularity`: smooth
scalar functions should eventually provide differentiability of their
metric-gradient vector fields.
-/
theorem hessianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (v w : TM x) :
    g.hessianAt (c • f) x v w = c * g.hessianAt f x v w := by
  have hgrad : g.gradient (c • f) = c • g.gradient f :=
    g.gradient_const_smul c hf
  unfold hessianAt
  rw [hgrad, g.leviCivita.isCovariantDerivativeOnUniv.smul_const c hgradf]
  simp [smul_eq_mul]

theorem hessianAt_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x)
    (v w : TM x) :
    g.hessianAt (f * h) x v w =
      f x * g.hessianAt h x v w + h x * g.hessianAt f x v w
        + extDerivFun f x v * extDerivFun h x w
        + extDerivFun h x v * extDerivFun f x w := by
  have hgrad : g.gradient (f * h) = f • g.gradient h + h • g.gradient f :=
    g.gradient_mul hf hh
  have hfgradh :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (f • g.gradient h)) x :=
    (hf x).smul_section hgradh
  have hhgradf :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (h • g.gradient f)) x :=
    (hh x).smul_section hgradf
  unfold hessianAt
  rw [hgrad, g.leviCivita.isCovariantDerivativeOnUniv.add hfgradh hhgradf]
  simp only [ContinuousLinearMap.add_apply]
  rw [g.leviCivita_smul_function (hf x) hgradh v,
    g.leviCivita_smul_function (hh x) hgradf v]
  simp [map_add, map_smul, gradient, inner_gradientAt, smul_eq_mul]
  ring_nf

theorem hessianContinuousAt_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.hessianContinuousAt (f * h) x =
      f x • g.hessianContinuousAt h x + h x • g.hessianContinuousAt f x
        + (extDerivFun f x).smulRight (extDerivFun h x)
        + (extDerivFun h x).smulRight (extDerivFun f x) := by
  ext v w
  rw [hessianContinuousAt_apply, g.hessianAt_mul hf hh hgradf hgradh]
  simp [hessianContinuousAt_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]

theorem hessianAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) (v w : TM x) :
    g.hessianAt (fun _ : M ↦ c) x v w = 0 := by
  have hgrad : g.gradient (fun _ : M ↦ c) = 0 := g.gradient_const c
  unfold hessianAt
  rw [hgrad]
  simp

/--
Symmetry of the covariant Hessian, assuming the gradient field has the
pointwise differentiability needed to apply torsion-freeness.
-/
theorem hessianAt_symm (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hgrad : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (v w : TM x) :
    g.hessianAt f x v w = g.hessianAt f x w v := by
  haveI : ModelWithCorners.Boundaryless I := by infer_instance
  let X : ∀ y : M, TM y := extend E v
  let Y : ∀ y : M, TM y := extend E w
  have hX : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% X) x := by
    simpa [X] using (mdifferentiableAt_extend (σ₀ := v) ..)
  have hY : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Y) x := by
    simpa [Y] using (mdifferentiableAt_extend (σ₀ := w) ..)
  have hXx : X x = v := by simp [X]
  have hYx : Y x = w := by simp [Y]
  have hpairX :
      (fun y : M => g.inner y ((g.gradient f) y) (X y)) =
        fun y : M => extDerivFun f y (X y) := by
    funext y
    simpa [gradient] using g.inner_gradientAt f y (X y)
  have hpairY :
      (fun y : M => g.inner y ((g.gradient f) y) (Y y)) =
        fun y : M => extDerivFun f y (Y y) := by
    funext y
    simpa [gradient] using g.inner_gradientAt f y (Y y)
  have hgrad_covY :
      g.inner x ((g.gradient f) x) (g.leviCivita Y x v) =
        extDerivFun f x (g.leviCivita Y x v) := by
    simpa [gradient] using g.inner_gradientAt f x (g.leviCivita Y x v)
  have hgrad_covX :
      g.inner x ((g.gradient f) x) (g.leviCivita X x w) =
        extDerivFun f x (g.leviCivita X x w) := by
    simpa [gradient] using g.inner_gradientAt f x (g.leviCivita X x w)
  have hcompatY :
      extDerivFun (fun y : M => extDerivFun f y (Y y)) x v =
        g.hessianAt f x v w + extDerivFun f x (g.leviCivita Y x v) := by
    have h := g.leviCivita_metricCompatibleAt x hgrad hY v
    rw [hpairY, hYx, hgrad_covY] at h
    simpa [hessianAt] using h
  have hcompatX :
      extDerivFun (fun y : M => extDerivFun f y (X y)) x w =
        g.hessianAt f x w v + extDerivFun f x (g.leviCivita X x w) := by
    have h := g.leviCivita_metricCompatibleAt x hgrad hX w
    rw [hpairX, hXx, hgrad_covX] at h
    simpa [hessianAt] using h
  have htangent :
      g.leviCivita Y x v - g.leviCivita X x w =
        VectorField.mlieBracket I X Y x := by
    have h := g.leviCivita_torsionFreeAt x hX hY
    simpa [hXx, hYx] using h
  have htorsion :
      extDerivFun f x (g.leviCivita Y x v) -
          extDerivFun f x (g.leviCivita X x w) =
        extDerivFun f x (VectorField.mlieBracket I X Y x) := by
    have h := congrArg (fun z : TM x => (extDerivFun f x : TM x →L[ℝ] ℝ) z)
      htangent
    simpa using h
  have hbracket :
      extDerivFun (fun y : M => extDerivFun f y (Y y)) x v -
          extDerivFun (fun y : M => extDerivFun f y (X y)) x w =
        extDerivFun f x (VectorField.mlieBracket I X Y x) := by
    have h := (extDerivFun_apply_mlieBracket (I' := I) hf hX hY).symm
    simpa [hXx, hYx] using h
  linarith

/-- Symmetry of the covariant Hessian from `C²` regularity of the scalar function alone. -/
theorem hessianAt_symm' (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TM x) :
    g.hessianAt f x v w = g.hessianAt f x w v :=
  g.hessianAt_symm hf (g.mdifferentiableAt_gradient hf) v w

theorem hessianDualAt_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.hessianDualAt (f + h) x =
      g.hessianDualAt f x + g.hessianDualAt h x := by
  ext v w
  exact g.hessianAt_add hf hh hgradf hgradh v w

theorem hessianDualAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    g.hessianDualAt (c • f) x = c • g.hessianDualAt f x := by
  ext v w
  simp [g.hessianAt_const_smul c hf hgradf v w, smul_eq_mul]

theorem hessianDualAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) :
    g.hessianDualAt (fun _ : M ↦ c) x = 0 := by
  ext v w
  simp [hessianAt_const]

/--
Additivity of the scalar Laplacian.

The gradient-field differentiability hypotheses are carried for ledger task
`M1-lc-regularity`.
-/
theorem laplacianAt_add (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x := by
  unfold laplacianAt
  rw [g.hessianDualAt_add hf hh hgradf hgradh]
  simp [LinearMap.comp_add]

/--
Additivity of the scalar Laplacian with the gradient-field regularity
discharged from pointwise `C²` scalar regularity.
-/
theorem laplacianAt_add' (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y)
    (hh : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 h y) :
    g.laplacianAt (f + h) x = g.laplacianAt f x + g.laplacianAt h x :=
  g.laplacianAt_add
    (fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (fun y ↦ (hh y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))
    (g.mdifferentiableAt_gradient (hh x))

/--
Homogeneity of the scalar Laplacian.

The gradient-field differentiability hypothesis is carried for ledger task
`M1-lc-regularity`.
-/
theorem laplacianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x) :
    g.laplacianAt (c • f) x = c * g.laplacianAt f x := by
  unfold laplacianAt
  rw [g.hessianDualAt_const_smul c hf hgradf]
  simp [LinearMap.comp_smul, smul_eq_mul]

/--
Homogeneity of the scalar Laplacian with the gradient-field regularity
discharged from pointwise `C²` scalar regularity.
-/
theorem laplacianAt_const_smul' (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M} (c : ℝ)
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y) :
    g.laplacianAt (c • f) x = c * g.laplacianAt f x :=
  g.laplacianAt_const_smul c
    (fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))

theorem laplacianAt_mul (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) f y)
    (hh : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) h y)
    (hgradf : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hgradh : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient h)) x) :
    g.laplacianAt (f * h) x =
      f x * g.laplacianAt h x + h x * g.laplacianAt f x
        + 2 * g.inner x (g.gradientAt f x) (g.gradientAt h x) := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  let A := (LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm.toLinearMap
  have hcross : ∀ φ ψ : TM x →L[ℝ] ℝ,
      LinearMap.trace ℝ (TM x)
        (A ∘ₗ
          (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
            ((φ.smulRight ψ).toLinearMap))) =
      φ ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm
          (LinearMap.toContinuousLinearMap.symm ψ)) := by
    intro φ ψ
    have hcomp : A ∘ₗ
        (LinearMap.toContinuousLinearMap.symm.toLinearMap.comp
          ((φ.smulRight ψ).toLinearMap)) =
        LinearMap.smulRight (φ.toLinearMap)
          ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
            (g.metricBilinAt_nondegenerate x)).symm
            (LinearMap.toContinuousLinearMap.symm ψ)) := by
      apply LinearMap.ext
      intro v
      have h1 : (φ.smulRight ψ).toLinearMap v = φ v • ψ := rfl
      simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
    rw [hcomp, LinearMap.trace_smulRight]
    rfl
  rw [g.laplacianAt_eq_trace_hessianContinuousAt (f * h) x,
    g.laplacianAt_eq_trace_hessianContinuousAt h x,
    g.laplacianAt_eq_trace_hessianContinuousAt f x]
  rw [g.hessianContinuousAt_mul hf hh hgradf hgradh]
  simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
    LinearMap.comp_add, LinearMap.comp_smul, map_add, map_smul, smul_eq_mul]
  have hT1 := hcross (extDerivFun f x) (extDerivFun h x)
  have hT2 := hcross (extDerivFun h x) (extDerivFun f x)
  rw [hT1, hT2]
  have hraise_h :
      ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm
          (LinearMap.toContinuousLinearMap.symm (extDerivFun h x))) =
        g.gradientAt h x := by
    unfold gradientAt
    rfl
  have hraise_f :
      ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x)).symm
          (LinearMap.toContinuousLinearMap.symm (extDerivFun f x))) =
        g.gradientAt f x := by
    unfold gradientAt
    rfl
  rw [hraise_h, hraise_f]
  rw [← g.inner_gradientAt f x (g.gradientAt h x),
    ← g.inner_gradientAt h x (g.gradientAt f x)]
  rw [g.inner_symm x (g.gradientAt h x) (g.gradientAt f x)]
  ring

theorem laplacianAt_mul' (g : ClosedSmoothRiemannianMetric n M)
    {f h : M → ℝ} {x : M}
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y)
    (hh : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 h y) :
    g.laplacianAt (f * h) x =
      f x * g.laplacianAt h x + h x * g.laplacianAt f x
        + 2 * g.inner x (g.gradientAt f x) (g.gradientAt h x) :=
  g.laplacianAt_mul
    (fun y ↦ (hf y).mdifferentiableAt two_ne_zero)
    (fun y ↦ (hh y).mdifferentiableAt two_ne_zero)
    (g.mdifferentiableAt_gradient (hf x))
    (g.mdifferentiableAt_gradient (hh x))

theorem laplacianAt_sq (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} {x : M}
    (hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 f y) :
    g.laplacianAt (fun y ↦ f y ^ 2) x =
      2 * f x * g.laplacianAt f x +
        2 * g.inner x (g.gradientAt f x) (g.gradientAt f x) := by
  have hfun : (fun y : M ↦ f y ^ 2) = f * f := by
    funext y
    simp [Pi.mul_apply, pow_two]
  rw [hfun, g.laplacianAt_mul' hf hf]
  ring

theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) :
    g.laplacianAt (fun _ : M ↦ c) x = 0 := by
  unfold laplacianAt
  rw [g.hessianDualAt_const c x]
  simp

end ClosedSmoothRiemannianMetric
end Poincare
