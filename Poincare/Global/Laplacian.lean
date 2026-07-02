import Poincare.Global.Curvature

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

open Bundle FiberBundle
open scoped Manifold ContDiff

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

/--
The covariant Hessian of a scalar function at `x`:
`Hess f(v,w) = g(∇_v grad f, w)`.
-/
noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (v w : TM x) : ℝ :=
  g.inner x (g.leviCivita (g.gradient f) x v) w

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

theorem hessianAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) (v w : TM x) :
    g.hessianAt (fun _ : M ↦ c) x v w = 0 := by
  have hgrad : g.gradient (fun _ : M ↦ c) = 0 := g.gradient_const c
  unfold hessianAt
  rw [hgrad]
  simp

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

theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (x : M) :
    g.laplacianAt (fun _ : M ↦ c) x = 0 := by
  unfold laplacianAt
  rw [g.hessianDualAt_const c x]
  simp

end ClosedSmoothRiemannianMetric
end Poincare
