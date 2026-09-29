# Exact source context for quotient-hessian

These excerpts record existing source at base 2da86427. Search and read nearest definitions/imports when using further symbols.

## Poincare/Global/Laplacian.lean:1-92

```lean
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
```

## Poincare/Global/Laplacian.lean:198-225

```lean
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
```

## Poincare/Global/Laplacian.lean:394-465

```lean

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

```

## Poincare/Global/IntrinsicBochnerScalarGradient.lean:174-198

```lean
    (ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two x f hs hf) v w

/-- The coordinate Hessian norm is the intrinsic metric trace of the squared
covariant derivative of the gradient, with the same basis and raised dual. -/
theorem coordCovariantHessNormSq_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (f : M → ℝ)
    (hs : tsupport f ⊆ (extChartAt (closedSmoothModelWithCorners 3) x).source)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    RicciFlow.RicciFlow.coordCovariantHessNormSq
      (anchorBlendedMetricFlow (fun _ ↦ g) x 0)
      (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) x f)
      (extChartAt (closedSmoothModelWithCorners 3) x x) =
    ∑ i, g.inner x
      (g.leviCivita (g.gradient f) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient f) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i))) := by
  unfold RicciFlow.RicciFlow.coordCovariantHessNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt (fun _ ↦ g) x 0 i,
    covariantDeriv_coordGradient_anchor g x f hs hf,
    covariantDeriv_coordGradient_anchor g x f hs hf, anchor_metric_apply]

/-- Trace the coordinate Hessian in the Euclidean basis using the inverse Gram matrix. -/
theorem curvedLaplacian_eq_inverseEntries_hessianForm
```

## Poincare/Global/HamiltonScalarGradientEstimate.lean:108-191

```lean
    (hS : IntrinsicBochnerScalarGradient.SatisfiesScalarGradientEvolutionAt gt t x)
    (hR : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x)
    (hRthree : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 (fun y ↦ (gt t).scalarAt y))
    (hRpos : ∀ y, 0 < (gt t).scalarAt y) :
    let g := gt t
    let R := fun y ↦ g.scalarAt y
    let S := fun y ↦ g.scalarGradNormSqAt y
    let H := ∑ i, g.inner x
      (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient R) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
    deriv (fun s ↦ (gt s).scalarGradNormSqAt x / (gt s).scalarAt x) t -
        g.laplacianAt (fun y ↦ S y / R y) x =
      -2 * H / R x +
        4 * g.inner x (g.gradientAt R x) (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) / R x -
        2 * S x * g.ricciNormSqAt x / R x ^ 2 -
        (4 / 3 : ℝ) * meanScalar g * (S x / R x) +
        2 * g.inner x (g.gradientAt R x) (g.gradientAt S x) / R x ^ 2 -
        2 * S x ^ 2 / R x ^ 3 := by
  have hS₂ : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun z ↦ (gt t).scalarGradNormSqAt z) y :=
    IntrinsicBochnerScalarGradient.gradientNormSq_contMDiffAt_two (gt t) _ hRthree
  have hR₂ : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (fun z ↦ (gt t).scalarAt z) y :=
    fun y ↦ hRthree.contMDiffAt.of_le (by norm_num)
  have he := heatOperator_div_expanded (gt t) x hS hR hS₂ hR₂
    (fun y ↦ (hRpos y).ne')
  dsimp only
  rw [he]
  unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
  field_simp (discharger := first | exact (hRpos x).ne' | norm_num)
  ring

variable [SecondCountableTopology M]

/-- Joint fifth-order metric entries supply all scalar regularity for the quotient identity. -/
theorem scalarGradientQuotient_evolution_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint5 : ∀ s y, MetricEntriesJointContDiffAt gt s y 5)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hRpos : ∀ y, 0 < (gt t).scalarAt y) :
    let g := gt t
    let R := fun y ↦ g.scalarAt y
    let S := fun y ↦ g.scalarGradNormSqAt y
    let H := ∑ i, g.inner x
      (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient R) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
    deriv (fun s ↦ (gt s).scalarGradNormSqAt x / (gt s).scalarAt x) t -
        g.laplacianAt (fun y ↦ S y / R y) x =
      -2 * H / R x +
        4 * g.inner x (g.gradientAt R x) (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) / R x -
        2 * S x * g.ricciNormSqAt x / R x ^ 2 -
        (4 / 3 : ℝ) * meanScalar g * (S x / R x) +
        2 * g.inner x (g.gradientAt R x) (g.gradientAt S x) / R x ^ 2 -
        2 * S x ^ 2 / R x ^ 3 := by
  letI : Nonempty M := ⟨x⟩
  exact scalarGradientQuotient_evolution x
    (IntrinsicBochnerScalarGradient.satisfiesScalarGradientEvolutionAt_of_normalizedFlow
      hJoint5 hFlow)
    (satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
        (fun s y ↦ (hJoint5 s y).of_le (by norm_num))))
    (IntrinsicBochnerScalarGradient.scalar_contMDiff_three_of_metricEntries_five hJoint5 t)
    hRpos

/-- The factor-three trace estimate removes the derivative term, with no strict damping. -/
theorem tracelessEnergy_evolution_le_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint : ∀ s y, MetricEntriesJointContDiffAt gt s y 3)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y) :
    deriv (fun s ↦ (gt s).tracelessRicciNormSqAt x) t -
        (gt t).laplacianAt (fun y ↦ (gt t).tracelessRicciNormSqAt y) x ≤
      (gt t).pinchingTracelessRicciReactionTrace3At x
        ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) -
        (4 / 3 : ℝ) * meanScalar (gt t) * (gt t).tracelessRicciNormSqAt x := by
  letI : Nonempty M := ⟨x⟩
  have hd :=
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
      (x := x) hFlow hJoint
  rw [hd.deriv]
  dsimp only [normalizedTracelessRicciEvolutionReactionAt]
  have hb := (gt t).scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
  linarith

```
