/-
The Ricci flow equation, with content.

This module states the Ricci flow equation `∂g/∂t = -2 Ric(g)` against the
genuine curvature objects of this development: each time slice carries a
Levi-Civita connection (pointwise metric compatibility and torsion-freeness),
and the time derivative of the metric on a `C²` field is `-2` times the Ricci
trace of the curvature of that connection.  Unlike the legacy
`SatisfiesRicciFlowEquation` interfaces of this repository, every ingredient
here is the real mathematical object.

It then verifies the first solution: Euclidean space with its constant metric
and flat Levi-Civita connection is a static Ricci flow (`Ric = 0`).
-/

import Poincare.FlatModelConnection
import Poincare.LeviCivitaUniqueness

noncomputable section

open Bundle Set FiberBundle
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace CovariantDerivative

variable (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
variable [IsManifold I 1 M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/--
A connection is Levi-Civita for `g` at `x` iff it is metric-compatible and
torsion-free there.
-/
def IsLeviCivitaAt (x : M) : Prop :=
  MetricCompatibleAt g cov x ∧ TorsionFreeAt cov x

variable [IsManifold I 2 M] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Ricci flow equation at a time `t₀` and point `x`, with content: each time
slice carries a Levi-Civita connection for its metric, and the time
derivative of the metric paired with a `C²` field and a tangent vector is
`-2` times the Ricci trace of the slice connection.
-/
structure IsRicciFlowSolutionAt
    (g : ℝ → Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _))
    (t₀ : ℝ) (x : M) : Prop where
  leviCivita : ∀ t : ℝ, IsLeviCivitaAt (g t) (cov t) x
  flow : ∀ {Z : Π y : M, TangentSpace I y}, CMDiff 2 (T% Z) →
    ∀ (hreg : DerivRegularAt (cov t₀) Z x) (w : TangentSpace I x),
      deriv (fun t ↦ g t x (Z x) w) t₀ =
        -2 * ricciTraceAt (cov t₀) hreg w

end CovariantDerivative

/-! ## Euclidean space is a static Ricci flow -/

open CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- The Euclidean metric as a fibrewise metric on the tangent bundle. -/
def euclideanBundleMetric :
    Π y : F, TangentSpace 𝓘(ℝ, F) y →L[ℝ] TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ :=
  fun _ ↦ (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
/-- The flat connection is metric-compatible with the Euclidean metric. -/
theorem flat_metricCompatibleAt (x : F) :
    MetricCompatibleAt euclideanBundleMetric
      (flatCovariantDerivative ℝ F) x := by
  intro Y Z hY hZ v
  have hY' := mdiffAt_vectorSpace_iff_differentiableAt.mp hY
  have hZ' := mdiffAt_vectorSpace_iff_differentiableAt.mp hZ
  have hcompat := flatCovariantDerivative_inner_compatible
    (Y := (Y : F → F)) (Z := (Z : F → F)) hY' hZ' v
  calc extDerivFun (fun y ↦ euclideanBundleMetric y (Y y) (Z y)) x v
      = fderiv ℝ (fun y ↦ @inner ℝ F _ (Y y) (Z y)) x v := by
        simp only [extDerivFun, mfderiv_eq_fderiv,
          ContinuousLinearMap.comp_apply]
        rfl
    _ = @inner ℝ F _ (Z x) (flatCovariantDerivative ℝ F Y x v)
        + @inner ℝ F _ (Y x) (flatCovariantDerivative ℝ F Z x v) := hcompat
    _ = euclideanBundleMetric x (flatCovariantDerivative ℝ F Y x v) (Z x)
        + euclideanBundleMetric x (Y x) (flatCovariantDerivative ℝ F Z x v) :=
        congrArg₂ (· + ·) (real_inner_comm _ _) rfl

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
/-- The flat connection is torsion-free at every point. -/
theorem flat_torsionFreeAt (x : F) :
    TorsionFreeAt (flatCovariantDerivative ℝ F) x := by
  intro X Y hX hY
  rw [mlieBracket_vectorSpace_eq]
  rfl

/-- The flat connection is Levi-Civita for the Euclidean metric. -/
theorem flat_isLeviCivitaAt (x : F) :
    IsLeviCivitaAt euclideanBundleMetric (flatCovariantDerivative ℝ F) x :=
  ⟨flat_metricCompatibleAt x, flat_torsionFreeAt x⟩

/-- The Ricci trace of the flat connection vanishes on `C²` fields. -/
theorem flat_ricciTraceAt_eq_zero
    {Z : Π y : F, TangentSpace 𝓘(ℝ, F) y} (hZcd : ContDiff ℝ 2 (Z : F → F))
    {x : F}
    (hreg : DerivRegularAt (flatCovariantDerivative ℝ F) Z x)
    (w : TangentSpace 𝓘(ℝ, F) x) :
    ricciTraceAt (flatCovariantDerivative ℝ F) hreg w = 0 := by
  have hcurv : curvatureEndAt (flatCovariantDerivative ℝ F) hreg w = 0 := by
    apply LinearMap.ext
    intro v
    rw [curvatureEndAt_apply]
    unfold curvatureTensorAt
    rw [TensorialAt.mkHom₂_apply_eq_extend]
    rw [flatCovariantDerivative_curvatureOp_eq_zero]
    · rfl
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp
        (mdifferentiableAt_extend ..)
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp
        (mdifferentiableAt_extend ..)
    · exact ((hZcd.contDiffAt (x := x)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero
    · exact (hZcd.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  unfold ricciTraceAt
  rw [hcurv, map_zero]

/--
**Euclidean space is a static solution of the Ricci flow.**  The constant
Euclidean metric with the flat Levi-Civita connection satisfies the Ricci
flow equation at every time and point.
-/
theorem euclidean_static_isRicciFlowSolutionAt (t₀ : ℝ) (x : F) :
    IsRicciFlowSolutionAt (fun _ ↦ euclideanBundleMetric)
      (fun _ ↦ flatCovariantDerivative ℝ F) t₀ x where
  leviCivita _ := flat_isLeviCivitaAt x
  flow hZ hreg w := by
    have hZcd : ContDiff ℝ 2 (_ : F → F) :=
      contMDiff_vectorSpace_iff_contDiff.mp hZ
    rw [deriv_const, flat_ricciTraceAt_eq_zero hZcd hreg w]
    ring

/-! ## Canonical Ricci values of the flat connection -/

open FiberBundle in
/-- On the model space, the canonical extension of a tangent vector is the
constant section. -/
theorem extend_model_space {x : F} (w : TangentSpace 𝓘(ℝ, F) x) :
    extend F w = fun _ ↦ (w : F) := by
  funext x'
  simp only [FiberBundle.extend]
  rw [← Trivialization.symmL_apply ℝ, TangentBundle.symmL_model_space]
  simp
  rfl

open FiberBundle in
/-- Extended sections are admissible for the flat connection. -/
theorem flat_derivRegularAt_extend {x : F} (w : TangentSpace 𝓘(ℝ, F) x) :
    DerivRegularAt (flatCovariantDerivative ℝ F) (extend F w) x := by
  intro W hW
  rw [mdiffAt_vectorSpace_iff_differentiableAt]
  have hS : (fun y ↦ flatCovariantDerivative ℝ F (extend F w) y (W y)) =
      fun _ ↦ (0 : F) := by
    funext y
    rw [extend_model_space w]
    simp
    rfl
  rw [hS]
  exact differentiableAt_const _

open FiberBundle in
/--
**The canonical Ricci values of Euclidean space vanish**: the Ricci trace of
the flat connection against any canonical extension is zero.
-/
theorem flat_ricciTraceAt_extend_eq_zero {x : F}
    (w u : TangentSpace 𝓘(ℝ, F) x)
    (hreg : DerivRegularAt (flatCovariantDerivative ℝ F) (extend F w) x) :
    ricciTraceAt (flatCovariantDerivative ℝ F) hreg u = 0 := by
  apply flat_ricciTraceAt_eq_zero
  rw [extend_model_space w]
  exact contDiff_const
