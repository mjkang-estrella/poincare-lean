/-
Curvature conditions.

With the genuine Ricci tensor and scalar curvature available, the classical
curvature hypotheses of geometric analysis (Einstein metrics, Ricci
positivity, positive scalar curvature) become stateable with content.  The
flat model realizes the degenerate cases.
-/

import Poincare.EuclideanLeviCivitaCheck

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

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
