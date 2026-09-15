import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.IntrinsicLaplacianCoordinateForm

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

set_option autoImplicit false

universe u

namespace Poincare.ScalarGradientEvolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Differentiate the squared norm of a moving covector with the moving
inverse metric. The metric variation has a negative sign. -/
theorem hasDerivAt_covectorNormSq
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    {α : ℝ → TM x →L[ℝ] ℝ} {α' : TM x →L[ℝ] ℝ}
    (hα : HasDerivAt α α' t₀) :
    HasDerivAt (fun t ↦ α t ((gt t).metricRaiseContinuousAt x (α t)))
      (2 * α' ((gt t₀).metricRaiseContinuousAt x (α t₀)) -
        timeDerivAt gt t₀ x
          ((gt t₀).metricRaiseContinuousAt x (α t₀))
          ((gt t₀).metricRaiseContinuousAt x (α t₀))) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  have hd := hα.clm_apply
    ((hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt hgt).clm_apply hα)
  apply hd.congr_deriv
  simp only [map_add]
  have hswap (v : TM x) :
      α t₀ v = (gt t₀).inner x v
        ((gt t₀).metricRaiseContinuousAt x (α t₀)) := by
    rw [(gt t₀).inner_symm]
    exact ((gt t₀).metricRaiseContinuousAt_inner_apply x (α t₀) v).symm
  rw [hswap (metricRaiseDerivAt gt t₀ x hgt (α t₀)),
    metricRaiseDerivAt_inner_apply hgt,
    hswap ((gt t₀).metricRaiseContinuousAt x α'),
    ClosedSmoothRiemannianMetric.metricRaiseContinuousAt_inner_apply]
  ring

/-- The moving-gradient norm rule, expressed using the derivative of `df`. -/
theorem hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    {f : ℝ → M → ℝ} {f' : M → ℝ}
    (hdf : HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
      (extDerivFun f' x) t₀) :
    HasDerivAt
      (fun t ↦ (gt t).inner x ((gt t).gradientAt (f t) x)
        ((gt t).gradientAt (f t) x))
      (2 * (gt t₀).inner x ((gt t₀).gradientAt f' x)
          ((gt t₀).gradientAt (f t₀) x) -
        timeDerivAt gt t₀ x ((gt t₀).gradientAt (f t₀) x)
          ((gt t₀).gradientAt (f t₀) x)) t₀ := by
  have h := hasDerivAt_covectorNormSq hgt hdf
  have heq (g : ClosedSmoothRiemannianMetric n M) (u : M → ℝ) :
      g.metricRaiseContinuousAt x (extDerivFun u x) = g.gradientAt u x := rfl
  simp_rw [heq] at h
  simpa only [ClosedSmoothRiemannianMetric.inner_gradientAt] using h

omit [T2Space M] [IsManifold I ∞ M] in
/-- Joint second-order scalar regularity commutes the time derivative and
the manifold differential in a fixed tangent fiber. -/
theorem hasDerivAt_extDerivFun_of_joint_contDiffAt_two
    {f : ℝ → M → ℝ} {t₀ : ℝ} {x : M}
    (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) (f t) x)
    (hft : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ deriv (fun t ↦ f t y) t₀) x)
    (hJoint : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ f p.1 ((extChartAt I x).symm p.2))
      (t₀, extChartAt I x x)) :
    HasDerivAt (fun t ↦ (extDerivFun (f t) x : TM x →L[ℝ] ℝ))
      (extDerivFun (fun y ↦ deriv (fun t ↦ f t y) t₀) x) t₀ := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  apply RicciFlow.RicciFlow.hasDerivAt_clm_of_forall_apply'
  intro v
  simp_rw [extDerivFun_apply_chart (hf _), extDerivFun_apply_chart hft]
  exact hasDerivAt_spatial_fderiv_of_joint_contDiffAt_two
    (fun t z ↦ f t ((extChartAt I x).symm z)) t₀ (extChartAt I x x) v hJoint

section Normalized

variable {N : Type u} [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [CompactSpace N] [ConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

local notation "I₃" => closedSmoothModelWithCorners 3
local notation "E₃" => ClosedSmoothModel 3

/-- Pointwise time variation of the scalar-gradient norm along normalized
flow. The joint scalar and Laplacian hypotheses are explicit regularity
requirements beyond the supplied joint metric entries. -/
theorem hasDerivAt_scalarGradNormSq_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 N} {t₀ : ℝ} {x : N}
    (hJoint : ∀ t y, MetricEntriesJointContDiffAt gt t y 3)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hScalarJoint : ContDiffAt ℝ 2
      (fun p : ℝ × E₃ ↦ (gt p.1).scalarAt ((extChartAt I₃ x).symm p.2))
      (t₀, extChartAt I₃ x x))
    (hLap : MDifferentiableAt I₃ 𝓘(ℝ)
      (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) :
    HasDerivAt (fun t ↦ (gt t).scalarGradNormSqAt x)
      (2 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt
            (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x) +
        4 * (gt t₀).inner x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x) +
        2 * (gt t₀).ricciAt x ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x)
          ((gt t₀).gradientAt (fun y ↦ (gt t₀).scalarAt y) x) -
        2 * meanScalar (gt t₀) * (gt t₀).scalarGradNormSqAt x) t₀ := by
  letI : Nonempty N := ⟨x⟩
  let g := gt t₀
  let R : N → ℝ := fun y ↦ g.scalarAt y
  let A : N → ℝ := fun y ↦ g.ricciNormSqAt y
  let L : N → ℝ := fun y ↦ g.laplacianAt R y
  let c : ℝ := -(2 / 3 : ℝ) * meanScalar g
  have hR : MDifferentiableAt I₃ 𝓘(ℝ) R x := scalarAt_mdifferentiableAt g x
  have hA : MDifferentiableAt I₃ 𝓘(ℝ) A x := ricciNormSqAt_mdifferentiableAt g x
  have hL : MDifferentiableAt I₃ 𝓘(ℝ) L x := hLap
  have heq : (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) =
      L + (2 : ℝ) • A + c • R := by
    funext y
    have hs : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ y :=
      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
        hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
    rw [hs.deriv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, L, A, R, c, g]
    ring
  have h2A : MDifferentiableAt I₃ 𝓘(ℝ) ((2 : ℝ) • A) x := by
    exact mdifferentiableAt_const.smul hA
  have hcR : MDifferentiableAt I₃ 𝓘(ℝ) (c • R) x := by
    exact mdifferentiableAt_const.smul hR
  have hft : MDifferentiableAt I₃ 𝓘(ℝ)
      (fun y ↦ deriv (fun t ↦ (gt t).scalarAt y) t₀) x := by
    rw [heq]
    exact (hL.add h2A).add hcR
  have hd := hasDerivAt_gradientNormSq_of_hasDerivAt_extDerivFun
    (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint t₀ x).of_le (by norm_num)))
    (hasDerivAt_extDerivFun_of_joint_contDiffAt_two
      (fun t ↦ scalarAt_mdifferentiableAt (gt t) x) hft hScalarJoint)
  rw [heq, g.gradientAt_add (hL.add h2A) hcR,
    g.gradientAt_add hL h2A,
    g.gradientAt_const_smul 2 hA, g.gradientAt_const_smul c hR] at hd
  apply hd.congr_deriv
  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
    (hFlow x)]
  simp only [normalizedRicciFlowRHSAt, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [ClosedSmoothRiemannianMetric.scalarGradNormSqAt, R, A, L, c, g]
  rw [(gt t₀).inner_symm x ((gt t₀).gradientAt
    (fun y ↦ (gt t₀).laplacianAt (fun z ↦ (gt t₀).scalarAt z) y) x),
    (gt t₀).inner_symm x ((gt t₀).gradientAt (fun y ↦ (gt t₀).ricciNormSqAt y) x)]
  ring

end Normalized

end Poincare.ScalarGradientEvolution
