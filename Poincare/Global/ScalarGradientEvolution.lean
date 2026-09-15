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

end Poincare.ScalarGradientEvolution
