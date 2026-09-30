import Poincare.Global.SmoothInitialMetricLocalPullback
import Poincare.ChartTransport
import Poincare.Global.DeTurckCompactJetRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.DeTurckChartLift
abbrev E := ClosedSmoothModel 3
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
abbrev I := closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]

/-- The actual coordinate tensor pulled back through the forward preferred-chart differential. -/
def localPullback (anchor : M) (F : E → Bilin) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let A := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x
  ((ContinuousLinearMap.precomp (𝕜₁ := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (G := ℝ) A).comp (F (extChartAt I anchor x))).comp A

/-- A global actual tensor, zero off the genuine preferred-chart source. -/
def chartLift (anchor : M) (F : E → Bilin) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := by
  classical
  exact if x ∈ (extChartAt I anchor).source then localPullback anchor F x else 0

/-- The transported compact coefficient support in the original manifold. -/
def sourceSupport (anchor : M) (F : E → Bilin) : Set M :=
  (extChartAt I anchor).symm '' tsupport F

end Poincare.DeTurckChartLift
