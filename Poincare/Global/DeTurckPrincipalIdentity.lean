import Poincare.Global.DeTurckPrincipalSecondJet

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100

noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology BigOperators NNReal

namespace Poincare.DeTurckPrincipalIdentity
open DeTurckPrincipalSecondJet DeTurckCoordinateJointRegularity

/-- The Koszul covector constructed directly from a first metric jet. -/
def koszul (J : Jet1) (u v : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (J u v + J v u - (J.flip u).flip v)

/-- The coordinate connection constructed directly from the metric value and first jet. -/
def connection (G : Bilin) (J : Jet1) (u v : E) : E :=
  G.inverse (koszul J v u)

/-- Evaluation of the Koszul covector uses only the three first-jet slots. -/
theorem koszul_apply (J : Jet1) (u v q : E) :
    koszul J u v q = (1 / 2 : ℝ) * (J u v q + J v u q - J q u v) := by
  rfl

end Poincare.DeTurckPrincipalIdentity
