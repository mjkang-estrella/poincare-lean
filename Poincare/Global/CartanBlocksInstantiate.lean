import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.CartanIsometryPackage
import Poincare.Global.GeodesicLengthFinal
import Poincare.Global.RoundSphereWitness
import Poincare.Global.TangentAlignmentExists

/-!
# Cartan block instantiation boundary

This module intentionally does not introduce a theorem-shaped wrapper around
`CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings`.
The bridge is already the correct downstream consumer.

The remaining missing exported interface is upstream of the bridge: a theorem
turning

```
v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source
```

into the cutoff-one PL/Jacobi endpoint package used by
`CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`,
`CartanIsometryPackage.actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique`,
`GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_orthogonal`,
and the endpoint derivative identifications in `CartanDifferential`.

Adding the final local-isometry theorem here without that implication would
amount to restating the bridge with its block hypotheses still assumed, not
instantiating the blocks.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanBlocksInstantiate

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

end CartanBlocksInstantiate
end Poincare
