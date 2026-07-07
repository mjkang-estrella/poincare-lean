import Poincare.Global.CartanHomogeneity
import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.CartanIsometryPackage
import Poincare.Global.SmoothDependenceDischarge

/-!
# Cartan blocks final boundary

This module is intentionally theorem-free for M5-rigid-33.

`CartanHomogeneity` supplies the hosted small-velocity parameterization
`v = T • u` with cutoff-one PL data at `(u, T)`.  The current downstream
consumer in `CartanCoefficientBridge`, however, still hardcodes the
transverse factor as `CartanLocalIsometry.transverseScale v = sin ‖v‖ / ‖v‖`.
The hosted Jacobi data must be transported with the honest working-speed/time
scale coming from `(u, T)`.  Without either a theorem identifying that honest
scale with the bridge's hardcoded factor, or a generalized bridge parameterized
by that scale, any final local-isometry theorem here would still assume or
force the missing normalization.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanBlocksFinal

end CartanBlocksFinal
end Poincare
