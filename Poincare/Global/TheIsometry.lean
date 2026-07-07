import Poincare.Global.BoundedPackage
import Poincare.Global.BundleDischarge
import Poincare.Global.CartanCascade
import Poincare.Global.LinearizedAdditivity

/-!
# Cartan local-isometry assembly boundary

M5-rigid-84 was intended to assemble the curvature-only theorem
`cartanMap_isLocalIsometry` by instantiating all source, target, radial, mixed,
and transverse feeds at one hosted datum.

The final consumer is available:
`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`.
The bounded transverse-transverse feed is also available, but its public
interface still requires a centered linearized Picard-Lindelof package
uniformly for every pair of endpoint directions:

```
(hplLinear : forall w w' : E3,
  IsPicardLindelof ... ((0 : E3), T^-1 • (w + w')) aLin rLin LipLin KLin)
```

The currently exported hosted linearized-family API consumes a single
zero-centered package and exports the rescaled family, endpoint additivity, and
endpoint homogeneity. It does not export this all-direction centered package,
nor the accompanying centered closed-ball membership hypotheses required by
`BoundedPackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall`
and its target analogue.

No theorem is stated here: adding a curvature-only wrapper would be vacuous
until that centered package is exported.
-/

noncomputable section

namespace Poincare

namespace TheIsometry

end TheIsometry

end Poincare
