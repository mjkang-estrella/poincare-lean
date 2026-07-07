import Poincare.Global.BundleDischarge
import Poincare.Global.CartanCascade
import Poincare.Global.IsometryInstantiate
import Poincare.Global.SolutionsFeed
import Poincare.Global.SpeedReconcile
import Poincare.Global.TheLocalIsometry

/-!
# Cartan isometry assembly boundary

This module records the M5-rigid-86 retry boundary.

The `hplLinear` obstruction isolated in `TheIsometry.lean` is gone from the
transverse-transverse feed after `SolutionsFeed`: endpoint additivity from the
hosted solution family replaces the old centered linearized package.

The remaining public exports still do not provide one common hosted datum for
the assembly consumer

`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`.

The first source-side field that cannot be fed for the same hosted curve
produced by `CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`
is the base-flow derivative required by
`SolutionsFeed.source_transverseTransverse_of_solutions_feed`:

```lean
(hγ : ∀ s ∈ Icc tmin tmax,
  HasDerivAt γ
    (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
```

For the cascade source curve

```lean
γ = αs (extChartAt I x₀ x₀, Ts⁻¹ • v)
```

the exported cascade package returns endpoint linearity and the strict
derivative conditional through the linearized family, but it does not export
the corresponding base-curve `HasDerivAt` field, nor the target-membership,
cutoff-one, speed, or norm-membership fields consumed by `SolutionsFeed`.

The closest reusable adapter is
`IsometryInstantiate.hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc`,
but applying it at the cascade endpoint would require a strictly interior
margin such as `Ts < εs`; the cascade theorem exports only

```lean
Ts ≤ εs
```

and does not export the base `HasDerivWithinAt` hypothesis for `αs` either.
The cutoff-one speed/ray packages expose such base-flow data for their own
hosted flow package, but the current public API does not identify that package
with the opaque cascade `αs`/`αt` used to build the endpoint-linear `Ψ`s and
strict derivatives.

Consequently a curvature-only `cartanMap_isLocalIsometry` theorem would still
have to assume this common hosted package in different notation.  No theorem is
stated here.
-/

noncomputable section

namespace Poincare
namespace IsometryAssembly

end IsometryAssembly
end Poincare
