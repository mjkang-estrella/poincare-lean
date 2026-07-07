import Poincare.Global.CombinedFeed
import Poincare.Global.OrthogonalityFeed
import Poincare.Global.TheLocalIsometry

/-!
# Hosted payload boundary

This module records the M5-rigid-78 boundary without introducing a vacuous
wrapper theorem.

The requested one-common-time hosted package cannot currently be constructed
from the exported facts.  The first field that does not co-discharge is the
variation-flow field consumed by
`OrthogonalityFeed.source_transverse_horth_on_Icc_of_payload` and its target
analogue.

That theorem needs, for an open payload interval containing `0`,

```
hflow : forall tau in Ioo a b,
  HasDerivAt
    (fun s : R => alpha (anchor, v + s * w) tau) (Psi tau) 0
```

together with `h0 : 0 in Ioo a b`.  Since the speed-generic interval package
also has `hzero : 0 in Icc tmin tmax` and `hT : T in Icc tmin tmax`, the
natural hosted interval contains the path from `0` to the positive hosted time
`T`.  Feeding the existing orthogonality theorem therefore requires `hflow` on
an open interval with left endpoint strictly below `0`.

The available exported discharge,
`GeodesicTransport.chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`,
only proves the same variation derivative under
`ht : t in Icc 0 epsilon`.  The wrappers in
`SmoothDependenceDischarge` preserve this nonnegative-time restriction.  Thus
the current exports do not supply the negative-time part of the open-interval
payload demanded by `OrthogonalityFeed`.

Closing this boundary requires either an exported negative-time version of the
initial-velocity derivative, or a new one-sided integrated transverse Gauss
payload compatible with the speed-generic `Icc 0 T` interval.  Assuming the
displayed `hflow` here would be the missing payload field in different
notation, so no theorem is stated.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace HostedPayload

end HostedPayload
end Poincare
