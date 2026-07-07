import Poincare.Global.RayIdentification
import Poincare.Global.OrthogonalityFeed
import Poincare.Global.TheLocalIsometry

/-!
# Final Cartan isometry discharge boundary

This module is intentionally theorem-free for M5-rigid-75.

The final consumer

`CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_corrected_radial_decomposed_blocks`

cannot be instantiated from the currently exported radial facts without an
extra radial coefficient-to-rescaled-pairing bridge.

The exported radial endpoint theorem gives the coefficient-product form

`(radialCoeff B v a * radialCoeff B v a') * plainRadialScale speed T`.

The consumer requires the rescaled-anchor form

`plainRadialScale speed T *
  B (T^-1 • radialPart B v a) (T^-1 • radialPart B v a')`.

For hosted data, `SpeedPackage` identifies `speed ^ 2` with
`B (T^-1 • v) (T^-1 • v)`.  Therefore the rescaled-anchor form contains an
additional factor of `speed ^ 2` relative to the exported coefficient-product
radial theorem, unless an explicit unit-speed normalization or a corrected
radial consumer scalar is supplied.

No wrapper theorem is stated here, because assuming that bridge would be the
unfed hypothesis in different notation.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace IsometryFinal

end IsometryFinal
end Poincare
