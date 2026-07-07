import Poincare.Global.BundleDischarge
import Poincare.Global.CartanEquivUpgrade
import Poincare.Global.UniformFlowExport

/-!
# Local isometry theorem assembly boundary

This module records the M5-rigid-99 final assembly boundary.

`UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`
now exports the common selector datum, concrete source/target linearized
Picard-Lindelof witnesses, strict endpoint derivatives, and both ray identities
at the same time `T`.  The downstream source and target transverse blocks are
available through `AssemblyDone`, and the final pointwise consumer is
`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`.

The first final-consumer witness that is not exported by the public selector
datum is the upgrade from the selected endpoint continuous linear maps to
continuous linear equivalences:

```lean
{A B : E3 ≃L[ℝ] E3}
(hA :
  (A : E3 →L[ℝ] E3) =
    linearizedEndpointCLM (Ψ := PsiS) T hadds hsmuls)
(hB :
  (B : E3 →L[ℝ] E3) =
    linearizedEndpointCLM (Ψ := PsiT) T haddt hsmult)
```

The selector exports the strict derivatives with these `linearizedEndpointCLM`
maps, but not equivalences whose coercions are those maps.  The available
non-vacuous upgrade,
`CartanEquivUpgrade.exists_continuousLinearEquiv_of_sourceScaledNormalVector_action`,
requires an explicit radial/transverse action equation for each endpoint CLM;
that action equation is not among the public witnesses assembled by the
common-time selector.

No curvature-only theorem is stated here, since assuming the missing
equivalence witnesses would only rename this boundary.
-/

noncomputable section

namespace Poincare
namespace LocalIsometryTheorem

end LocalIsometryTheorem
end Poincare
