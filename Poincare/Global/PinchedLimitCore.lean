import Poincare.Global.PinchedLimitInterface
import Poincare.Global.EinsteinInterface

/-!
# Core-payload consequences

With scalar-curvature differentiability unconditional
(`scalarAt_mdifferentiableAt`), the pinched-limit sphere theorem and the
Einstein reduction can be restated against the reduced core payload: no
regularity hypothesis appears anywhere.  This module records those
differentiability-free forms and the per-manifold conclusion under the two
minimal interfaces.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
Differentiability-free pinched-limit sphere theorem: vanishing traceless
Ricci and somewhere-positive scalar curvature alone (plus the space-form
recognition interface) give the statement-layer sphere; the scalar-regularity
input of `sphere_of_pinched_limit` is supplied by
`scalarAt_mdifferentiableAt`.
-/
theorem sphere_of_pinched_limit_core
    (g : ClosedSmoothRiemannianMetric 3 M)
    (htr : ∀ x : M, g.tracelessRicciNormSqAt x = 0)
    (hpos : ∃ x : M, 0 < g.scalarAt x)
    (hSpaceForm : PositiveConstantCurvatureSpaceForm3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  sphere_of_pinched_limit (g := g)
    (fun x => scalarAt_mdifferentiableAt g x) htr hpos hSpaceForm

/-- A positive Einstein metric supplies the reduced core payload directly. -/
theorem hamiltonConvergencePinchedLimit3Core_of_positiveEinsteinMetric3
    (h : PositiveEinsteinMetric3 M) :
    HamiltonConvergencePinchedLimit3Core M :=
  (hamiltonConvergencePinchedLimit3_iff_core (M := M)).mp
    (hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3 h)

/--
Per-manifold statement-layer conclusion from the reduced core payload and
unit-curvature recognition — the two-interface endgame in pointwise form.
-/
theorem poincareConjecture_conclusion_of_core_of_unitRecognition
    (hCore : HamiltonConvergencePinchedLimit3Core M)
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  poincareConjecture_conclusion_of_hamiltonConvergencePinchedLimit3
    ((hamiltonConvergencePinchedLimit3_iff_core (M := M)).mpr hCore)
    (positiveConstantCurvatureSpaceForm3_of_unitRecognition hUnit)

end Poincare
