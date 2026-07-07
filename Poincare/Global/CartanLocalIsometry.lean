import Poincare.Global.CartanDifferential

/-!
# Cartan local-isometry pullback assembly

This module performs the final Cartan pullback algebra in normal coordinates.
The analytic input expected from the endpoint differential surface is that both
source and round-sphere endpoint metrics decompose with the same radial factor
and transverse factor.  Under that shared-factor expansion, the tangent
alignment gives the pointwise chart-metric pullback identity.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanLocalIsometry

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The source normal-coordinate vector after applying radial/transverse factors. -/
def sourceScaledNormalVector
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (ρ σ : ℝ) (v u : E) : E :=
  ρ • CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u +
    σ • CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u

/--
The target normal-coordinate vector after the tangent alignment and the same
radial/transverse factors.
-/
def targetScaledNormalVector
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (ρ σ : ℝ) (v u : E) : E :=
  ρ • L (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u) +
    σ • L (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u)

/-- The classical Cartan transverse factor in normal coordinates. -/
def transverseScale (v : E) : ℝ :=
  Real.sin ‖v‖ / ‖v‖

/--
Source endpoint metric expansion at one normal-coordinate vector.  This is the
exact source-side field required by the Cartan pullback algebra.
-/
structure SourceEndpointExpansion
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (v : E) : Prop where
  metric :
    ∀ u u' : E,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        CartanMap.sourceAnchorChartMetric g x₀
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u')

/--
Target endpoint metric expansion at the aligned round-sphere endpoint.  This
is stated on the scaled target vectors, before substituting the chain-rule
differential.
-/
structure TargetEndpointExpansion
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) : Prop where
  metric :
    ∀ u u' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u') =
        CartanMap.targetAnchorChartMetric p₀
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u')

/--
The endpoint expansion bundle consumed by the rigid-11 Cartan local-isometry
proof: source and target endpoint metrics have the same radial factor `1` and
transverse factor `sin ‖v‖ / ‖v‖`.
-/
structure EndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) : Prop where
  sourceExpansion : SourceEndpointExpansion g x₀ v
  targetExpansion : TargetEndpointExpansion L v

/--
Source endpoint metric expansion with a shared endpoint chart-weight.  This is
the corrected form needed when the endpoint chart metric is not the anchor
chart metric.
-/
structure WeightedSourceEndpointExpansion
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (v : E) (κ : ℝ) : Prop where
  metric :
    ∀ u u' : E,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        κ *
          CartanMap.sourceAnchorChartMetric g x₀
            (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
            (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u')

/--
Target endpoint metric expansion with the same shared endpoint chart-weight.
For non-normal endpoint charts this is the form that survives the sphere
sanity check: the varying chart metric contributes `κ` on both sides.
-/
structure WeightedTargetEndpointExpansion
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) (κ : ℝ) : Prop where
  metric :
    ∀ u u' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u') =
        κ *
          CartanMap.targetAnchorChartMetric p₀
            (targetScaledNormalVector L 1 (transverseScale v) v u)
            (targetScaledNormalVector L 1 (transverseScale v) v u')

/--
Corrected endpoint expansion bundle: both source and target endpoint metrics
carry the same endpoint chart-weight `κ`.
-/
structure WeightedEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) (κ : ℝ) : Prop where
  sourceExpansion : WeightedSourceEndpointExpansion g x₀ v κ
  targetExpansion : WeightedTargetEndpointExpansion L v κ

/-- Constructor for the endpoint expansion bundle from its two metric fields. -/
theorem endpointExpansionBundle_of_metric_expansions
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E)
    (hsource :
      ∀ u u' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            u u' =
          CartanMap.sourceAnchorChartMetric g x₀
            (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
            (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u'))
    (htarget :
      ∀ u u' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (targetScaledNormalVector L 1 (transverseScale v) v u)
            (targetScaledNormalVector L 1 (transverseScale v) v u') =
          CartanMap.targetAnchorChartMetric p₀
            (targetScaledNormalVector L 1 (transverseScale v) v u)
            (targetScaledNormalVector L 1 (transverseScale v) v u')) :
    EndpointExpansionBundle L v where
  sourceExpansion := ⟨hsource⟩
  targetExpansion := ⟨htarget⟩

/-- Constructor for the corrected weighted endpoint bundle from its two fields. -/
theorem weightedEndpointExpansionBundle_of_metric_expansions
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (v : E) (κ : ℝ)
    (hsource :
      ∀ u u' : E,
        CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            u u' =
          κ *
            CartanMap.sourceAnchorChartMetric g x₀
              (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
              (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u'))
    (htarget :
      ∀ u u' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (targetScaledNormalVector L 1 (transverseScale v) v u)
            (targetScaledNormalVector L 1 (transverseScale v) v u') =
          κ *
            CartanMap.targetAnchorChartMetric p₀
              (targetScaledNormalVector L 1 (transverseScale v) v u)
              (targetScaledNormalVector L 1 (transverseScale v) v u')) :
    WeightedEndpointExpansionBundle L v κ where
  sourceExpansion := ⟨hsource⟩
  targetExpansion := ⟨htarget⟩

/-- The strict chart differential obtained from the Cartan chain rule. -/
def cartanChartDifferential
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (A B : E ≃L[ℝ] E) :
    E →L[ℝ] E :=
  (B : E →L[ℝ] E).comp
    ((L.toContinuousLinearEquiv : E →L[ℝ] E).comp
      (A.symm : E →L[ℝ] E))

/--
The isolated algebra step: if both endpoint differentials carry the same
radial factor `ρ` and transverse factor `σ`, the target anchor pairing equals
the source anchor pairing after tangent alignment.
-/
theorem sameFactors_anchor_pair
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (ρ σ : ℝ) (v u u' : E) :
    CartanMap.targetAnchorChartMetric p₀
      (targetScaledNormalVector L ρ σ v u)
      (targetScaledNormalVector L ρ σ v u') =
    CartanMap.sourceAnchorChartMetric g x₀
      (sourceScaledNormalVector g x₀ ρ σ v u)
      (sourceScaledNormalVector g x₀ ρ σ v u') := by
  simpa [sourceScaledNormalVector, targetScaledNormalVector] using
    CartanDifferential.tangentAlignment_scaled_radial_transverse_pair
      (g := g) (x₀ := x₀) (p₀ := p₀) L ρ σ v u u'

/--
Pointwise chart-metric pullback identity in normal coordinates, assuming the
source and target endpoint metrics have already been expanded with the same
radial/transverse factors.
-/
theorem chartMetric_pullback_identity_of_sameFactors
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (ρ σ : ℝ) (v u u' : E)
    (hsource :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        CartanMap.sourceAnchorChartMetric g x₀
          (sourceScaledNormalVector g x₀ ρ σ v u)
          (sourceScaledNormalVector g x₀ ρ σ v u'))
    (htarget :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L ρ σ v u)
          (targetScaledNormalVector L ρ σ v u') =
        CartanMap.targetAnchorChartMetric p₀
          (targetScaledNormalVector L ρ σ v u)
          (targetScaledNormalVector L ρ σ v u')) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (targetScaledNormalVector L ρ σ v u)
        (targetScaledNormalVector L ρ σ v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' := by
  rw [htarget, hsource]
  exact sameFactors_anchor_pair (g := g) (x₀ := x₀) (p₀ := p₀) L ρ σ v u u'

/--
Weighted version of `chartMetric_pullback_identity_of_sameFactors`.  The
endpoint chart-weight may be nontrivial, but it cancels because it is shared by
the source and target endpoint expansions.
-/
theorem chartMetric_pullback_identity_of_sameWeightedFactors
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (κ ρ σ : ℝ) (v u u' : E)
    (hsource :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        κ *
          CartanMap.sourceAnchorChartMetric g x₀
            (sourceScaledNormalVector g x₀ ρ σ v u)
            (sourceScaledNormalVector g x₀ ρ σ v u'))
    (htarget :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L ρ σ v u)
          (targetScaledNormalVector L ρ σ v u') =
        κ *
          CartanMap.targetAnchorChartMetric p₀
            (targetScaledNormalVector L ρ σ v u)
            (targetScaledNormalVector L ρ σ v u')) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (targetScaledNormalVector L ρ σ v u)
        (targetScaledNormalVector L ρ σ v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' := by
  rw [htarget, hsource]
  exact congrArg (fun q : ℝ => κ * q)
    (sameFactors_anchor_pair (g := g) (x₀ := x₀) (p₀ := p₀) L ρ σ v u u')

/--
The Cartan pullback identity with radial factor `1` and transverse factor
`sin ‖v‖ / ‖v‖`, once the two endpoint metric expansions have those factors.
-/
theorem cartanMap_chart_pullback_identity
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (v u u' : E)
    (hsource :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        CartanMap.sourceAnchorChartMetric g x₀
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u'))
    (htarget :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u') =
        CartanMap.targetAnchorChartMetric p₀
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u')) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (targetScaledNormalVector L 1 (transverseScale v) v u)
        (targetScaledNormalVector L 1 (transverseScale v) v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' :=
  chartMetric_pullback_identity_of_sameFactors
    (g := g) (x₀ := x₀) (p₀ := p₀) L 1 (transverseScale v) v u u'
    hsource htarget

/--
Pointwise Cartan pullback identity from the bundled endpoint expansions.
-/
theorem cartanMap_chart_pullback_identity_of_endpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (v u u' : E) (hexpansion : EndpointExpansionBundle L v) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (targetScaledNormalVector L 1 (transverseScale v) v u)
        (targetScaledNormalVector L 1 (transverseScale v) v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' :=
  cartanMap_chart_pullback_identity
    (g := g) (x₀ := x₀) (p₀ := p₀) L v u u'
    (hexpansion.sourceExpansion.metric u u')
    (hexpansion.targetExpansion.metric u u')

/--
Pointwise Cartan pullback identity from the corrected weighted endpoint
expansions.
-/
theorem cartanMap_chart_pullback_identity_of_weightedEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    (v u u' : E) {κ : ℝ} (hexpansion : WeightedEndpointExpansionBundle L v κ) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        (targetScaledNormalVector L 1 (transverseScale v) v u)
        (targetScaledNormalVector L 1 (transverseScale v) v u') =
      CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        u u' :=
  chartMetric_pullback_identity_of_sameWeightedFactors
    (g := g) (x₀ := x₀) (p₀ := p₀) L κ 1 (transverseScale v) v u u'
    (hexpansion.sourceExpansion.metric u u')
    (hexpansion.targetExpansion.metric u u')

/--
Packaged chart-local-isometry statement for the Cartan map on a normal
coordinate point: the strict chain-rule differential is retained, and its
pointwise metric pullback is the source chart metric.
-/
theorem cartanMap_isLocalIsometry_on_normalBall
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      cartanChartDifferential L A B u =
        targetScaledNormalVector L 1 (transverseScale v) v u)
    (hDu' :
      cartanChartDifferential L A B u' =
        targetScaledNormalVector L 1 (transverseScale v) v u')
    (hsourceMetric :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' =
        CartanMap.sourceAnchorChartMetric g x₀
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u)
          (sourceScaledNormalVector g x₀ 1 (transverseScale v) v u'))
    (htargetMetric :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (cartanChartDifferential L A B u)
          (cartanChartDifferential L A B u') =
        CartanMap.targetAnchorChartMetric p₀
          (cartanChartDifferential L A B u)
          (cartanChartDifferential L A B u')) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (cartanChartDifferential L A B u)
          (cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := by
  constructor
  · simpa [cartanChartDifferential] using
      CartanDifferential.cartanChartMap_hasStrictFDerivAt_of_expAtChart
        (g := g) (x₀ := x₀) (p₀ := p₀) (L := L)
        (v := v) (A := A) (B := B)
        hvsrc hsourceDeriv htargetDeriv
  · have htargetExpanded :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u') =
        CartanMap.targetAnchorChartMetric p₀
          (targetScaledNormalVector L 1 (transverseScale v) v u)
          (targetScaledNormalVector L 1 (transverseScale v) v u') := by
      simpa [hDu, hDu'] using htargetMetric
    have hpull :=
      cartanMap_chart_pullback_identity
        (g := g) (x₀ := x₀) (p₀ := p₀) L v u u'
        hsourceMetric htargetExpanded
    simpa [hDu, hDu'] using hpull

/--
Packaged chart-local-isometry statement using the endpoint expansion bundle.
This is the same rigid-11 proof pattern as
`cartanMap_isLocalIsometry_on_normalBall`, with the source and target metric
expansions supplied through one reusable constructor surface.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_endpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      cartanChartDifferential L A B u =
        targetScaledNormalVector L 1 (transverseScale v) v u)
    (hDu' :
      cartanChartDifferential L A B u' =
        targetScaledNormalVector L 1 (transverseScale v) v u')
    (hexpansion : EndpointExpansionBundle L v) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (cartanChartDifferential L A B u)
          (cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := by
  refine
    cartanMap_isLocalIsometry_on_normalBall
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (A := A) (B := B)
      hvsrc hsourceDeriv htargetDeriv u u' hDu hDu'
      (hexpansion.sourceExpansion.metric u u') ?_
  simpa [hDu, hDu'] using hexpansion.targetExpansion.metric u u'

/--
Packaged chart-local-isometry statement using the corrected weighted endpoint
expansion bundle.  This is the non-normal-chart analogue of
`cartanMap_isLocalIsometry_on_normalBall_of_endpointExpansionBundle`: the
shared endpoint chart-weight cancels in the final pullback identity.
-/
theorem cartanMap_isLocalIsometry_on_normalBall_of_weightedEndpointExpansionBundle
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E} {κ : ℝ}
    (hvsrc : v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v))
    (u u' : E)
    (hDu :
      cartanChartDifferential L A B u =
        targetScaledNormalVector L 1 (transverseScale v) v u)
    (hDu' :
      cartanChartDifferential L A B u' =
        targetScaledNormalVector L 1 (transverseScale v) v u')
    (hexpansion : WeightedEndpointExpansionBundle L v κ) :
    HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (cartanChartDifferential L A B)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v))
          (cartanChartDifferential L A B u)
          (cartanChartDifferential L A B u') =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          u u' := by
  constructor
  · simpa [cartanChartDifferential] using
      CartanDifferential.cartanChartMap_hasStrictFDerivAt_of_expAtChart
        (g := g) (x₀ := x₀) (p₀ := p₀) (L := L)
        (v := v) (A := A) (B := B)
        hvsrc hsourceDeriv htargetDeriv
  · have hpull :=
      cartanMap_chart_pullback_identity_of_weightedEndpointExpansionBundle
        (g := g) (x₀ := x₀) (p₀ := p₀) L v u u' hexpansion
    simpa [hDu, hDu'] using hpull

end CartanLocalIsometry
end Poincare
