import Poincare.Global.ExponentialLocalHomeo
import Poincare.Global.RoundSphereMetric
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Candidate Cartan map for the unit-curvature rigidity campaign

This file opens the Cartan/Killing-Hopf local rigidity route.  At chart level,
the fixed-time exponential is already packaged as
`expAtChartOpenPartialHomeomorph`.  The local candidate map is therefore the
composition

`chart_x₀ ; (exp_x₀)⁻¹ ; L ; exp_p₀ ; (chart_p₀)⁻¹`.

The total function `cartanMap` is the coercion of this open partial
homeomorphism.  As usual for `OpenPartialHomeomorph`, values outside the source
are unspecified junk; the theorems below concern the open source neighborhood.

Mathlib's `E ≃ₗᵢ[ℝ] E` type preserves the ambient Euclidean norm on `E`.  The
Cartan alignment needed here preserves two chart-metric bilinear forms instead,
so the faithful bundled type is `LinearMap.BilinForm.IsometryEquiv`.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

namespace CartanMap

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The source anchor metric transported to the model chart at `x₀`. -/
def sourceAnchorChartMetric (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)

/-- The round-sphere anchor metric transported to the model chart at `p₀`. -/
def targetAnchorChartMetric (p₀ : RoundSphere3) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ (extChartAt I p₀ p₀)

/-- Forget continuity from a continuous bilinear form. -/
def continuousBilinFormToBilinForm (B : E →L[ℝ] E →L[ℝ] ℝ) :
    LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun u v : E => B u v)
    (fun u u' v => by simp)
    (fun c u v => by simp)
    (fun u v v' => by simp)
    (fun c u v => by simp)

/-- The source anchor chart metric as an unbundled bilinear form. -/
def sourceAnchorBilinForm (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    LinearMap.BilinForm ℝ E :=
  continuousBilinFormToBilinForm (sourceAnchorChartMetric g x₀)

/-- The round-sphere anchor chart metric as an unbundled bilinear form. -/
def targetAnchorBilinForm (p₀ : RoundSphere3) : LinearMap.BilinForm ℝ E :=
  continuousBilinFormToBilinForm (targetAnchorChartMetric p₀)

@[simp]
theorem sourceAnchorBilinForm_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (u v : E) :
    sourceAnchorBilinForm g x₀ u v = sourceAnchorChartMetric g x₀ u v :=
  rfl

@[simp]
theorem targetAnchorBilinForm_apply (p₀ : RoundSphere3) (u v : E) :
    targetAnchorBilinForm p₀ u v = targetAnchorChartMetric p₀ u v :=
  rfl

/--
The tangent alignment at the two anchors.

This is the chart-metric version of a linear isometry equivalence: it is a
linear equivalence of the common model space `E` preserving the source and
target anchor bilinear forms.
-/
abbrev TangentAlignment (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p₀ : RoundSphere3) : Type :=
  (sourceAnchorBilinForm g x₀).IsometryEquiv (targetAnchorBilinForm p₀)

theorem sourceAnchorChartMetric_symm
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (u v : E) :
    sourceAnchorChartMetric g x₀ u v = sourceAnchorChartMetric g x₀ v u := by
  simpa [sourceAnchorChartMetric] using
    CovariantDerivative.chartMetric_symm g.inner
      (fun y a b => g.symm y a b) x₀ (extChartAt I x₀ x₀) u v

theorem targetAnchorChartMetric_symm (p₀ : RoundSphere3) (u v : E) :
    targetAnchorChartMetric p₀ u v = targetAnchorChartMetric p₀ v u := by
  simpa [targetAnchorChartMetric] using
    CovariantDerivative.chartMetric_symm roundSphereMetric3.inner
      (fun y a b => roundSphereMetric3.symm y a b) p₀ (extChartAt I p₀ p₀) u v

theorem sourceAnchorChartMetric_pos
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {v : E} (hv : v ≠ 0) :
    0 < sourceAnchorChartMetric g x₀ v v := by
  simpa [sourceAnchorChartMetric] using
    CovariantDerivative.chartMetric_posDef g.inner
      (fun y a ha => g.pos y a ha) x₀
      (isInvertible_mfderivWithin_extChartAt_symm
        (mem_extChartAt_target x₀)) hv

theorem targetAnchorChartMetric_pos (p₀ : RoundSphere3) {v : E} (hv : v ≠ 0) :
    0 < targetAnchorChartMetric p₀ v v := by
  simpa [targetAnchorChartMetric] using
    CovariantDerivative.chartMetric_posDef roundSphereMetric3.inner
      (fun y a ha => roundSphereMetric3.pos y a ha) p₀
      (isInvertible_mfderivWithin_extChartAt_symm
        (mem_extChartAt_target p₀)) hv

/-- The defining metric-preservation law of a Cartan tangent alignment. -/
theorem TangentAlignment.map_app
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : TangentAlignment g x₀ p₀) (u v : E) :
    targetAnchorChartMetric p₀ (L u) (L v) =
      sourceAnchorChartMetric g x₀ u v :=
  L.map_app' u v

/-- The underlying continuous linear equivalence of a tangent alignment. -/
def TangentAlignment.toContinuousLinearEquiv
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : TangentAlignment g x₀ p₀) : E ≃L[ℝ] E :=
  (L : E ≃ₗ[ℝ] E).toContinuousLinearEquiv

@[simp]
theorem TangentAlignment.toContinuousLinearEquiv_apply
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : TangentAlignment g x₀ p₀) (v : E) :
    L.toContinuousLinearEquiv v = L v :=
  rfl

/-- The tangent alignment as an open partial homeomorphism of the model space. -/
def tangentAlignmentOpenPartialHomeomorph
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : TangentAlignment g x₀ p₀) : OpenPartialHomeomorph E E :=
  L.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem tangentAlignmentOpenPartialHomeomorph_apply
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : TangentAlignment g x₀ p₀) (v : E) :
    tangentAlignmentOpenPartialHomeomorph L v = L v :=
  rfl

/--
The local Cartan map as an open partial homeomorphism.

Its source is the open normal-coordinate neighborhood on which the charted
source exponential can be inverted, then transported by `L`, then fed into the
charted round-sphere exponential.  The target is open by the
`OpenPartialHomeomorph` package.
-/
def openPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) : OpenPartialHomeomorph M RoundSphere3 :=
  (chartAt E x₀).trans
    ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).symm.trans
      ((tangentAlignmentOpenPartialHomeomorph L).trans
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀).trans
          (chartAt E p₀).symm)))

/--
The total candidate Cartan map.

Outside `openPartialHomeomorph g x₀ p₀ L).source` this is the arbitrary total
extension supplied by the composed partial homeomorphism.
-/
def cartanMap (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) : M → RoundSphere3 :=
  openPartialHomeomorph g x₀ p₀ L

theorem cartanMap_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) (x : M) :
    cartanMap g x₀ p₀ L x =
      (chartAt E p₀).symm
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀
          (L ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₀).symm ((chartAt E x₀) x)))) :=
  rfl

theorem expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ (0 : E) =
      (chartAt E x₀) x₀ := by
  simp [GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
    GeodesicTransport.expAt_zero, closedSmoothModelWithCorners]

theorem expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).symm
        ((chartAt E x₀) x₀) = (0 : E) := by
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0 : (0 : E) ∈ e.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  have hbase : e (0 : E) = (chartAt E x₀) x₀ := by
    simp [e, expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor]
  rw [← hbase]
  exact e.left_inv h0

theorem cartanMap_anchor
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    cartanMap g x₀ p₀ L x₀ = p₀ := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀
  have hM : eM.symm ((chartAt E x₀) x₀) = (0 : E) := by
    simpa [eM] using
      expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero (g := g) x₀
  have hS : eS (0 : E) = (chartAt E p₀) p₀ := by
    simp [eS, expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor]
  calc
    cartanMap g x₀ p₀ L x₀ =
        (chartAt E p₀).symm (eS (L (eM.symm ((chartAt E x₀) x₀)))) := rfl
    _ = (chartAt E p₀).symm (eS (L (0 : E))) := by rw [hM]
    _ = (chartAt E p₀).symm (eS (0 : E)) := by simp
    _ = (chartAt E p₀).symm ((chartAt E p₀) p₀) := by rw [hS]
    _ = p₀ := (chartAt E p₀).left_inv (mem_chart_source E p₀)

theorem anchor_mem_source
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    x₀ ∈ (openPartialHomeomorph g x₀ p₀ L).source := by
  simp [openPartialHomeomorph, expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero]
  constructor
  · simpa [closedSmoothModelWithCorners, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x₀
  constructor
  · simp [tangentAlignmentOpenPartialHomeomorph]
  · exact
      GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
        (g := roundSphereMetric3) p₀

theorem anchor_mem_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    p₀ ∈ (openPartialHomeomorph g x₀ p₀ L).target := by
  have hx : x₀ ∈ (openPartialHomeomorph g x₀ p₀ L).source :=
    anchor_mem_source g x₀ p₀ L
  have hmap := (openPartialHomeomorph g x₀ p₀ L).map_source hx
  change cartanMap g x₀ p₀ L x₀ ∈ (openPartialHomeomorph g x₀ p₀ L).target at hmap
  simpa [cartanMap_anchor] using hmap

/-- The source normal neighborhood of the local Cartan map is open. -/
theorem isOpen_source
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    IsOpen (openPartialHomeomorph g x₀ p₀ L).source :=
  (openPartialHomeomorph g x₀ p₀ L).open_source

/-- The image normal neighborhood of the local Cartan map is open. -/
theorem isOpen_target
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    IsOpen (openPartialHomeomorph g x₀ p₀ L).target :=
  (openPartialHomeomorph g x₀ p₀ L).open_target

/-- The Cartan map restricts to a homeomorphism between its open source and target. -/
def sourceTargetHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (L : TangentAlignment g x₀ p₀) :
    (openPartialHomeomorph g x₀ p₀ L).source ≃ₜ
      (openPartialHomeomorph g x₀ p₀ L).target :=
  (openPartialHomeomorph g x₀ p₀ L).toHomeomorphSourceTarget

end CartanMap
end Poincare
