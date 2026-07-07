import Poincare.Global.GermDeterminacy
import Poincare.Global.GeodesicReanchorLaw
import Poincare.Global.IsometryConsumers

/-!
# Induced tangent alignment at a Cartan re-anchor

This module isolates the non-arbitrary part of the globalization re-anchoring
step.  If the old Cartan chart map has a metric-preserving differential at the
new source point, then after transporting both sides through the source and
target chart transitions that differential is a genuine
`CartanMap.TangentAlignment` at the new anchors.

The final old-germ-versus-reanchored-germ `EqOn` statement still requires a
separate re-centering theorem identifying the old germ, near the new anchor, as
the Cartan germ determined by this induced tangent alignment.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace InducedAlignment

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Choose the continuous linear equivalence represented by an invertible CLM. -/
def continuousLinearEquivOfInvertible
    (D : E →L[ℝ] E) (hD : D.IsInvertible) : E ≃L[ℝ] E :=
  Classical.choose hD

/--
The tangent alignment induced by the old Cartan differential at a new anchor.

The hypotheses are exactly the chart-level data needed to change coordinates:
`hxcoord` and `hpcoord` identify the old source/target chart coordinates of the
new anchors with the old exponential-chart point, while `hpullback` is the
carried metric pullback identity for the old Cartan chart differential at that
point.
-/
def inducedTangentAlignmentOfChartPullback
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x₀ x₁ : M} {p₀ p₁ : RoundSphere3}
    (L₀ : CartanMap.TangentAlignment g x₀ p₀)
    {v : E} {A B : E ≃L[ℝ] E}
    (hx₁_old : x₁ ∈ (extChartAt I x₀).source)
    (hp₁_old : p₁ ∈ (extChartAt I p₀).source)
    (hxcoord :
      extChartAt I x₀ x₁ =
        GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ v)
    (hpcoord :
      extChartAt I p₀ p₁ =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀ (L₀ v))
    (hpullback :
      ∀ u u' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L₀ v))
            (CartanLocalIsometry.cartanChartDifferential L₀ A B u)
            (CartanLocalIsometry.cartanChartDifferential L₀ A B u') =
          CovariantDerivative.chartMetric g.inner x₀
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            u u') :
    CartanMap.TangentAlignment g x₁ p₁ := by
  let zSource : E := extChartAt I x₁ x₁
  have hzSource : zSource ∈ (extChartAt I x₁).target := by
    simpa [zSource] using
      (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsourceSymm : (extChartAt I x₁).symm zSource = x₁ := by
    simpa [zSource] using
      (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hySource : (extChartAt I x₁).symm zSource ∈ (extChartAt I x₀).source := by
    rw [hsourceSymm]
    exact hx₁_old
  let sourceCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := x₁) (y₀ := x₀) zSource
  have hsourceCLM_inv : sourceCLM.IsInvertible := by
    dsimp [sourceCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hySource).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzSource)
  let sourceEquiv : E ≃L[ℝ] E :=
    continuousLinearEquivOfInvertible sourceCLM hsourceCLM_inv
  have hsourceEquiv_coe : (sourceEquiv : E →L[ℝ] E) = sourceCLM := by
    simpa [sourceEquiv, continuousLinearEquivOfInvertible] using
      Classical.choose_spec hsourceCLM_inv
  have hsourceChartPoint :
      GeodesicTransport.chartTransition (n := 3) x₁ x₀ zSource =
        GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ v := by
    change
      extChartAt I x₀ ((extChartAt I x₁).symm zSource) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀ v
    rw [hsourceSymm]
    exact hxcoord

  let zTarget : E := extChartAt I p₁ p₁
  have hzTarget : zTarget ∈ (extChartAt I p₁).target := by
    simpa [zTarget] using
      (extChartAt I p₁).map_source (mem_extChartAt_source p₁)
  have htargetSymm : (extChartAt I p₁).symm zTarget = p₁ := by
    simpa [zTarget] using
      (extChartAt I p₁).left_inv (mem_extChartAt_source p₁)
  have hyTarget : (extChartAt I p₁).symm zTarget ∈ (extChartAt I p₀).source := by
    rw [htargetSymm]
    exact hp₁_old
  let targetCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv (x₀ := p₁) (y₀ := p₀) zTarget
  have htargetCLM_inv : targetCLM.IsInvertible := by
    dsimp [targetCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hyTarget).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzTarget)
  let targetEquiv : E ≃L[ℝ] E :=
    continuousLinearEquivOfInvertible targetCLM htargetCLM_inv
  have htargetEquiv_coe : (targetEquiv : E →L[ℝ] E) = targetCLM := by
    simpa [targetEquiv, continuousLinearEquivOfInvertible] using
      Classical.choose_spec htargetCLM_inv
  have htargetChartPoint :
      GeodesicTransport.chartTransition (n := 3) p₁ p₀ zTarget =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀ (L₀ v) := by
    change
      extChartAt I p₀ ((extChartAt I p₁).symm zTarget) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀ (L₀ v)
    rw [htargetSymm]
    exact hpcoord

  let oldD : E ≃L[ℝ] E := (A.symm.trans L₀.toContinuousLinearEquiv).trans B
  have holdD :
      (oldD : E →L[ℝ] E) =
        CartanLocalIsometry.cartanChartDifferential L₀ A B := by
    ext u
    simp [oldD, CartanLocalIsometry.cartanChartDifferential]
  let induced : E ≃L[ℝ] E := (sourceEquiv.trans oldD).trans targetEquiv.symm
  refine
    { toLinearEquiv := induced.toLinearEquiv
      map_app' := ?_ }
  intro u u'
  have htargetTransport :=
    GeodesicTransport.chartMetric_chartTransitionMFDeriv
      (g := roundSphereMetric3) (x₀ := p₁) (y₀ := p₀)
      (z := zTarget) hyTarget (induced u) (induced u')
  have htargetTransport' :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L₀ v))
          (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) := by
    have h := htargetTransport.symm
    rw [htargetChartPoint] at h
    change
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L₀ v))
          (targetCLM (induced u)) (targetCLM (induced u')) at h
    rw [← htargetEquiv_coe] at h
    simpa [induced, oldD] using h
  have hpull := hpullback (sourceEquiv u) (sourceEquiv u')
  rw [← holdD] at hpull
  have hsourceTransport :=
    GeodesicTransport.chartMetric_chartTransitionMFDeriv
      (g := g) (x₀ := x₁) (y₀ := x₀)
      (z := zSource) hySource u u'
  have hsourceTransport' :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (sourceEquiv u) (sourceEquiv u') =
        CovariantDerivative.chartMetric g.inner x₁ zSource u u' := by
    have h := hsourceTransport
    rw [hsourceChartPoint] at h
    change
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (sourceCLM u) (sourceCLM u') =
        CovariantDerivative.chartMetric g.inner x₁ zSource u u' at h
    rw [← hsourceEquiv_coe] at h
    exact h
  calc
    CartanMap.targetAnchorBilinForm p₁ (induced u) (induced u') =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₁ zTarget
          (induced u) (induced u') := rfl
    _ =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L₀ v))
          (oldD (sourceEquiv u)) (oldD (sourceEquiv u')) :=
      htargetTransport'
    _ =
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (sourceEquiv u) (sourceEquiv u') :=
      hpull
    _ = CovariantDerivative.chartMetric g.inner x₁ zSource u u' :=
      hsourceTransport'
    _ = CartanMap.sourceAnchorBilinForm g x₁ u u' := rfl

namespace CompatibleStep

/-- Re-anchor a chain state with an explicitly supplied tangent alignment. -/
def nextWithAlignment
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁)) :
    CartanChain.ChainState g where
  anchor := x₁
  target := s.map x₁
  alignment := L₁

/--
Compatibility for an explicitly aligned step.  Unlike
`CartanChain.ChainState.next`, this step has no arbitrary tangent-alignment
choice hidden in its definition.
-/
def RigidStepCompatibleWith
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁)) : Prop :=
  let s₁ := nextWithAlignment s x₁ L₁
  EqOn s.germ s₁.germ (s.germ.source ∩ s₁.germ.source)

end CompatibleStep

end InducedAlignment
end Poincare
