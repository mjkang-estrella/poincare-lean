import Poincare.Global.DifferentialField
import Poincare.Global.InducedAlignment
import Poincare.Global.GeodesicReanchorClose

/-!
# Differential-induced Cartan successors

This module replaces the arbitrary orthonormal-basis alignment formerly hidden
in a Cartan-chain successor by the differential actually carried by the
predecessor Cartan map.  The coordinate-change and metric-pullback witnesses
are retained, so the resulting alignment can be used by the re-centering
rigidity theorem rather than merely asserting existence of some alignment.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialInducedSuccessor

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The complete differential data determining the successor alignment at `x₁`.

The source and target chart transitions convert the old Cartan chart
differential into a map between the tangent models at `x₁` and `s.map x₁`.
The pullback field proves that this converted differential is a tangent
alignment.
-/
structure Data {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (x₁ : M) where
  v : E
  A : E ≃L[ℝ] E
  B : E ≃L[ℝ] E
  source_vector_mem :
    v ∈ (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).source
  target_vector_mem :
    s.alignment v ∈
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target).source
  source_mem_oldChart : x₁ ∈ (extChartAt I s.anchor).source
  target_mem_oldChart : s.map x₁ ∈ (extChartAt I s.target).source
  source_coordinate :
    extChartAt I s.anchor x₁ =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor v
  target_coordinate :
    extChartAt I s.target (s.map x₁) =
      GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target (s.alignment v)
  source_exp_derivative :
    HasStrictFDerivAt
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor) (A : E →L[ℝ] E) v
  target_exp_derivative :
    HasStrictFDerivAt
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target) (B : E →L[ℝ] E)
      (s.alignment v)
  cartan_chart_derivative :
    HasStrictFDerivAt
      (CartanDifferential.cartanChartMap
        g s.anchor s.target s.alignment)
      (CartanLocalIsometry.cartanChartDifferential s.alignment A B)
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor) v)
  metric_pullback :
    ∀ u u' : E,
      CovariantDerivative.chartMetric roundSphereMetric3.inner s.target
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) s.target) (s.alignment v))
          (CartanLocalIsometry.cartanChartDifferential s.alignment A B u)
          (CartanLocalIsometry.cartanChartDifferential s.alignment A B u') =
        CovariantDerivative.chartMetric g.inner s.anchor
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) s.anchor) v) u u'

/-- The tangent alignment represented by the predecessor's actual differential. -/
def Data.alignment {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    CartanMap.TangentAlignment g x₁ (s.map x₁) :=
  InducedAlignment.inducedTangentAlignmentOfChartPullback
    s.alignment d.source_mem_oldChart d.target_mem_oldChart
      d.source_coordinate d.target_coordinate d.metric_pullback

/-- Re-anchor using the predecessor differential, with no arbitrary choice. -/
def Data.successor {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    CartanChain.ChainState g :=
  InducedAlignment.CompatibleStep.nextWithAlignment s x₁ d.alignment

/-- The predecessor Cartan chart map, re-expressed in the source chart at
`x₁` and target chart at `s.map x₁`. -/
def reanchoredChartMap
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (x₁ : M) : E → E := fun z =>
  GeodesicTransport.chartTransition s.target (s.map x₁)
    (CartanDifferential.cartanChartMap
      g s.anchor s.target s.alignment
      (GeodesicTransport.chartTransition x₁ s.anchor z))

/-- Forward and reverse preferred-chart derivatives compose to the identity. -/
private theorem reverse_chartTransitionMFDeriv_comp_forward_eq_id
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source) :
    (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)).comp
      (GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) =
      ContinuousLinearMap.id ℝ E := by
  let zT : E := extChartAt I y₀ y₀
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) zT
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hzT : zT ∈ (extChartAt I y₀).target :=
    (extChartAt I y₀).map_source (mem_extChartAt_source y₀)
  have hxT : (extChartAt I y₀).symm zT = y₀ :=
    (extChartAt I y₀).left_inv (mem_extChartAt_source y₀)
  apply ContinuousLinearMap.ext
  intro w
  let Dnew : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I y₀).symm) (range I) zT
  let Cold : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p₀) y₀
  let Iold : E →L[ℝ] E :=
    mfderivWithin (modelWithCornersSelf ℝ E) I
      ((extChartAt I p₀).symm) (range I) (extChartAt I p₀ y₀)
  let Cnew : E →L[ℝ] E :=
    mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I y₀) y₀
  have holdCLM : Iold.comp Cold = ContinuousLinearMap.id ℝ E := by
    simpa [Iold, Cold] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy)
  have hnewCLM : Cnew.comp Dnew = ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hzT
    rw [hxT] at h
    simpa [Cnew, Dnew] using h
  change Drev (DT w) = w
  dsimp [Drev, DT, GeodesicTransport.chartTransitionMFDeriv]
  have hxT' : (chartAt E y₀).symm zT = y₀ := by
    simpa [extChartAt_coe] using hxT
  have hold' :
      (chartAt E p₀).symm ((chartAt E p₀) y₀) = y₀ :=
    (chartAt E p₀).left_inv (by
      simpa [extChartAt_source] using hy)
  rw [hxT', hold']
  change Cnew (Iold (Cold (Dnew w))) = w
  calc
    Cnew (Iold (Cold (Dnew w))) = Cnew (Dnew w) := by
      have hw := congrArg (fun L : E →L[ℝ] E => L (Dnew w)) holdCLM
      simpa [ContinuousLinearMap.comp_apply] using congrArg Cnew hw
    _ = w := by
      have hw := congrArg (fun L : E →L[ℝ] E => L w) hnewCLM
      simpa [ContinuousLinearMap.comp_apply] using hw

/-- The derivative of the reverse chart transition is the inverse of the
chosen equivalence representing the forward transition derivative. -/
private theorem reverse_chartTransitionMFDeriv_eq_symm
    (p₀ y₀ : RoundSphere3)
    (hy : y₀ ∈ (extChartAt I p₀).source)
    (T : E ≃L[ℝ] E)
    (hTco : (T : E →L[ℝ] E) =
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)) :
    GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀) =
      (T.symm : E →L[ℝ] E) := by
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := y₀) (y₀ := p₀) (extChartAt I y₀ y₀)
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := p₀) (y₀ := y₀) (extChartAt I p₀ y₀)
  have hcomp : Drev.comp DT = ContinuousLinearMap.id ℝ E := by
    simpa [Drev, DT] using
      reverse_chartTransitionMFDeriv_comp_forward_eq_id p₀ y₀ hy
  apply ContinuousLinearMap.ext
  intro w
  calc
    Drev w = Drev (T (T.symm w)) := by rw [T.apply_symm_apply]
    _ = (Drev.comp DT) (T.symm w) := by
      rw [ContinuousLinearMap.comp_apply]
      have hTco' : (T : E →L[ℝ] E) = DT := by
        simpa [DT] using hTco
      rw [← hTco']
      rfl
    _ = T.symm w := by rw [hcomp]; rfl

/-- The induced tangent alignment is exactly the Frechet derivative of the
predecessor Cartan map expressed in the new source and target charts. -/
theorem Data.hasFDerivAt_reanchoredChartMap
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    HasFDerivAt (reanchoredChartMap s x₁)
      (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E)
      (extChartAt I x₁ x₁) := by
  let zS : E := extChartAt I x₁ x₁
  have hzS : zS ∈ (extChartAt I x₁).target := by
    exact (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hxS : (extChartAt I x₁).symm zS = x₁ := by
    exact (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hyS : (extChartAt I x₁).symm zS ∈ (extChartAt I s.anchor).source := by
    rw [hxS]
    exact d.source_mem_oldChart
  let DS : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := x₁) (y₀ := s.anchor) zS
  have hDSinv : DS.IsInvertible := by
    dsimp [DS, GeodesicTransport.chartTransitionMFDeriv]
    exact (isInvertible_mfderiv_extChartAt hyS).comp
      (isInvertible_mfderivWithin_extChartAt_symm hzS)
  let S : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible DS hDSinv
  have hSco : (S : E →L[ℝ] E) = DS := by
    simpa [S, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec hDSinv
  have hsourcePoint :
      GeodesicTransport.chartTransition x₁ s.anchor zS =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor) d.v := by
    change extChartAt I s.anchor ((extChartAt I x₁).symm zS) = _
    rw [hxS]
    exact d.source_coordinate
  have hsourceDeriv :
      HasFDerivAt (GeodesicTransport.chartTransition x₁ s.anchor) DS zS :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      x₁ s.anchor hzS hyS
  let Dold : E ≃L[ℝ] E :=
    (d.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d.B
  have hDold : (Dold : E →L[ℝ] E) =
      CartanLocalIsometry.cartanChartDifferential
        s.alignment d.A d.B := by
    rfl
  have hcartan : HasFDerivAt
      (CartanDifferential.cartanChartMap
        g s.anchor s.target s.alignment)
      (Dold : E →L[ℝ] E)
      (GeodesicTransport.chartTransition x₁ s.anchor zS) := by
    rw [hsourcePoint, hDold]
    exact d.cartan_chart_derivative.hasFDerivAt
  have hmiddle := hcartan.comp zS hsourceDeriv
  let zT : E := extChartAt I (s.map x₁) (s.map x₁)
  have hzT : zT ∈ (extChartAt I (s.map x₁)).target := by
    exact (extChartAt I (s.map x₁)).map_source
      (mem_extChartAt_source (s.map x₁))
  have hxT : (extChartAt I (s.map x₁)).symm zT = s.map x₁ := by
    exact (extChartAt I (s.map x₁)).left_inv
      (mem_extChartAt_source (s.map x₁))
  have hyT : (extChartAt I (s.map x₁)).symm zT ∈
      (extChartAt I s.target).source := by
    rw [hxT]
    exact d.target_mem_oldChart
  let DT : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := s.map x₁) (y₀ := s.target) zT
  have hDTinv : DT.IsInvertible := by
    dsimp [DT, GeodesicTransport.chartTransitionMFDeriv]
    exact (isInvertible_mfderiv_extChartAt hyT).comp
      (isInvertible_mfderivWithin_extChartAt_symm hzT)
  let T : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible DT hDTinv
  have hTco : (T : E →L[ℝ] E) = DT := by
    simpa [T, InducedAlignment.continuousLinearEquivOfInvertible] using
      Classical.choose_spec hDTinv
  have htargetPoint :
      CartanDifferential.cartanChartMap g s.anchor s.target s.alignment
          (GeodesicTransport.chartTransition x₁ s.anchor zS) =
        extChartAt I s.target (s.map x₁) := by
    rw [hsourcePoint]
    change
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) s.target)
          (s.alignment
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) s.anchor).symm
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) s.anchor) d.v))) = _
    rw [(GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).left_inv d.source_vector_mem]
    exact d.target_coordinate.symm
  let Drev : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := s.target) (y₀ := s.map x₁)
      (extChartAt I s.target (s.map x₁))
  have htargetOld :
      extChartAt I s.target (s.map x₁) ∈
        (extChartAt I s.target).target :=
    (extChartAt I s.target).map_source d.target_mem_oldChart
  have htargetBack :
      (extChartAt I s.target).symm
          (extChartAt I s.target (s.map x₁)) ∈
        (extChartAt I (s.map x₁)).source := by
    rw [(extChartAt I s.target).left_inv d.target_mem_oldChart]
    exact mem_extChartAt_source (s.map x₁)
  have houter : HasFDerivAt
      (GeodesicTransport.chartTransition s.target (s.map x₁)) Drev
      (extChartAt I s.target (s.map x₁)) :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      s.target (s.map x₁) htargetOld htargetBack
  have hrev : Drev = (T.symm : E →L[ℝ] E) := by
    simpa [Drev, zT] using
      reverse_chartTransitionMFDeriv_eq_symm
        s.target (s.map x₁) d.target_mem_oldChart T (by
          simpa [DT, zT] using hTco)
  have houter' : HasFDerivAt
      (GeodesicTransport.chartTransition s.target (s.map x₁)) Drev
      ((CartanDifferential.cartanChartMap
        g s.anchor s.target s.alignment ∘
          GeodesicTransport.chartTransition x₁ s.anchor) zS) := by
    change HasFDerivAt
      (GeodesicTransport.chartTransition s.target (s.map x₁)) Drev
      (CartanDifferential.cartanChartMap g s.anchor s.target s.alignment
        (GeodesicTransport.chartTransition x₁ s.anchor zS))
    rw [htargetPoint]
    exact houter
  have htotal := houter'.comp zS hmiddle
  change HasFDerivAt (reanchoredChartMap s x₁)
      (Drev.comp ((Dold : E →L[ℝ] E).comp DS)) zS at htotal
  have halign : (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
      (T.symm : E →L[ℝ] E).comp
        ((Dold : E →L[ℝ] E).comp (S : E →L[ℝ] E)) := by
    rfl
  rw [hrev, ← hSco, ← halign] at htotal
  exact htotal

/-- Equality of the re-anchored coordinate germs forces equality of the
differential-induced tangent maps, even before identifying their target
indices. -/
theorem Data.alignment_clm_eq_of_reanchoredChartMap_eventuallyEq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x : M}
    (d₁ : Data s₁ x) (d₂ : Data s₂ x)
    (hmap : reanchoredChartMap s₁ x =ᶠ[𝓝 (extChartAt I x x)]
      reanchoredChartMap s₂ x) :
    (d₁.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
      (d₂.alignment.toContinuousLinearEquiv : E →L[ℝ] E) := by
  calc
    (d₁.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
        fderiv ℝ (reanchoredChartMap s₁ x) (extChartAt I x x) :=
      d₁.hasFDerivAt_reanchoredChartMap.fderiv.symm
    _ = fderiv ℝ (reanchoredChartMap s₂ x) (extChartAt I x x) :=
      Filter.EventuallyEq.fderiv_eq hmap
    _ = (d₂.alignment.toContinuousLinearEquiv : E →L[ℝ] E) :=
      d₂.hasFDerivAt_reanchoredChartMap.fderiv

/-- Equality of target indices and equality of the underlying linear maps give
heterogeneous equality of tangent alignments.  The target indices stay abstract
here, avoiding reduction of the concrete sphere-valued Cartan maps. -/
private theorem tangentAlignment_heq_of_target_eq_of_clm_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    (L₁ : CartanMap.TangentAlignment g x p₁)
    (L₂ : CartanMap.TangentAlignment g x p₂)
    (hp : p₁ = p₂)
    (hclm : (L₁.toContinuousLinearEquiv : E →L[ℝ] E) =
      (L₂.toContinuousLinearEquiv : E →L[ℝ] E)) :
    HEq L₁ L₂ := by
  subst p₂
  apply heq_of_eq
  apply DFunLike.coe_injective
  funext u
  exact DFunLike.congr_fun hclm u

/-- Abstract fieldwise equality constructor for explicitly aligned chain
states. -/
private theorem chainState_eq_of_target_eq_of_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    {L₁ : CartanMap.TangentAlignment g x p₁}
    {L₂ : CartanMap.TangentAlignment g x p₂}
    (hp : p₁ = p₂) (hL : HEq L₁ L₂) :
    (CartanChain.ChainState.mk x p₁ L₁ : CartanChain.ChainState g) =
      CartanChain.ChainState.mk x p₂ L₂ := by
  subst p₂
  cases hL
  rfl

/-- Congruence for a preferred target chart with both its anchor and argument
kept abstract, so equality elimination never unfolds a concrete Cartan map. -/
private theorem extChartAt_apply_eq_of_eq
    {p₁ p₂ q₁ q₂ : RoundSphere3}
    (hp : p₁ = p₂) (hq : q₁ = q₂) :
    extChartAt I p₁ q₁ = extChartAt I p₂ q₂ := by
  subst p₂
  subst q₂
  rfl

/-- If the two carried values agree at the new anchor, equality of their
re-anchored coordinate germs identifies the dependent tangent alignments. -/
theorem Data.alignment_heq_of_target_eq_of_reanchoredChartMap_eventuallyEq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x : M}
    (d₁ : Data s₁ x) (d₂ : Data s₂ x)
    (htarget : s₁.map x = s₂.map x)
    (hmap : reanchoredChartMap s₁ x =ᶠ[𝓝 (extChartAt I x x)]
      reanchoredChartMap s₂ x) :
    HEq d₁.alignment d₂.alignment := by
  have hclm :=
    d₁.alignment_clm_eq_of_reanchoredChartMap_eventuallyEq d₂ hmap
  exact tangentAlignment_heq_of_target_eq_of_clm_eq
    d₁.alignment d₂.alignment htarget hclm

/-- Differential-induced successor states respect equality of the carried map
germs at their common new anchor. -/
theorem Data.successor_eq_of_target_eq_of_reanchoredChartMap_eventuallyEq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x : M}
    (d₁ : Data s₁ x) (d₂ : Data s₂ x)
    (htarget : s₁.map x = s₂.map x)
    (hmap : reanchoredChartMap s₁ x =ᶠ[𝓝 (extChartAt I x x)]
      reanchoredChartMap s₂ x) :
    d₁.successor = d₂.successor := by
  have hL : HEq d₁.alignment d₂.alignment :=
    d₁.alignment_heq_of_target_eq_of_reanchoredChartMap_eventuallyEq
      d₂ htarget hmap
  change
    CartanChain.ChainState.mk x (s₁.map x) d₁.alignment =
      CartanChain.ChainState.mk x (s₂.map x) d₂.alignment
  exact chainState_eq_of_target_eq_of_alignment_heq htarget hL

/-- Equality of carried map germs in the manifold chart induces equality of
their re-anchored model-coordinate germs. -/
theorem reanchoredChartMap_eventuallyEq_of_eventuallyEq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x : M}
    (htarget : s₁.map x = s₂.map x)
    (hmaps : s₁.map =ᶠ[𝓝 x] s₂.map) :
    reanchoredChartMap s₁ x =ᶠ[𝓝 (extChartAt I x x)]
      reanchoredChartMap s₂ x := by
  have hz : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  have htend :
      Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) :=
    by
      have hcont :
          ContinuousAt ((extChartAt I x).symm : E → M) (extChartAt I x x) :=
        continuousAt_extChartAt_symm x
      change Tendsto (extChartAt I x).symm
        (𝓝 (extChartAt I x x))
        (𝓝 ((extChartAt I x).symm (extChartAt I x x))) at hcont
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x)] at hcont
      exact hcont
  have hpre := hmaps.comp_tendsto htend
  filter_upwards [hpre] with z hzmap
  exact extChartAt_apply_eq_of_eq htarget hzmap

/-- Open-set equality is enough to identify the two differential successors
at any common point of that open set. -/
theorem Data.successor_eq_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x : M}
    (d₁ : Data s₁ x) (d₂ : Data s₂ x)
    {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    (hEq : EqOn s₁.map s₂.map U) :
    d₁.successor = d₂.successor := by
  have htarget : s₁.map x = s₂.map x := hEq hx
  have hmaps : s₁.map =ᶠ[𝓝 x] s₂.map :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hEq
  exact d₁.successor_eq_of_target_eq_of_reanchoredChartMap_eventuallyEq
    d₂ htarget
      (reanchoredChartMap_eventuallyEq_of_eventuallyEq htarget hmaps)

/-- Differential-induced single-insertion independence.  A compatible step
at `y` does not change the actual differential successor subsequently formed
at `z`; no basis-choice alignment is involved. -/
theorem endpoint_successor_eq_insert_of_compatible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {y z : M}
    (dy : Data s y)
    (hcompat : EqOn s.germ dy.successor.germ
      (s.germ.source ∩ dy.successor.germ.source))
    (hz : z ∈ s.germ.source ∩ dy.successor.germ.source)
    (dz : Data s z) (dyz : Data dy.successor z) :
    dz.successor = dyz.successor := by
  apply dz.successor_eq_of_eqOn_open dyz
    (s.germ.open_source.inter dy.successor.germ.open_source) hz
  intro q hq
  simpa [CartanChain.ChainState.germ, CartanChain.ChainState.map] using
    hcompat hq

@[simp]
theorem Data.successor_anchor {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    d.successor.anchor = x₁ :=
  rfl

@[simp]
theorem Data.successor_target {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    d.successor.target = s.map x₁ :=
  rfl

/-- The new anchor encoded by differential data lies in the predecessor's
strict Cartan source. -/
theorem Data.anchor_mem_predecessor_source
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    x₁ ∈ s.germ.source := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) s.target
  have hxchart : x₁ ∈ (chartAt E s.anchor).source := by
    simpa [extChartAt_source] using d.source_mem_oldChart
  have hxcoord : (chartAt E s.anchor) x₁ = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hxexp : (chartAt E s.anchor) x₁ ∈ eM.target := by
    rw [hxcoord]
    exact eM.map_source d.source_vector_mem
  have hinv : eM.symm ((chartAt E s.anchor) x₁) = d.v := by
    rw [hxcoord]
    exact eM.left_inv d.source_vector_mem
  have htargetChart :
      (chartAt E s.target)
          (GeodesicTransport.expAt roundSphereMetric3 s.target
            (s.alignment d.v)) ∈ (chartAt E s.target).target := by
    have h := (extChartAt I s.target).map_source d.target_mem_oldChart
    rw [d.target_coordinate] at h
    simpa [eS, extChartAt_coe,
      GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using h
  simpa [CartanChain.ChainState.germ, CartanMap.openPartialHomeomorph,
    eM, eS, hinv] using
    ⟨hxchart, hxexp,
      (show d.v ∈
        (CartanMap.tangentAlignmentOpenPartialHomeomorph
          s.alignment).source by simp [CartanMap.tangentAlignmentOpenPartialHomeomorph]),
      d.target_vector_mem, htargetChart⟩

/-- The stored differential is the canonical Frechet derivative of the old
Cartan chart map at the new anchor coordinate. -/
theorem Data.chartDifferential_eq_fderiv
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d : Data s x₁) :
    CartanLocalIsometry.cartanChartDifferential s.alignment d.A d.B =
      fderiv ℝ
        (CartanDifferential.cartanChartMap
          g s.anchor s.target s.alignment)
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor) d.v) :=
  d.cartan_chart_derivative.hasFDerivAt.fderiv.symm

/-- The old normal vector stored by differential successor data is uniquely
determined by its new anchor. -/
theorem Data.vector_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d₁ d₂ : Data s x₁) :
    d₁.v = d₂.v := by
  apply
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).injOn d₁.source_vector_mem d₂.source_vector_mem
  exact d₁.source_coordinate.symm.trans d₂.source_coordinate

/-- Differential-induced alignments are independent of the selected
pointwise derivative-field witness.  Both witnesses are strict derivatives of
the same chart map, hence their middle continuous linear equivalences agree;
the source and target chart transports are determined only by the two anchors. -/
theorem Data.alignment_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d₁ d₂ : Data s x₁) :
    d₁.alignment = d₂.alignment := by
  have hv : d₁.v = d₂.v := d₁.vector_eq d₂
  have hD :
      CartanLocalIsometry.cartanChartDifferential s.alignment d₁.A d₁.B =
        CartanLocalIsometry.cartanChartDifferential s.alignment d₂.A d₂.B := by
    rw [d₁.chartDifferential_eq_fderiv,
      d₂.chartDifferential_eq_fderiv, hv]
  have hE :
      (d₁.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₁.B =
        (d₂.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₂.B := by
    apply ContinuousLinearEquiv.coe_injective
    exact hD
  let zSource : E := extChartAt I x₁ x₁
  have hzSource : zSource ∈ (extChartAt I x₁).target := by
    simpa [zSource] using
      (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsourceSymm : (extChartAt I x₁).symm zSource = x₁ := by
    simpa [zSource] using
      (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hySource :
      (extChartAt I x₁).symm zSource ∈ (extChartAt I s.anchor).source := by
    rw [hsourceSymm]
    exact d₁.source_mem_oldChart
  let sourceCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := x₁) (y₀ := s.anchor) zSource
  have hsourceInv : sourceCLM.IsInvertible := by
    dsimp [sourceCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hySource).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzSource)
  let S : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible sourceCLM hsourceInv
  let zTarget : E := extChartAt I (s.map x₁) (s.map x₁)
  have hzTarget : zTarget ∈ (extChartAt I (s.map x₁)).target := by
    simpa [zTarget] using
      (extChartAt I (s.map x₁)).map_source
        (mem_extChartAt_source (s.map x₁))
  have htargetSymm :
      (extChartAt I (s.map x₁)).symm zTarget = s.map x₁ := by
    simpa [zTarget] using
      (extChartAt I (s.map x₁)).left_inv
        (mem_extChartAt_source (s.map x₁))
  have hyTarget :
      (extChartAt I (s.map x₁)).symm zTarget ∈
        (extChartAt I s.target).source := by
    rw [htargetSymm]
    exact d₁.target_mem_oldChart
  let targetCLM : E →L[ℝ] E :=
    GeodesicTransport.chartTransitionMFDeriv
      (x₀ := s.map x₁) (y₀ := s.target) zTarget
  have htargetInv : targetCLM.IsInvertible := by
    dsimp [targetCLM, GeodesicTransport.chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hyTarget).comp
        (isInvertible_mfderivWithin_extChartAt_symm hzTarget)
  let T : E ≃L[ℝ] E :=
    InducedAlignment.continuousLinearEquivOfInvertible targetCLM htargetInv
  apply DFunLike.coe_injective
  funext u
  simp only [Data.alignment,
    InducedAlignment.inducedTangentAlignmentOfChartPullback]
  change T.symm
      (((d₁.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₁.B)
        (S u)) =
    T.symm
      (((d₂.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₂.B)
        (S u))
  exact congrArg (fun D : E ≃L[ℝ] E => T.symm (D (S u))) hE

/-- The successor state itself is canonical once differential data exist. -/
theorem Data.successor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M} (d₁ d₂ : Data s x₁) :
    d₁.successor = d₂.successor := by
  unfold Data.successor
  rw [d₁.alignment_eq d₂]

/-- Differential successor canonicity also compares data whose predecessor
states have first been identified. -/
theorem Data.successor_eq_of_state_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x₁ : M}
    (hstate : s₁ = s₂) (d₁ : Data s₁ x₁) (d₂ : Data s₂ x₁) :
    d₁.successor = d₂.successor := by
  subst s₂
  exact d₁.successor_eq d₂

/-- Choose the canonical differential-induced successor from an existence
witness.  Although the data package is selected classically, `successor_eq`
shows that the resulting state does not depend on that selection. -/
def successorOfNonempty
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (x₁ : M) (h : Nonempty (Data s x₁)) :
    CartanChain.ChainState g :=
  (Classical.choice h).successor

theorem successorOfNonempty_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (h : Nonempty (Data s x₁)) (d : Data s x₁) :
    successorOfNonempty s x₁ h = d.successor :=
  (Classical.choice h).successor_eq d

namespace Chain

/-- A data-supply policy for a fixed node sequence.  Only the policy value at
the recursively reached state is used; quantifying over all states keeps the
primitive recursion nondependent and its computation rule transparent. -/
abbrev StepAvailable
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M) : Prop :=
  ∀ (n : ℕ) (s : CartanChain.ChainState g),
    Nonempty (Data s (nodes (n + 1)))

/-- Iterate only differential-induced successors along `nodes`. -/
def chainState
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step : StepAvailable (g := g) nodes) :
    ℕ → CartanChain.ChainState g
  | 0 => initial
  | n + 1 =>
      successorOfNonempty (chainState nodes initial step n) (nodes (n + 1))
        (step n (chainState nodes initial step n))

@[simp]
theorem chainState_zero
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step : StepAvailable (g := g) nodes) :
    chainState nodes initial step 0 = initial :=
  rfl

@[simp]
theorem chainState_succ
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step : StepAvailable (g := g) nodes)
    (n : ℕ) :
    chainState nodes initial step (n + 1) =
      successorOfNonempty (chainState nodes initial step n) (nodes (n + 1))
        (step n (chainState nodes initial step n)) :=
  rfl

/-- The induced chain is independent of every classical selection inside the
differential data supply. -/
theorem chainState_policy_independent
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step₁ step₂ : StepAvailable (g := g) nodes) :
    ∀ n : ℕ, chainState nodes initial step₁ n =
      chainState nodes initial step₂ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [chainState_succ]

/-- A realized differential-induced chain along `nodes`.

Unlike `StepAvailable`, this witness stores successor data only at the states
that the chain actually reaches.  Thus constructing a `ReachableChain` never
requires differential data at counterfactual chain states. -/
structure ReachableChain
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) where
  state : ℕ → CartanChain.ChainState g
  initial_eq : state 0 = initial
  data : ∀ n : ℕ, Data (state n) (nodes (n + 1))
  successor_eq : ∀ n : ℕ, state (n + 1) = (data n).successor

@[simp]
theorem ReachableChain.state_zero
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial) :
    chain.state 0 = initial :=
  chain.initial_eq

@[simp]
theorem ReachableChain.state_succ
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial) (n : ℕ) :
    chain.state (n + 1) = (chain.data n).successor :=
  chain.successor_eq n

/-- Every positive-index state of a realized chain is anchored at the node
that produced it. -/
@[simp]
theorem ReachableChain.state_succ_anchor
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial) (n : ℕ) :
    (chain.state (n + 1)).anchor = nodes (n + 1) := by
  rw [chain.state_succ]
  exact (chain.data n).successor_anchor

/-- Each realized next node belongs to the strict Cartan source of its actual
predecessor state. -/
theorem ReachableChain.node_mem_predecessor_source
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial) (n : ℕ) :
    nodes (n + 1) ∈ (chain.state n).germ.source :=
  (chain.data n).anchor_mem_predecessor_source

/-- If the initial anchor is the zeroth node, all realized states are anchored
at their corresponding nodes. -/
theorem ReachableChain.state_anchor_eq_node
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial)
    (hinitial : initial.anchor = nodes 0) :
    ∀ n : ℕ, (chain.state n).anchor = nodes n := by
  intro n
  cases n with
  | zero => simpa using hinitial
  | succ n =>
      simpa [Nat.succ_eq_add_one] using chain.state_succ_anchor n

/-- Realized differential chains with the same nodes and initial state reach
the same state at every index.  This uses canonicity of differential-induced
successors and does not compare unused data policies. -/
theorem ReachableChain.state_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {nodes : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain₁ chain₂ : ReachableChain nodes initial) :
    ∀ n : ℕ, chain₁.state n = chain₂.state n := by
  intro n
  induction n with
  | zero => exact chain₁.initial_eq.trans chain₂.initial_eq.symm
  | succ n ih =>
      rw [chain₁.state_succ, chain₂.state_succ]
      exact (chain₁.data n).successor_eq_of_state_eq ih (chain₂.data n)

/-- The old universal policy produces a realized chain, but users of
`ReachableChain` need only retain the data on the resulting trajectory. -/
def reachableChainOfStepAvailable
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step : StepAvailable (g := g) nodes) :
    ReachableChain nodes initial where
  state := chainState nodes initial step
  initial_eq := rfl
  data := fun n =>
    Classical.choice (step n (chainState nodes initial step n))
  successor_eq := by
    intro n
    rw [chainState_succ]
    exact successorOfNonempty_eq
      (step n (chainState nodes initial step n))
      (Classical.choice (step n (chainState nodes initial step n)))

@[simp]
theorem reachableChainOfStepAvailable_state
    {g : ClosedSmoothRiemannianMetric 3 M} (nodes : ℕ → M)
    (initial : CartanChain.ChainState g)
    (step : StepAvailable (g := g) nodes) (n : ℕ) :
    (reachableChainOfStepAvailable nodes initial step).state n =
      chainState nodes initial step n :=
  rfl

end Chain


/--
Constant curvature produces differential-induced successor data at every
nonzero point of a sufficiently small old normal ball which lies in the old
strict Cartan source.
-/
theorem exists_data_on_punctured_ball
    [T2Space M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ ρ > (0 : ℝ),
      ∀ x₁ : M, x₁ ∈ s.germ.source →
        let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor
        let v := eM.symm ((chartAt E s.anchor) x₁)
        ‖v‖ < ρ → v ≠ 0 → Nonempty (Data s x₁) := by
  rcases
      DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := s.anchor) (p₀ := s.target) s.alignment with
    ⟨ρ, hρ, Afield, Bfield, DF, hDF, hfield⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x₁ hx₁
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) s.target
  let v : E := eM.symm ((chartAt E s.anchor) x₁)
  intro hv hvne
  have hsource :
      x₁ ∈ (chartAt E s.anchor).source ∧
        (chartAt E s.anchor) x₁ ∈ eM.target ∧
          v ∈ (CartanMap.tangentAlignmentOpenPartialHomeomorph
            s.alignment).source ∧
            s.alignment v ∈ eS.source ∧
              (chartAt E s.target)
                (GeodesicTransport.expAt roundSphereMetric3 s.target
                  (s.alignment v)) ∈ (chartAt E s.target).target := by
    simpa [CartanChain.ChainState.germ, eM, eS, v,
      CartanMap.openPartialHomeomorph] using hx₁
  have hxcoord :
      extChartAt I s.anchor x₁ = eM v := by
    simpa [eM, v, extChartAt_coe] using (eM.right_inv hsource.2.1).symm
  have hpcoord :
      extChartAt I s.target (s.map x₁) = eS (s.alignment v) := by
    have hright := (chartAt E s.target).right_inv hsource.2.2.2.2
    simpa [CartanChain.ChainState.map, CartanMap.cartanMap_apply,
      eM, eS, v, extChartAt_coe] using hright
  have hpold : s.map x₁ ∈ (extChartAt I s.target).source := by
    have hmap := (chartAt E s.target).map_target hsource.2.2.2.2
    simpa [CartanChain.ChainState.map, CartanMap.cartanMap_apply,
      eM, eS, v, extChartAt_source] using hmap
  rcases hfield v hv hvne with
    ⟨hsourceStrict, htargetStrict, _hinv, hmapStrict, hpull⟩
  refine ⟨⟨v, Afield v, Bfield v, ?_, ?_, ?_, hpold, ?_, ?_,
    hsourceStrict, htargetStrict, ?_, ?_⟩⟩
  · exact eM.symm.map_source hsource.2.1
  · exact hsource.2.2.2.1
  · simpa [extChartAt_source] using hsource.1
  · simpa [eM] using hxcoord
  · simpa [eS] using hpcoord
  · simpa [hDF v] using hmapStrict
  · intro u u'
    rw [← hDF v]
    exact hpull u u'

end DifferentialInducedSuccessor
end Poincare
