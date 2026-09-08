import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.DifferentialInducedSuccessor

/-!
# Supplied Cartan maps and differential successor witnesses

Normal charts, velocity frames, and coordinate hosts are explicit.
The patch frame is extended by the identity outside its retained anchors;
anchor laws only apply on the retained sets.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace CartanSuppliedDifferentialSuccessor
structure Interpretation (g : ClosedSmoothRiemannianMetric 3 M) where
  sourceAnchors : Set M
  targetAnchors : Set RoundSphere3
  sourceNormal : M → OpenPartialHomeomorph M E
  targetNormal : RoundSphere3 → OpenPartialHomeomorph RoundSphere3 E
  sourceFrame : M → E ≃L[ℝ] E
  targetFrame : RoundSphere3 → E ≃L[ℝ] E
  sourceHost : M → M
  targetHost : RoundSphere3 → RoundSphere3
  source_anchor_mem : ∀ x ∈ sourceAnchors, x ∈ (sourceNormal x).source
  source_anchor_zero : ∀ x ∈ sourceAnchors, sourceNormal x x = 0
  target_anchor_mem : ∀ p ∈ targetAnchors, p ∈ (targetNormal p).source
  target_anchor_zero : ∀ p ∈ targetAnchors, targetNormal p p = 0

def generic (g : ClosedSmoothRiemannianMetric 3 M) : Interpretation g where
  sourceAnchors := univ
  targetAnchors := univ
  sourceNormal := (CartanSourceExponential.genericFamily g).normal
  targetNormal := (CartanSourceExponential.genericFamily roundSphereMetric3).normal
  sourceFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  targetFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  sourceHost := id
  targetHost := id
  source_anchor_mem := fun x _ => (CartanSourceExponential.genericFamily g).anchor_mem_source x
  source_anchor_zero := fun x _ => (CartanSourceExponential.genericFamily g).normal_anchor x
  target_anchor_mem := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).anchor_mem_source p
  target_anchor_zero := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).normal_anchor p

def patchFrame {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) : E ≃L[ℝ] E :=
  @dite _ (x ∈ C.anchors) (Classical.propDecidable _) (fun hx =>
    InducedAlignment.continuousLinearEquivOfInvertible
      (FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x)
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx))
    (fun _ => ContinuousLinearEquiv.refl ℝ E)

def patch {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V) :
    Interpretation g where
  sourceAnchors := C.anchors
  targetAnchors := D.anchors
  sourceNormal := C.normal
  targetNormal := D.normal
  sourceFrame := patchFrame C
  targetFrame := patchFrame D
  sourceHost := fun _ => x₀
  targetHost := fun _ => p₀
  source_anchor_mem := C.anchor_mem_normal_source
  source_anchor_zero := C.normal_anchor
  target_anchor_mem := D.anchor_mem_normal_source
  target_anchor_zero := D.normal_anchor

def linear (Q : Interpretation g) (s : CartanChain.ChainState g) : E ≃L[ℝ] E :=
  ((Q.sourceFrame s.anchor).trans s.alignment.toContinuousLinearEquiv).trans
    (Q.targetFrame s.target).symm

def germ (Q : Interpretation g) (s : CartanChain.ChainState g) :
    OpenPartialHomeomorph M RoundSphere3 :=
  (Q.sourceNormal s.anchor).trans
    ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
      (Q.targetNormal s.target).symm)

def map (Q : Interpretation g) (s : CartanChain.ChainState g) : M → RoundSphere3 :=
  germ Q s

def sourceExp (Q : Interpretation g) (x : M) : OpenPartialHomeomorph E E :=
  (Q.sourceNormal x).symm.trans (chartAt E (Q.sourceHost x))

def targetExp (Q : Interpretation g) (p : RoundSphere3) : OpenPartialHomeomorph E E :=
  (Q.targetNormal p).symm.trans (chartAt E (Q.targetHost p))

def chartMap (Q : Interpretation g) (s : CartanChain.ChainState g) : E → E :=
  fun z => targetExp Q s.target (linear Q s ((sourceExp Q s.anchor).symm z))

def chartDifferential (Q : Interpretation g) (s : CartanChain.ChainState g)
    (A B : E ≃L[ℝ] E) : E →L[ℝ] E :=
  ((A.symm.trans (linear Q s)).trans B : E ≃L[ℝ] E)

def reanchoredChartMap (Q : Interpretation g) (s : CartanChain.ChainState g)
    (z : M) : E → E :=
  fun w => extChartAt I (map Q s z) (map Q s ((extChartAt I z).symm w))

structure CoordinateData (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M) where
  source_anchor_valid : s.anchor ∈ Q.sourceAnchors
  target_anchor_valid : s.target ∈ Q.targetAnchors
  source_mem : z ∈ (germ Q s).source
  v : E
  A : E ≃L[ℝ] E
  B : E ≃L[ℝ] E
  source_vector_mem : v ∈ (sourceExp Q s.anchor).source
  target_vector_mem : linear Q s v ∈ (targetExp Q s.target).source
  source_mem_oldChart : z ∈ (extChartAt I (Q.sourceHost s.anchor)).source
  target_mem_oldChart : map Q s z ∈ (extChartAt I (Q.targetHost s.target)).source
  source_coordinate : extChartAt I (Q.sourceHost s.anchor) z = sourceExp Q s.anchor v
  target_coordinate : extChartAt I (Q.targetHost s.target) (map Q s z) =
    targetExp Q s.target (linear Q s v)
  source_exp_derivative : HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E) v
  target_exp_derivative : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E) (linear Q s v)
  cartan_chart_derivative : HasStrictFDerivAt (chartMap Q s)
    (chartDifferential Q s A B) (sourceExp Q s.anchor v)
  metric_pullback : ∀ u u' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost s.target)
      (targetExp Q s.target (linear Q s v))
      (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
    CovariantDerivative.chartMetric g.inner (Q.sourceHost s.anchor)
      (sourceExp Q s.anchor v) u u'

structure Data (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    extends CoordinateData Q s z where
  alignment : CartanMap.TangentAlignment g z (map Q s z)
  hasFDerivAt_reanchoredChartMap : HasFDerivAt (reanchoredChartMap Q s z)
    (alignment.toContinuousLinearEquiv : E →L[ℝ] E) (extChartAt I z z)

def Data.successor {Q : Interpretation g} {s : CartanChain.ChainState g} {z : M}
    (d : Data Q s z) : CartanChain.ChainState g :=
  ⟨z, map Q s z, d.alignment⟩

/-- Retained anchors lie in the supplied germ source and map to the target anchor. -/
theorem anchor_laws : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g),
  s.anchor ∈ Q.sourceAnchors → s.target ∈ Q.targetAnchors →
  s.anchor ∈ (germ Q s).source ∧ map Q s s.anchor = s.target := by
  intro Q s hx hp
  have hzero : (0 : E) ∈ (Q.targetNormal s.target).target := by
    simpa only [Q.target_anchor_zero s.target hp] using
      (Q.targetNormal s.target).map_source (Q.target_anchor_mem s.target hp)
  constructor
  · change s.anchor ∈ (Q.sourceNormal s.anchor).source ∧
      Q.sourceNormal s.anchor s.anchor ∈
        ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
          (Q.targetNormal s.target).symm).source
    refine ⟨Q.source_anchor_mem s.anchor hx, ?_⟩
    simpa [Q.source_anchor_zero s.anchor hx] using hzero
  · change (Q.targetNormal s.target).symm
      (linear Q s (Q.sourceNormal s.anchor s.anchor)) = s.target
    rw [Q.source_anchor_zero s.anchor hx, map_zero,
      ← Q.target_anchor_zero s.target hp]
    exact (Q.targetNormal s.target).left_inv (Q.target_anchor_mem s.target hp)

/-- Identity frames and generic normals recover the old total forward map. -/
theorem generic_map_eq : ∀ (s : CartanChain.ChainState g), map (generic g) s = s.map := by
  intro s
  funext z
  change ((CartanSourceExponential.genericFamily roundSphereMetric3).normal s.target).symm
    (s.alignment.toContinuousLinearEquiv
      ((CartanSourceExponential.genericFamily g).normal s.anchor z)) =
    CartanMap.cartanMap g s.anchor s.target s.alignment z
  rw [CartanSourceExponential.genericFamily_apply, CartanMap.cartanMap_apply]
  rfl

/-- The stored host-chart coordinate identifies the actual supplied normal vector. -/
theorem vector_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.v = Q.sourceNormal s.anchor z := by
  intro Q s z d
  have hz : z ∈ (chartAt E (Q.sourceHost s.anchor)).source := by
    simpa only [extChartAt_source] using d.source_mem_oldChart
  have hc : (chartAt E (Q.sourceHost s.anchor)) z =
      (chartAt E (Q.sourceHost s.anchor)) ((Q.sourceNormal s.anchor).symm d.v) := by
    simpa only [extChartAt_coe] using d.source_coordinate
  have he : z = (Q.sourceNormal s.anchor).symm d.v :=
    (chartAt E (Q.sourceHost s.anchor)).injOn hz d.source_vector_mem.2 hc
  calc
    d.v = Q.sourceNormal s.anchor ((Q.sourceNormal s.anchor).symm d.v) :=
      ((Q.sourceNormal s.anchor).right_inv d.source_vector_mem.1).symm
    _ = Q.sourceNormal s.anchor z := congrArg (Q.sourceNormal s.anchor) he.symm

/-- The successor retains its new anchor, actual target, and predecessor source evidence. -/
theorem successor_fields : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.successor.anchor = z ∧
  d.successor.target = map Q s z ∧ z ∈ (germ Q s).source := by
  intro Q s z d
  exact ⟨rfl, rfl, d.source_mem⟩

/-- A zero stored normal vector forces the new point to be the predecessor anchor. -/
theorem eq_anchor_of_vector_eq_zero :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z), d.v = 0 → z = s.anchor := by
  intro Q s z d hv
  apply (Q.sourceNormal s.anchor).injOn d.source_mem.1
    (Q.source_anchor_mem s.anchor d.source_anchor_valid)
  rw [← vector_eq Q s z d, hv,
    Q.source_anchor_zero s.anchor d.source_anchor_valid]

end CartanSuppliedDifferentialSuccessor
end Poincare
