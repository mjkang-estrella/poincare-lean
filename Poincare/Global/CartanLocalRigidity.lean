import Poincare.Global.CartanOverlapContinuation
import Poincare.Global.GermDeterminacy
import Poincare.Global.OffAnchorNaturality
import Poincare.Global.RoundSphereSimpleConnected

/-!
# Local Cartan rigidity from common re-centering data

`CartanOverlapContinuation` reduces global overlap compatibility to a local
uniqueness statement.  This module proves the part of that local statement
which follows directly from the explicit Cartan-germ construction.

After two germs are re-centered at the same source point and target value,
their re-centered tangent alignments are their complete remaining data.  If
those linear actions agree, `GermDeterminacy` identifies the re-centered germs
on their common strict source.  Intersecting with the two original re-centering
neighborhoods gives the open equality neighborhood required by connected
continuation.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanLocalRigidity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Two same-anchor, same-target Cartan germs with the same tangent action agree
locally at the anchor.

In fact `GermDeterminacy` proves equality on the whole common strict source;
this theorem packages it in the open-neighborhood shape used by overlap
continuation.
-/
theorem sameAnchor_cartanGerms_locally_eq_of_alignment_apply_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {z : M} {p : RoundSphere3}
    (L₁ L₂ : CartanMap.TangentAlignment g z p)
    (hL : ∀ v : E, L₁ v = L₂ v) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      EqOn (CartanMap.openPartialHomeomorph g z p L₁)
        (CartanMap.openPartialHomeomorph g z p L₂)
        (V ∩
          ((CartanMap.openPartialHomeomorph g z p L₁).source ∩
            (CartanMap.openPartialHomeomorph g z p L₂).source)) := by
  let F₁ := CartanMap.openPartialHomeomorph g z p L₁
  let F₂ := CartanMap.openPartialHomeomorph g z p L₂
  have hdet : EqOn F₁ F₂ (F₁.source ∩ F₂.source) := by
    simpa [F₁, F₂] using
      (GermDeterminacy.cartanGerm_determinacy_of_tangentAlignment_apply_eq
        (g := g) (x₀ := z) (p₀ := p) (L₁ := L₁) (L₂ := L₂) hL).2
  refine ⟨F₁.source ∩ F₂.source,
    F₁.open_source.inter F₂.open_source, ?_, ?_⟩
  · exact ⟨CartanMap.anchor_mem_source g z p L₁,
      CartanMap.anchor_mem_source g z p L₂⟩
  · intro x hx
    exact hdet hx.2

/--
The exact local data needed to compare two arbitrary carried Cartan germs at
an equality point.

Each carried germ is locally re-centered to a Cartan germ based at `z` and
targeted at `F z`.  The two re-centered tangent actions are required to agree.
The latter is precisely the value-and-differential uniqueness input; all
subsequent propagation is formal.
-/
def CommonDifferentialRecenterDataAt
    (g : ClosedSmoothRiemannianMetric 3 M)
    (F G : OpenPartialHomeomorph M RoundSphere3) (z : M) : Prop :=
  ∃ (L₁ L₂ : CartanMap.TangentAlignment g z (F z)),
    (∀ v : E, L₁ v = L₂ v) ∧
      EqOn F (CartanMap.openPartialHomeomorph g z (F z) L₁)
        (F.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₁).source) ∧
      EqOn G (CartanMap.openPartialHomeomorph g z (F z) L₂)
        (G.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₂).source)

/--
Common differential re-centering supplies the local equality-propagation
hypothesis required by `CartanOverlapContinuation`.
-/
theorem locally_eq_of_commonDifferentialRecenterDataAt
    {g : ClosedSmoothRiemannianMetric 3 M}
    {F G : OpenPartialHomeomorph M RoundSphere3} {z : M}
    (_hz : z ∈ F.source ∩ G.source)
    (hdata : CommonDifferentialRecenterDataAt g F G z) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      EqOn F G (V ∩ (F.source ∩ G.source)) := by
  rcases hdata with ⟨L₁, L₂, hL, hF, hG⟩
  let H₁ := CartanMap.openPartialHomeomorph g z (F z) L₁
  let H₂ := CartanMap.openPartialHomeomorph g z (F z) L₂
  have hdet : EqOn H₁ H₂ (H₁.source ∩ H₂.source) := by
    simpa [H₁, H₂] using
      (GermDeterminacy.cartanGerm_determinacy_of_tangentAlignment_apply_eq
        (g := g) (x₀ := z) (p₀ := F z) (L₁ := L₁) (L₂ := L₂) hL).2
  refine ⟨H₁.source ∩ H₂.source,
    H₁.open_source.inter H₂.open_source, ?_, ?_⟩
  · exact ⟨CartanMap.anchor_mem_source g z (F z) L₁,
      CartanMap.anchor_mem_source g z (F z) L₂⟩
  · intro x hx
    have hxV : x ∈ H₁.source ∩ H₂.source := hx.1
    have hxFG : x ∈ F.source ∩ G.source := hx.2
    calc
      F x = H₁ x := hF ⟨hxFG.1, hxV.1⟩
      _ = H₂ x := hdet hxV
      _ = G x := (hG ⟨hxFG.2, hxV.2⟩).symm

/--
A single common re-centered Cartan germ is a convenient sufficient form of
`CommonDifferentialRecenterDataAt`.
-/
theorem commonDifferentialRecenterDataAt_of_common_recenter
    {g : ClosedSmoothRiemannianMetric 3 M}
    {F G : OpenPartialHomeomorph M RoundSphere3} {z : M}
    (L : CartanMap.TangentAlignment g z (F z))
    (hF : EqOn F (CartanMap.openPartialHomeomorph g z (F z) L)
      (F.source ∩ (CartanMap.openPartialHomeomorph g z (F z) L).source))
    (hG : EqOn G (CartanMap.openPartialHomeomorph g z (F z) L)
      (G.source ∩ (CartanMap.openPartialHomeomorph g z (F z) L).source)) :
    CommonDifferentialRecenterDataAt g F G z := by
  exact ⟨L, L, fun _ => rfl, hF, hG⟩

/--
The charted re-centered exponential identities naturally produced by the
geodesic re-anchor cascade give `CommonDifferentialRecenterDataAt` directly.

No further chart algebra is needed: each displayed right-hand side is
definitionally the corresponding same-anchor Cartan map.
-/
theorem commonDifferentialRecenterDataAt_of_charted_recenter_identities
    {g : ClosedSmoothRiemannianMetric 3 M}
    {F G : OpenPartialHomeomorph M RoundSphere3} {z : M}
    (L₁ L₂ : CartanMap.TangentAlignment g z (F z))
    (hL : ∀ v : E, L₁ v = L₂ v)
    (hF :
      ∀ x ∈ F.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₁).source,
        F x =
          (chartAt E (F z)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (F z)
              (L₁
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) z).symm ((chartAt E z) x)))))
    (hG :
      ∀ x ∈ G.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₂).source,
        G x =
          (chartAt E (F z)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (F z)
              (L₂
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) z).symm ((chartAt E z) x))))) :
    CommonDifferentialRecenterDataAt g F G z := by
  refine ⟨L₁, L₂, hL, ?_, ?_⟩
  · intro x hx
    change F x = CartanMap.cartanMap g z (F z) L₁ x
    exact hF x hx
  · intro x hx
    change G x = CartanMap.cartanMap g z (F z) L₂ x
    exact hG x hx

/--
Charted re-centered exponential identities plus equality of the tangent
actions give the local overlap equality neighborhood in one step.
-/
theorem locally_eq_of_charted_recenter_identities
    {g : ClosedSmoothRiemannianMetric 3 M}
    {F G : OpenPartialHomeomorph M RoundSphere3} {z : M}
    (hz : z ∈ F.source ∩ G.source)
    (L₁ L₂ : CartanMap.TangentAlignment g z (F z))
    (hL : ∀ v : E, L₁ v = L₂ v)
    (hF :
      ∀ x ∈ F.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₁).source,
        F x =
          (chartAt E (F z)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (F z)
              (L₁
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) z).symm ((chartAt E z) x)))))
    (hG :
      ∀ x ∈ G.source ∩
          (CartanMap.openPartialHomeomorph g z (F z) L₂).source,
        G x =
          (chartAt E (F z)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (F z)
              (L₂
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) z).symm ((chartAt E z) x))))) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      EqOn F G (V ∩ (F.source ∩ G.source)) :=
  locally_eq_of_commonDifferentialRecenterDataAt hz
    (commonDifferentialRecenterDataAt_of_charted_recenter_identities
      L₁ L₂ hL hF hG)

/--
Concrete chain-state form of local value-and-differential uniqueness.

The two hypotheses `h₁` and `h₂` are the existing
`RigidStepCompatibleWith` outputs targeted by the re-anchor/naturality
cascade.  Equality of the carried target values and heterogeneous equality of
the induced tangent alignments identify the two re-centered Cartan germs by
`CartanContinuation.openPartialHomeomorph_eq_of_anchor_data_eq`.  The two
rigid steps then identify the original germs on an open neighborhood of `z`.
-/
theorem locally_eq_of_rigidSteps_of_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (L₁ : CartanMap.TangentAlignment g z (s₁.map z))
    (L₂ : CartanMap.TangentAlignment g z (s₂.map z))
    (hp : s₁.map z = s₂.map z) (hL : HEq L₁ L₂)
    (h₁ : InducedAlignment.CompatibleStep.RigidStepCompatibleWith s₁ z L₁)
    (h₂ : InducedAlignment.CompatibleStep.RigidStepCompatibleWith s₂ z L₂) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
      EqOn s₁.germ s₂.germ (V ∩ (s₁.germ.source ∩ s₂.germ.source)) := by
  let n₁ := InducedAlignment.CompatibleStep.nextWithAlignment s₁ z L₁
  let n₂ := InducedAlignment.CompatibleStep.nextWithAlignment s₂ z L₂
  have hn : n₁.germ = n₂.germ := by
    simpa [n₁, n₂, InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ, CartanChain.ChainState.map] using
      (CartanContinuation.openPartialHomeomorph_eq_of_anchor_data_eq
        (g := g) (x₀ := z) hp hL)
  refine ⟨n₁.germ.source ∩ n₂.germ.source,
    n₁.germ.open_source.inter n₂.germ.open_source, ?_, ?_⟩
  · constructor
    · simpa [n₁, InducedAlignment.CompatibleStep.nextWithAlignment,
        CartanChain.ChainState.germ] using
        CartanMap.anchor_mem_source g z (s₁.map z) L₁
    · simpa [n₂, InducedAlignment.CompatibleStep.nextWithAlignment,
        CartanChain.ChainState.germ] using
        CartanMap.anchor_mem_source g z (s₂.map z) L₂
  · intro x hx
    have hxV : x ∈ n₁.germ.source ∩ n₂.germ.source := hx.1
    have hxold : x ∈ s₁.germ.source ∩ s₂.germ.source := hx.2
    have hmid : n₁.germ x = n₂.germ x := by
      rw [hn]
    calc
      s₁.germ x = n₁.germ x := h₁ ⟨hxold.1, hxV.1⟩
      _ = n₂.germ x := hmid
      _ = s₂.germ x := (h₂ ⟨hxold.2, hxV.2⟩).symm

/--
The same two rigid re-anchor steps also produce the bundled common
differential re-centering data used by the componentwise globalization
interface.

The first induced alignment is used as the common alignment.  Equality of the
two re-centered germs follows from target equality and heterogeneous alignment
equality, so the second rigid step can be rewritten to that common germ.
-/
theorem commonDifferentialRecenterDataAt_of_rigidSteps_of_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (z : M)
    (L₁ : CartanMap.TangentAlignment g z (s₁.map z))
    (L₂ : CartanMap.TangentAlignment g z (s₂.map z))
    (hp : s₁.map z = s₂.map z) (hL : HEq L₁ L₂)
    (h₁ : InducedAlignment.CompatibleStep.RigidStepCompatibleWith s₁ z L₁)
    (h₂ : InducedAlignment.CompatibleStep.RigidStepCompatibleWith s₂ z L₂) :
    CommonDifferentialRecenterDataAt g s₁.germ s₂.germ z := by
  let n₁ := InducedAlignment.CompatibleStep.nextWithAlignment s₁ z L₁
  let n₂ := InducedAlignment.CompatibleStep.nextWithAlignment s₂ z L₂
  have hn : n₁.germ = n₂.germ := by
    simpa [n₁, n₂, InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ, CartanChain.ChainState.map] using
      (CartanContinuation.openPartialHomeomorph_eq_of_anchor_data_eq
        (g := g) (x₀ := z) hp hL)
  refine ⟨L₁, L₁, fun _ => rfl, h₁, ?_⟩
  intro x hx
  have hx₂ : x ∈ s₂.germ.source ∩ n₂.germ.source := by
    refine ⟨hx.1, ?_⟩
    rw [← hn]
    exact hx.2
  calc
    s₂.germ x = n₂.germ x := h₂ hx₂
    _ = n₁.germ x := by rw [hn]

/-- A Cartan state associated to one member of an anchored Cartan family. -/
def anchoredFamilyState
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M → RoundSphere3)
    (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)) (x : M) :
    CartanChain.ChainState g where
  anchor := x
  target := p x
  alignment := L x

@[simp]
theorem anchoredFamilyState_germ
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M → RoundSphere3)
    (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)) (x : M) :
    (anchoredFamilyState g p L x).germ =
      CartanMap.openPartialHomeomorph g x (p x) (L x) :=
  rfl

@[simp]
theorem anchoredFamilyState_map
    (g : ClosedSmoothRiemannianMetric 3 M) (p : M → RoundSphere3)
    (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)) (x : M) :
    (anchoredFamilyState g p L x).map =
      CartanMap.cartanMap g x (p x) (L x) :=
  rfl

/--
Unit-curvature payload reduced to component seeds and common differential
re-centering at equality points.

The re-centering clauses are the outputs naturally targeted by the existing
geodesic re-anchor and exponential-naturality cascade.  This proposition no
longer asks for equality at every point of an overlap.
-/
def UnitCurvatureComponentwiseDifferentialRecenterRigidity3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          ∀ x y : M,
            let Fx := CartanMap.openPartialHomeomorph g x (p x) (L x)
            let Fy := CartanMap.openPartialHomeomorph g y (p y) (L y)
            (∀ z ∈ Fx.source ∩ Fy.source,
              ∃ w ∈ connectedComponentIn (Fx.source ∩ Fy.source) z,
                Fx w = Fy w) ∧
              (∀ z ∈ Fx.source ∩ Fy.source, Fx z = Fy z →
                CommonDifferentialRecenterDataAt g Fx Fy z)

/--
Minimal induced-alignment path-independence payload for unit-curvature Cartan
continuation.

The first clause supplies one carried-value equality seed in every connected
component of every germ overlap.  The second clause says that, at any such
equality point, both chain histories provide the existing rigid re-anchor step
and their induced tangent alignments are heterogeneously equal.  The `HEq` is
the precise path-independence datum because the two alignments initially have
dependent target types; `hvalue` identifies those targets.

No all-point overlap equality is assumed.

The component seed is kept explicit: the current chain API proves that each
germ contains its own anchor, but does not place a common chain node in every
connected component of an arbitrary pairwise overlap.
-/
def UnitCurvatureInducedAlignmentPathIndependence3
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      ∃ (p : M → RoundSphere3)
        (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
          (∀ x y z : M,
            z ∈ (anchoredFamilyState g p L x).germ.source ∩
                (anchoredFamilyState g p L y).germ.source →
              ∃ w ∈ connectedComponentIn
                  ((anchoredFamilyState g p L x).germ.source ∩
                    (anchoredFamilyState g p L y).germ.source) z,
                (anchoredFamilyState g p L x).germ w =
                  (anchoredFamilyState g p L y).germ w) ∧
          (∀ x y z : M,
            z ∈ (anchoredFamilyState g p L x).germ.source ∩
                (anchoredFamilyState g p L y).germ.source →
            (hvalue : (anchoredFamilyState g p L x).map z =
              (anchoredFamilyState g p L y).map z) →
              ∃ (Lx : CartanMap.TangentAlignment g z
                    ((anchoredFamilyState g p L x).map z))
                (Ly : CartanMap.TangentAlignment g z
                    ((anchoredFamilyState g p L y).map z)),
                InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                    (anchoredFamilyState g p L x) z Lx ∧
                  InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                    (anchoredFamilyState g p L y) z Ly ∧
                  HEq Lx Ly)

/--
Induced-alignment path independence supplies the componentwise differential
re-centering payload.
-/
theorem componentwiseDifferentialRecenterRigidity_of_inducedAlignmentPathIndependence
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureInducedAlignmentPathIndependence3 (M := M)) :
    UnitCurvatureComponentwiseDifferentialRecenterRigidity3 (M := M) := by
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hseed, hpath⟩
  refine ⟨p, L, ?_⟩
  intro x y
  let sx := anchoredFamilyState g p L x
  let sy := anchoredFamilyState g p L y
  constructor
  · intro z hz
    simpa [sx, sy] using hseed x y z (by simpa [sx, sy] using hz)
  · intro z hz hvalue
    have hz' : z ∈ sx.germ.source ∩ sy.germ.source := by
      simpa [sx, sy] using hz
    have hvalue' : sx.map z = sy.map z := by
      simpa [sx, sy] using hvalue
    rcases hpath x y z (by simpa [sx, sy] using hz')
        (by simpa [sx, sy] using hvalue') with
      ⟨Lx, Ly, hx, hy, hLxy⟩
    simpa [sx, sy] using
      commonDifferentialRecenterDataAt_of_rigidSteps_of_alignment_heq
        sx sy z Lx Ly hvalue' hLxy hx hy

/--
The same path-independence payload directly supplies componentwise overlap
local rigidity.  This route uses the concrete two-rigid-step local theorem,
without first repackaging the steps as common differential re-centering data.
-/
theorem componentwiseOverlapLocalRigidity_of_inducedAlignmentPathIndependence
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureInducedAlignmentPathIndependence3 (M := M)) :
    CartanOverlapContinuation.UnitCurvatureComponentwiseOverlapLocalRigidity3
      (M := M) := by
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hseed, hpath⟩
  refine ⟨p, L, ?_⟩
  intro x y
  let sx := anchoredFamilyState g p L x
  let sy := anchoredFamilyState g p L y
  constructor
  · intro z hz
    simpa [sx, sy] using hseed x y z (by simpa [sx, sy] using hz)
  · intro z hz hvalue
    have hz' : z ∈ sx.germ.source ∩ sy.germ.source := by
      simpa [sx, sy] using hz
    have hvalue' : sx.map z = sy.map z := by
      simpa [sx, sy] using hvalue
    rcases hpath x y z (by simpa [sx, sy] using hz')
        (by simpa [sx, sy] using hvalue') with
      ⟨Lx, Ly, hx, hy, hLxy⟩
    simpa [sx, sy] using
      locally_eq_of_rigidSteps_of_alignment_heq
        sx sy z Lx Ly hvalue' hLxy hx hy

/--
The common differential re-centering payload supplies the componentwise local
rigidity interface of `CartanOverlapContinuation`.
-/
theorem componentwiseOverlapLocalRigidity_of_differentialRecenterRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureComponentwiseDifferentialRecenterRigidity3 (M := M)) :
    CartanOverlapContinuation.UnitCurvatureComponentwiseOverlapLocalRigidity3
      (M := M) := by
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hL⟩
  refine ⟨p, L, ?_⟩
  intro x y
  rcases hL x y with ⟨hseed, hrecenter⟩
  refine ⟨hseed, ?_⟩
  intro z hz hEq
  exact locally_eq_of_commonDifferentialRecenterDataAt hz
    (hrecenter z hz hEq)

/--
Consequently, component seeds plus common value-and-differential re-centering
prove the all-anchor charted Cartan naturality statement.
-/
theorem chartedRecenterNaturality_of_differentialRecenterRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureComponentwiseDifferentialRecenterRigidity3 (M := M)) :
    CartanOverlapCompatibility.UnitCurvatureChartedRecenterNaturality3
      (M := M) :=
  CartanOverlapContinuation.chartedRecenterNaturality_of_componentwiseOverlapLocalRigidity
    (componentwiseOverlapLocalRigidity_of_differentialRecenterRigidity h)

/-- The same differential re-centering payload supplies the compatible atlas. -/
theorem compatibleCartanAtlas_of_differentialRecenterRigidity
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureComponentwiseDifferentialRecenterRigidity3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  CartanOverlapContinuation.compatibleCartanAtlas_of_componentwiseOverlapLocalRigidity
    (componentwiseOverlapLocalRigidity_of_differentialRecenterRigidity h)

/-- Induced-alignment path independence supplies the compatible Cartan atlas. -/
theorem compatibleCartanAtlas_of_inducedAlignmentPathIndependence
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureInducedAlignmentPathIndependence3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  CartanOverlapContinuation.compatibleCartanAtlas_of_componentwiseOverlapLocalRigidity
    (componentwiseOverlapLocalRigidity_of_inducedAlignmentPathIndependence h)

/--
Induced-alignment path independence discharges unit-curvature sphere
recognition; simple connectivity of the literal round sphere is supplied by
the existing stereographic Van Kampen theorem.
-/
theorem unitConstantCurvatureSphereRecognition3_of_inducedAlignmentPathIndependence
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (h : UnitCurvatureInducedAlignmentPathIndependence3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    (compatibleCartanAtlas_of_inducedAlignmentPathIndependence h)

end CartanLocalRigidity
end Poincare
