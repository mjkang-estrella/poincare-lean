import Poincare.Global.CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope
import Poincare.Global.CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
import Poincare.Global.DifferentialSuccessorEqualityStabilityReduction

/-!
# Canonical-only Cartan continuation and comparison lifting

The provenance-retaining compared-successor construction first builds generic
target data and then transfers it to `canonicalFamily`.  Uniformizing that
transfer in the target anchor exposes a regularity gap for the independently
chosen generic target exponential.

This module separates the two logically independent jobs.

* Canonical successor data are uniformized using only `canonicalFamily`.
* The remaining conversion to the legacy compared locus is recorded by an
  exact conditional continuation locus: wherever canonical data exist, a
  compared step can be selected.

The latter contains no chart-agreement radius, no generic-target source locus,
and no lower-semicontinuity premise.  Its diagonal is automatic under unit
curvature, so openness (or directly neighborhood membership) is enough.

There is also a genuinely canonical-only recognition endpoint.  A restricted
compatible atlas made from canonical Cartan maps is shrunk independently at
each anchor to the fixed-anchor canonical/generic germ-comparison patch.  It
then enters the existing restricted-atlas consumer without any uniformity of
those patches in the target anchor.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyComparedCanonicalContinuation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanCanonicalFamilyGermComparison
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalFamilyComparedForwardNormalRegularity
open CartanCanonicalFamilyLocalUniformData
open CartanCanonicalFamilyProvenanceLocalUniformData

/-! ## A canonical restricted Cartan atlas -/

/-- Restricted compatibility stated entirely for the normalized target
family.  No generic target exponential occurs in this structure. -/
structure CanonicalRestrictedCompatibleCartanAtlasData3
    (g : ClosedSmoothRiemannianMetric 3 M) where
  target : M → RoundSphere3
  alignment : ∀ x : M, CartanMap.TangentAlignment g x (target x)
  domain : M → Set M
  isOpen_domain : ∀ x : M, IsOpen (domain x)
  anchor_mem_domain : ∀ x : M, x ∈ domain x
  domain_subset_source : ∀ x : M,
    domain x ⊆
      (CartanTargetExponential.openPartialHomeomorph canonicalFamily
        g x (target x) (alignment x)).source
  compatible : ∀ x y : M,
    EqOn
      (CartanTargetExponential.openPartialHomeomorph canonicalFamily
        g x (target x) (alignment x))
      (CartanTargetExponential.openPartialHomeomorph canonicalFamily
        g y (target y) (alignment y))
      (domain x ∩ domain y)

namespace CanonicalRestrictedCompatibleCartanAtlasData3

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The canonical state underlying one member of a canonical restricted
atlas. -/
def state
    (data : CanonicalRestrictedCompatibleCartanAtlasData3 g) (x : M) :
    ChainState canonicalFamily g :=
  ChainState.mk x (data.target x) (data.alignment x)

/-- Fixed-anchor germ comparison supplies an open equality patch.  The patch
may depend arbitrarily on the anchor; no moving-target regularity is used. -/
theorem exists_open_canonicalGenericAgreement
    (data : CanonicalRestrictedCompatibleCartanAtlasData3 g) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U,
        (data.state x).map z =
          (canonicalToGenericState (data.state x)).map z := by
  have heq := canonicalState_map_eventuallyEq_genericState (data.state x)
  have hset :
      {z : M | (data.state x).map z =
        (canonicalToGenericState (data.state x)).map z} ∈ nhds x := by
    simpa [state] using heq
  rcases mem_nhds_iff.mp hset with ⟨U, hsubset, hU, hxU⟩
  exact ⟨U, hU, hxU, fun z hz ↦ hsubset hz⟩

/-- Shrink a canonical compatible atlas to fixed-anchor germ-agreement
patches and obtain the legacy generic restricted atlas.

Only the already proved comparison at each individual anchor is used.  In
particular, the patches are not required to have a common radius or to vary
continuously with either source or target anchor. -/
noncomputable def toGenericRestrictedCompatible
    [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (data : CanonicalRestrictedCompatibleCartanAtlasData3 g) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g := by
  classical
  choose U hU hxU hEq using data.exists_open_canonicalGenericAgreement
  exact
    { target := data.target
      alignment := data.alignment
      domain := fun x ↦
        (data.domain x ∩ U x) ∩
          (canonicalToGenericState (data.state x)).germ.source
      isOpen_domain := fun x ↦
        ((data.isOpen_domain x).inter (hU x)).inter
          (canonicalToGenericState (data.state x)).germ.open_source
      anchor_mem_domain := by
        intro x
        refine ⟨⟨data.anchor_mem_domain x, hxU x⟩, ?_⟩
        exact CartanMap.anchor_mem_source
          g x (data.target x) (data.alignment x)
      domain_subset_source := by
        intro x z hz
        exact hz.2
      compatible := by
        intro x y z hz
        change
          (canonicalToGenericState (data.state x)).map z =
            (canonicalToGenericState (data.state y)).map z
        calc
          (canonicalToGenericState (data.state x)).map z =
              (data.state x).map z := (hEq x z hz.1.1.2).symm
          _ = (data.state y).map z :=
            data.compatible x y ⟨hz.1.1.1, hz.2.1.1⟩
          _ = (canonicalToGenericState (data.state y)).map z :=
            hEq y z hz.2.1.2 }

/-- Canonical restricted compatibility is already sufficient for the
existing generic restricted-atlas recognition consumer. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRestrictedCompatibleCartanAtlas
    [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (hcanonical : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g 1 →
        Nonempty (CanonicalRestrictedCompatibleCartanAtlasData3 g)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  rcases hcanonical g hcurv with ⟨data⟩
  exact ⟨data.toGenericRestrictedCompatible⟩

end CanonicalRestrictedCompatibleCartanAtlasData3

/-! ## Canonical successor-radius envelopes -/

section Compact

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- A generic-source normal radius is canonical-admissible when it produces
`canonicalFamily` successor data for every dependent alignment.  No generic
target chart or comparison package occurs in this definition. -/
def CanonicalNormalRadiusAdmissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) (radius : ℝ) : Prop :=
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
    z ∈ ((CartanSourceExponential.genericFamily g).normal x).source →
    ‖(CartanSourceExponential.genericFamily g).normal x z‖ < radius →
      Nonempty
        (Data canonicalFamily (ChainState.mk x p L) z)

/-- Canonical radius admissibility is downward closed. -/
theorem CanonicalNormalRadiusAdmissible.mono
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x : M} {p : RoundSphere3} {r s : ℝ}
    (h : CanonicalNormalRadiusAdmissible g x p r)
    (hsr : s ≤ r) :
    CanonicalNormalRadiusAdmissible g x p s := by
  intro L z hzSource hzNorm
  exact h L z hzSource (hzNorm.trans_le hsr)

/-- A proof-independent positive lower-semicontinuous radius family for
canonical successor data. -/
structure LocallyUniformCanonicalRadiusEnvelope
    (g : ClosedSmoothRiemannianMetric 3 M) where
  radius : M → RoundSphere3 → ℝ
  positive : ∀ (x : M) (p : RoundSphere3), 0 < radius x p
  lowerSemicontinuous : LowerSemicontinuous
    (fun xp : M × RoundSphere3 ↦ radius xp.1 xp.2)
  admissible : ∀ (x : M) (p : RoundSphere3),
    CanonicalNormalRadiusAdmissible g x p (radius x p)

/-- A positive lower-semicontinuous minorant of the curvature-selected
canonical radius is a canonical radius envelope. -/
def canonicalRadiusEnvelope_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalNormalAnchorTargetRadius hcurv x p) :
    LocallyUniformCanonicalRadiusEnvelope g where
  radius := pairRadius
  positive := hpositive
  lowerSemicontinuous := hlower
  admissible := by
    intro x p L z hzSource hzNorm
    apply
      nonempty_canonical_data_of_normal_lt_canonicalNormalAnchorTargetRadius
        hcurv x p L z hzSource
    exact hzNorm.trans_le (hminorant x p)

/-- A canonical envelope gives a source-local radius uniform over the entire
compact target sphere. -/
theorem exists_chartLocal_genericNormal_canonicalData_of_radiusEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (R : LocallyUniformCanonicalRadiusEnvelope g)
    (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ rho > (0 : ℝ),
        ∀ (x : M), x ∈ U →
          ∀ (p : RoundSphere3)
            (L : CartanMap.TangentAlignment g x p) (z : M),
            z ∈ ((CartanSourceExponential.genericFamily g).normal x).source →
            ‖(CartanSourceExponential.genericFamily g).normal x z‖ < rho →
              Nonempty (Data canonicalFamily (ChainState.mk x p L) z) := by
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_positive_lowerSemicontinuous_source_minorant_of_compact_target
        R.radius R.positive R.lowerSemicontinuous with
    ⟨sourceRadius, hsourcePositive, hsourceLower, hsourceMinorant⟩
  let rho : ℝ := sourceRadius x₀ / 2
  have hrho : 0 < rho := half_pos (hsourcePositive x₀)
  let U : Set M := sourceRadius ⁻¹' Ioi rho
  have hU : IsOpen U := hsourceLower.isOpen_preimage rho
  have hx₀U : x₀ ∈ U := by
    change rho < sourceRadius x₀
    dsimp only [rho]
    linarith [hsourcePositive x₀]
  refine ⟨U, hU, hx₀U, rho, hrho, ?_⟩
  intro x hx p L z hzSource hzNorm
  exact R.admissible x p L z hzSource
    (hzNorm.trans_le ((le_of_lt hx).trans (hsourceMinorant x p)))

/-- The exact local generic-normal control cover and a canonical radius
envelope produce the canonical supplied-family successor-data neighborhood.

This theorem contains no target-chart comparison or provenance package. -/
theorem canonicalSuccessorDataNeighborhood_of_controlledLocalFamilyCover_of_radiusEnvelope
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (R : LocallyUniformCanonicalRadiusEnvelope g) :
    UniversalSuccessorDataNeighborhood canonicalFamily g := by
  apply universalSuccessorDataNeighborhood_of_localSourceFamilyCover
    canonicalFamily
  intro x₀
  rcases exists_chartLocal_genericNormal_canonicalData_of_radiusEnvelope R x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius, hgenericData⟩
  rcases hcontrol x₀ genericRadius hgenericRadius with
    ⟨A, hx₀A, localRadius, hlocalRadius, hcontrols⟩
  let B : LocalFamily g := A.restrictAnchors U hU
  have hx₀B : x₀ ∈ B.anchors := ⟨hx₀A, hx₀U⟩
  have hcontrolsB : B.ControlsGenericNormal localRadius genericRadius := by
    intro x z hzSource hzNorm
    exact hcontrols x z hzSource.1 hzNorm
  have hdataB : LocalUniformNormalSuccessorData B canonicalFamily := by
    apply localUniformNormalSuccessorData_of_controlsGenericNormal
      B canonicalFamily hlocalRadius hcontrolsB
    intro x hx p L z hzSource hzNorm
    exact hgenericData x hx.2 p L z hzSource hzNorm
  exact ⟨B, hx₀B, hdataB⟩

/-- Curvature/minorant specialization of the canonical-only neighborhood. -/
theorem canonicalSuccessorDataNeighborhood_of_curvature_of_controlledLocalFamilyCover_of_jointMinorant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcontrol : GenericNormalControlledLocalFamilyCover g)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤ canonicalNormalAnchorTargetRadius hcurv x p) :
    UniversalSuccessorDataNeighborhood canonicalFamily g := by
  exact
    canonicalSuccessorDataNeighborhood_of_controlledLocalFamilyCover_of_radiusEnvelope
      hcontrol
      (canonicalRadiusEnvelope_of_jointMinorant hcurv pairRadius
        hpositive hlower hminorant)

/-! ## The exact canonical-to-compared continuation boundary -/

/-- The locus on which existence of canonical supplied-family data can be
lifted to existence of a canonical step retaining a legacy generic successor
comparison.

The implication is deliberate: away from the canonical data locus no
comparison is requested.  Thus this is strictly narrower than asking for a
generic/canonical chart-agreement neighborhood independently of actual
successor data. -/
def CanonicalComparedContinuationLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Set ((M × RoundSphere3) × M) :=
  {q | q ∈ UniversalSuccessorDataLocus canonicalFamily g →
    q ∈ UniversalComparedSuccessorLocus g}

/-- Exact diagonal continuation contract for the conditional canonical lift. -/
def CanonicalComparedDiagonalContinuation
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  CanonicalComparedContinuationLocus g ∈
    nhdsSet (successorParameterDiagonal (M := M))

/-- Canonical data and conditional comparison continuation together give the
legacy compared-successor neighborhood used by the direct recognition
consumer. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_continuation
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcanonical : UniversalSuccessorDataNeighborhood canonicalFamily g)
    (hcontinuation : CanonicalComparedDiagonalContinuation g) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply Filter.mem_of_superset (inter_mem hcanonical hcontinuation)
  rintro q ⟨hqCanonical, hqContinuation⟩
  exact hqContinuation hqCanonical

/-- Curvature puts the complete parameter diagonal in the compared locus. -/
theorem successorParameterDiagonal_subset_comparedSuccessorLocus_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    successorParameterDiagonal (M := M) ⊆
      UniversalComparedSuccessorLocus g := by
  rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
  intro L
  have hxSource :
      x ∈ ((CartanSourceExponential.genericFamily g).normal x).source :=
    (CartanSourceExponential.genericFamily g).anchor_mem_source x
  have hxNorm :
      ‖(CartanSourceExponential.genericFamily g).normal x x‖ <
        canonicalTransferredAnchorTargetRadius hcurv x p := by
    rw [(CartanSourceExponential.genericFamily g).normal_anchor x, norm_zero]
    exact canonicalTransferredAnchorTargetRadius_pos hcurv x p
  rcases
      nonempty_transferredPackage_of_normal_lt_selectedRadius
        hcurv x p L x hxSource hxNorm with
    ⟨package⟩
  exact ⟨package.toCanonicalComparedStep⟩

/-- Hence the conditional canonical-comparison locus also contains the
diagonal. -/
theorem successorParameterDiagonal_subset_canonicalComparedContinuationLocus_of_curvature
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    successorParameterDiagonal (M := M) ⊆
      CanonicalComparedContinuationLocus g := by
  intro q hq _hcanonical
  exact
    successorParameterDiagonal_subset_comparedSuccessorLocus_of_curvature
      hcurv hq

/-- Openness of the conditional lift locus supplies its exact diagonal
continuation contract. -/
theorem canonicalComparedDiagonalContinuation_of_isOpen
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hopen : IsOpen (CanonicalComparedContinuationLocus g)) :
    CanonicalComparedDiagonalContinuation g := by
  exact hopen.mem_nhdsSet.mpr
    (successorParameterDiagonal_subset_canonicalComparedContinuationLocus_of_curvature
      hcurv)

/-- Canonical neighborhood plus openness of only the conditional comparison
locus gives the compared neighborhood.  No joint target-chart agreement
premise remains. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_isOpen_continuation
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hcanonical : UniversalSuccessorDataNeighborhood canonicalFamily g)
    (hopen : IsOpen (CanonicalComparedContinuationLocus g)) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  exact
    comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_continuation
      hcanonical
      (canonicalComparedDiagonalContinuation_of_isOpen hcurv hopen)

/-! ## Direct recognition specializations -/

/-- The direct-uniform recognition consumer can take canonical successor-data
stability plus only the conditional comparison continuation boundary. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalNeighborhood_of_continuation_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (canonicalStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood canonicalFamily g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityNeighborhood
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    CartanCanonicalRootedDirectUniformSuccessorMeshRecognition.unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_jointEqualityNeighborhood
  · intro g hcurv
    exact
      comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_continuation
        (canonicalStability g hcurv) (comparisonContinuation g hcurv)
  · exact equalityStability

/-- Envelope form of the canonical-only recognition route.  The target-side
successor radii are canonical from the start; the only legacy conversion
input is the conditional comparison continuation. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRadiusEnvelope_of_controlledLocalFamilyCover_of_continuation_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (hcontrol : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      GenericNormalControlledLocalFamilyCover g)
    (radiusEnvelope : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        LocallyUniformCanonicalRadiusEnvelope g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityNeighborhood
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalNeighborhood_of_continuation_jointEqualityNeighborhood
  · intro g hcurv
    exact
      canonicalSuccessorDataNeighborhood_of_controlledLocalFamilyCover_of_radiusEnvelope
        (hcontrol g) (radiusEnvelope g hcurv)
  · exact comparisonContinuation
  · exact equalityStability

/-- Uniform actual-successor equality is the direct consumer form of the
equality input.  Thus the canonical continuation route plugs into selected
packages without first exposing a four-variable equality neighborhood. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalNeighborhood_of_continuation_uniformActualSuccessorEquality
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (canonicalStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood canonicalFamily g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorEqualityStabilityReduction.UniformActualSuccessorEquality
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    DifferentialSuccessorEqualityStabilityReduction.unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_uniformActualSuccessorEquality
  · intro g hcurv
    exact
      comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_continuation
        (canonicalStability g hcurv) (comparisonContinuation g hcurv)
  · exact equalityStability

/-- Envelope specialization of the uniform actual-successor equality route. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRadiusEnvelope_of_controlledLocalFamilyCover_of_continuation_uniformActualSuccessorEquality
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (hcontrol : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      GenericNormalControlledLocalFamilyCover g)
    (radiusEnvelope : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        LocallyUniformCanonicalRadiusEnvelope g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorEqualityStabilityReduction.UniformActualSuccessorEquality
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalNeighborhood_of_continuation_uniformActualSuccessorEquality
  · intro g hcurv
    exact
      canonicalSuccessorDataNeighborhood_of_controlledLocalFamilyCover_of_radiusEnvelope
        (hcontrol g) (radiusEnvelope g hcurv)
  · exact comparisonContinuation
  · exact equalityStability

/-- The current locally persistent actual-successor equality-radius boundary
also feeds the canonical continuation route through its proved uniformization
theorem. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRadiusEnvelope_of_controlledLocalFamilyCover_of_continuation_localPersistentActualSuccessorEqualityRadius
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (hcontrol : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      GenericNormalControlledLocalFamilyCover g)
    (radiusEnvelope : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        LocallyUniformCanonicalRadiusEnvelope g)
    (comparisonContinuation : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalComparedDiagonalContinuation g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalRadiusEnvelope_of_controlledLocalFamilyCover_of_continuation_uniformActualSuccessorEquality
      hcontrol radiusEnvelope comparisonContinuation
  intro g hcurv
  exact
    DifferentialSuccessorEqualityStabilityReduction.uniformActualSuccessorEquality_of_localPersistence
      g (equalityStability g hcurv)

end Compact

end CartanCanonicalFamilyComparedCanonicalContinuation
end Poincare
