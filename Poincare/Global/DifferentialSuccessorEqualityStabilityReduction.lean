import Poincare.Global.CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.DifferentialSuccessorFiniteAnchorRadius

/-!
# The exact stability boundary for differential-successor equality

The four-variable `UniversalSuccessorEqualityNeighborhood` can look stronger
than the uniform equality ball consumed by the rooted mesh construction.  On
a compact closed manifold the two formulations are equivalent.  The reverse
implication does not use compactness: two open distance inequalities already
give a neighborhood of the predecessor/successor/evaluation diagonal.

Constant curvature does prove the corresponding fixed-anchor, actual-data
statement.  There is one input radius, uniform over tangent alignments and
successor data, and each actual successor has an equality neighborhood at its
new anchor.  The output neighborhood is selected after the datum.  Thus the
remaining gap to the joint neighborhood is precisely uniform persistence of
those output neighborhoods as the anchors and actual successor vary; neither
interval naturality nor a finite-anchor minimum silently supplies it.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorEqualityStabilityReduction

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
open CartanTargetExponential
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorJointEqualityNeighborhood
open DifferentialUniformSuccessorMesh

/-- The direct uniform equality-ball statement used by the mesh consumer.

Unlike `UniversalSuccessorEqualityNeighborhood`, this formulation does not
quantify over a four-variable ambient locus. -/
def UniformActualSuccessorEquality
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ eta > (0 : ℝ), UniformSuccessorEqOnBall g eta

/-- A uniform equality ball gives a neighborhood of the full joint diagonal.

The open set used in the proof only asks that the successor anchor be within
`eta` of the predecessor anchor and that the evaluation point be within
`eta` of the successor anchor. -/
theorem universalSuccessorEqualityNeighborhood_of_uniformSuccessorEqOnBall
    (g : ClosedSmoothRiemannianMetric 3 M)
    {eta : ℝ} (heta : 0 < eta)
    (huniform : UniformSuccessorEqOnBall g eta) :
    UniversalSuccessorEqualityNeighborhood g := by
  letI : MetricSpace M := g.toMetricSpace
  change ∀ (s : CartanChain.ChainState g) {z : M}
      (d : DifferentialInducedSuccessor.Data s z),
      dist z s.anchor < eta →
        EqOn s.germ d.successor.germ (Metric.ball z eta) at huniform
  let W : Set (JointSuccessorEqualityParameter3 M) :=
    {q | dist q.1.2 q.1.1.1 < eta} ∩
      {q | dist q.2 q.1.2 < eta}
  have hfirstContinuous : Continuous
      (fun q : JointSuccessorEqualityParameter3 M ↦
        dist q.1.2 q.1.1.1) := by
    exact
      (continuous_snd.comp continuous_fst).dist
        (continuous_fst.comp (continuous_fst.comp continuous_fst))
  have hsecondContinuous : Continuous
      (fun q : JointSuccessorEqualityParameter3 M ↦
        dist q.2 q.1.2) := by
    exact continuous_snd.dist (continuous_snd.comp continuous_fst)
  have hWopen : IsOpen W := by
    exact
      (isOpen_lt hfirstContinuous continuous_const).inter
        (isOpen_lt hsecondContinuous continuous_const)
  have hdiag : successorEqualityParameterDiagonal (M := M) ⊆ W := by
    rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
    exact ⟨by simpa using heta, by simpa using heta⟩
  have hWsubset : W ⊆ UniversalSuccessorEqualityLocus g := by
    rintro q ⟨hzx, hqz⟩ L d
    have hEq := huniform
      (CartanChain.ChainState.mk q.1.1.1 q.1.1.2 L) d hzx
    apply hEq
    simpa [Metric.mem_ball] using hqz
  exact Filter.mem_of_superset (hWopen.mem_nhdsSet.mpr hdiag) hWsubset

/-- On compact closed manifolds the joint-diagonal neighborhood is exactly
the existence of the state-uniform equality ball used downstream. -/
theorem universalSuccessorEqualityNeighborhood_iff_uniformActualSuccessorEquality
    (g : ClosedSmoothRiemannianMetric 3 M) :
    UniversalSuccessorEqualityNeighborhood g ↔
      UniformActualSuccessorEquality g := by
  constructor
  · intro h
    exact exists_uniformSuccessorEqOnBall_of_jointNeighborhood g h
  · rintro ⟨eta, heta, huniform⟩
    exact
      universalSuccessorEqualityNeighborhood_of_uniformSuccessorEqOnBall
        g heta huniform

/-- The strongest fixed-anchor consequence currently obtained directly from
constant-curvature interval naturality.

The predecessor/successor input radius is uniform over all tangent alignments
and actual data.  The evaluation neighborhood is only required to be a
neighborhood of the actual successor anchor and may depend on that datum. -/
def FixedAnchorActualSuccessorEqualityNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (p : RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ epsilon > (0 : ℝ),
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk x p L) z),
      dist z x < epsilon →
        {q : M |
          (CartanChain.ChainState.mk x p L).germ q =
            d.successor.germ q} ∈ 𝓝 z

/-- Constant curvature proves fixed-anchor actual-successor equality
neighborhoods, with no continuation or path-independence premise. -/
theorem fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    FixedAnchorActualSuccessorEqualityNeighborhood g x p := by
  letI : MetricSpace M := g.toMetricSpace
  let anchor : Unit → M := fun _ ↦ x
  let target : Unit → RoundSphere3 := fun _ ↦ p
  rcases
      DifferentialSuccessorFiniteAnchorRadius.exists_uniform_distance_radius_with_datum_eqOn_ball_on_finite_family
        g hcurv anchor target with
    ⟨epsilon, hepsilon, hlocal⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z d hdist
  rcases hlocal () L d (by simpa [anchor] using hdist) with
    ⟨r, hr, hEq⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
  intro q hq
  simpa [anchor, target] using hEq hq

/-- The pointwise radius statement that can be extracted from a fixed-anchor
actual-successor equality neighborhood.

There is one predecessor/successor input radius, but the equality-ball radius
is selected after the alignment, successor anchor, and actual successor datum.
This dependent order is exactly what constant curvature currently proves. -/
def PointwiseActualSuccessorEqualityRadius
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (p : RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ epsilon > (0 : ℝ),
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk x p L) z),
      dist z x < epsilon →
        ∃ radius > (0 : ℝ),
          EqOn
            (CartanChain.ChainState.mk x p L).germ
            d.successor.germ (Metric.ball z radius)

/-- A neighborhood of equality at each actual successor anchor contains an
actual metric equality ball. -/
theorem pointwiseActualSuccessorEqualityRadius_of_fixedAnchorNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (p : RoundSphere3)
    (hlocal : FixedAnchorActualSuccessorEqualityNeighborhood g x p) :
    PointwiseActualSuccessorEqualityRadius g x p := by
  letI : MetricSpace M := g.toMetricSpace
  rcases hlocal with ⟨epsilon, hepsilon, hactual⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z d hzx
  rcases Metric.mem_nhds_iff.mp (hactual L z d hzx) with
    ⟨radius, hradius, hball⟩
  refine ⟨radius, hradius, ?_⟩
  intro q hq
  exact hball hq

/-- Constant curvature discharges positivity at every fixed source-target
pair and every actual successor, with the equality radius still selected
after the datum. -/
theorem pointwiseActualSuccessorEqualityRadius_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    PointwiseActualSuccessorEqualityRadius g x p := by
  exact
    pointwiseActualSuccessorEqualityRadius_of_fixedAnchorNeighborhood
      g x p
      (fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature
        g hcurv x p)

/-- A common actual-successor equality radius at one source-target pair.

The same radius controls both movement of the successor anchor and the
equality ball around it, uniformly over every dependent tangent alignment and
every actual differential-successor datum.  Keeping those dependent objects
under universal quantifiers avoids inventing a topology on the space of
moving alignments or successor data. -/
def ActualSuccessorEqualityRadiusAdmissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) (radius : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : DifferentialInducedSuccessor.Data
      (CartanChain.ChainState.mk x p L) z),
    dist z x < radius →
      EqOn
        (CartanChain.ChainState.mk x p L).germ
        d.successor.germ (Metric.ball z radius)

/-- Actual-successor equality-radius admissibility is downward closed. -/
theorem ActualSuccessorEqualityRadiusAdmissible.mono
    {g : ClosedSmoothRiemannianMetric 3 M}
    {x : M} {p : RoundSphere3} {large small : ℝ}
    (hlarge : ActualSuccessorEqualityRadiusAdmissible g x p large)
    (hsmall : small ≤ large) :
    ActualSuccessorEqualityRadiusAdmissible g x p small := by
  letI : MetricSpace M := g.toMetricSpace
  intro L z d hzx q hq
  apply hlarge L z d (hzx.trans_le hsmall)
  rw [Metric.mem_ball] at hq ⊢
  exact hq.trans_le hsmall

/-- One equality radius is locally persistent at `(x,p)` when it remains
admissible at every source-target pair in some neighborhood of `(x,p)`. -/
def LocallyPersistentActualSuccessorEqualityRadiusAt
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) (radius : ℝ) : Prop :=
  ∀ᶠ yq in 𝓝 xp,
    ActualSuccessorEqualityRadiusAdmissible
      g yq.1 yq.2 radius

/-- The local geometric regularity boundary on the full compact
source-target parameter space.

All successor anchors, evaluation points, dependent alignments, and actual
successor data remain universally quantified inside admissibility.  The new
content is that at every `(x,p)` one positive common radius persists under
movement of `(x,p)`.  Pointwise positivity above does not imply this. -/
def ActualSuccessorEqualityRadiusLocalPersistence
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ xp : M × RoundSphere3,
    ∃ radius > (0 : ℝ),
      LocallyPersistentActualSuccessorEqualityRadiusAt g xp radius

/-- Positive capped radii which persist locally at one source-target pair. -/
def locallyPersistentActualSuccessorEqualityRadiusCandidates
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) : Set ℝ :=
  {radius : ℝ |
    0 < radius ∧ radius ≤ 1 ∧
      LocallyPersistentActualSuccessorEqualityRadiusAt g xp radius}

/-- The canonical locally persistent actual-successor equality radius.

The cap makes the supremum bounded, insertion of zero makes it total, and
halving keeps the selected radius strictly below a genuine candidate whenever
local persistence supplies one. -/
def canonicalLocallyPersistentActualSuccessorEqualityRadius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) : ℝ :=
  sSup
      (insert (0 : ℝ)
        (locallyPersistentActualSuccessorEqualityRadiusCandidates
          g (x, p))) /
    2

private theorem locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
    (g : ClosedSmoothRiemannianMetric 3 M)
    (xp : M × RoundSphere3) :
    BddAbove
      (insert (0 : ℝ)
        (locallyPersistentActualSuccessorEqualityRadiusCandidates g xp)) := by
  refine ⟨1, ?_⟩
  intro radius hradius
  rcases Set.mem_insert_iff.mp hradius with hradius | hradius
  · subst radius
    exact zero_le_one
  · exact hradius.2.1

/-- The canonical locally persistent radius is always nonnegative. -/
theorem canonicalLocallyPersistentActualSuccessorEqualityRadius_nonneg
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x : M) (p : RoundSphere3) :
    0 ≤ canonicalLocallyPersistentActualSuccessorEqualityRadius g x p := by
  have hzero : (0 : ℝ) ≤
      sSup
        (insert (0 : ℝ)
          (locallyPersistentActualSuccessorEqualityRadiusCandidates
            g (x, p))) :=
    le_csSup
      (locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
        g (x, p))
      (Set.mem_insert (0 : ℝ) _)
  exact div_nonneg hzero (by norm_num)

/-- Local persistence is converted into lower semicontinuity by the canonical
supremum envelope.  For each fixed candidate radius, its persistence locus is
open by construction. -/
theorem canonicalLocallyPersistentActualSuccessorEqualityRadius_lowerSemicontinuous
    (g : ClosedSmoothRiemannianMetric 3 M) :
    LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦
        canonicalLocallyPersistentActualSuccessorEqualityRadius
          g xp.1 xp.2) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  by_cases ha : a < 0
  · have hpreimage :
        (fun xp : M × RoundSphere3 ↦
          canonicalLocallyPersistentActualSuccessorEqualityRadius
            g xp.1 xp.2) ⁻¹' Ioi a = Set.univ := by
      ext xp
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact ha.trans_le
        (canonicalLocallyPersistentActualSuccessorEqualityRadius_nonneg
          g xp.1 xp.2)
    rw [hpreimage]
    exact isOpen_univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    rw [isOpen_iff_mem_nhds]
    intro xp hxp
    change a <
      canonicalLocallyPersistentActualSuccessorEqualityRadius
        g xp.1 xp.2 at hxp
    let candidates : Set ℝ :=
      insert (0 : ℝ)
        (locallyPersistentActualSuccessorEqualityRadiusCandidates g xp)
    have hnonempty : candidates.Nonempty := by
      exact ⟨0, by simp [candidates]⟩
    have hbdd : BddAbove candidates := by
      simpa [candidates] using
        locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
          g xp
    have htwice : 2 * a < sSup candidates := by
      dsimp [canonicalLocallyPersistentActualSuccessorEqualityRadius] at hxp
      simpa [candidates] using (show 2 * a <
        sSup
          (insert (0 : ℝ)
            (locallyPersistentActualSuccessorEqualityRadiusCandidates
              g xp)) by
        linarith)
    rcases exists_lt_of_lt_csSup hnonempty htwice with
      ⟨radius, hradius, htwiceRadius⟩
    have hradiusCandidate :
        radius ∈
          locallyPersistentActualSuccessorEqualityRadiusCandidates
            g xp := by
      change radius ∈
        insert (0 : ℝ)
          (locallyPersistentActualSuccessorEqualityRadiusCandidates
            g xp) at hradius
      rcases Set.mem_insert_iff.mp hradius with hradius | hradius
      · subst radius
        have : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha0
        exact (not_lt_of_ge this htwiceRadius).elim
      · exact hradius
    let stableSet : Set (M × RoundSphere3) :=
      {yq | ∀ᶠ wq in 𝓝 yq,
        ActualSuccessorEqualityRadiusAdmissible
          g wq.1 wq.2 radius}
    have hstableOpen : IsOpen stableSet := by
      exact isOpen_setOf_eventually_nhds
    have hxpStable : xp ∈ stableSet := hradiusCandidate.2.2
    refine Filter.mem_of_superset
      (hstableOpen.mem_nhds hxpStable) ?_
    intro yq hyq
    change a <
      canonicalLocallyPersistentActualSuccessorEqualityRadius
        g yq.1 yq.2
    have hradiusCandidateY :
        radius ∈
          locallyPersistentActualSuccessorEqualityRadiusCandidates
            g yq :=
      ⟨hradiusCandidate.1, hradiusCandidate.2.1, hyq⟩
    have hradiusLe : radius ≤
        sSup
          (insert (0 : ℝ)
            (locallyPersistentActualSuccessorEqualityRadiusCandidates
              g yq)) :=
      le_csSup
        (locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
          g yq)
        (Set.mem_insert_of_mem _ hradiusCandidateY)
    dsimp [canonicalLocallyPersistentActualSuccessorEqualityRadius]
    linarith

/-- Local positive-radius persistence makes the canonical envelope positive
at every point of the compact source-target parameter space. -/
theorem canonicalLocallyPersistentActualSuccessorEqualityRadius_pos
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : ActualSuccessorEqualityRadiusLocalPersistence g)
    (x : M) (p : RoundSphere3) :
    0 < canonicalLocallyPersistentActualSuccessorEqualityRadius g x p := by
  rcases hstable (x, p) with ⟨radius, hradius, hlocal⟩
  let capped : ℝ := min radius 1
  have hcapped : 0 < capped := lt_min hradius zero_lt_one
  have hcappedLocal :
      LocallyPersistentActualSuccessorEqualityRadiusAt
        g (x, p) capped := by
    filter_upwards [hlocal] with yq hyq
    exact hyq.mono (min_le_left _ _)
  have hcappedCandidate :
      capped ∈
        locallyPersistentActualSuccessorEqualityRadiusCandidates
          g (x, p) :=
    ⟨hcapped, min_le_right _ _, hcappedLocal⟩
  have hcappedLe : capped ≤
      sSup
        (insert (0 : ℝ)
          (locallyPersistentActualSuccessorEqualityRadiusCandidates
            g (x, p))) :=
    le_csSup
      (locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
        g (x, p))
      (Set.mem_insert_of_mem _ hcappedCandidate)
  dsimp [canonicalLocallyPersistentActualSuccessorEqualityRadius]
  linarith

/-- Under local persistence, the canonical envelope is itself admissible at
each source-target pair. -/
theorem canonicalLocallyPersistentActualSuccessorEqualityRadius_admissible
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : ActualSuccessorEqualityRadiusLocalPersistence g)
    (x : M) (p : RoundSphere3) :
    ActualSuccessorEqualityRadiusAdmissible g x p
      (canonicalLocallyPersistentActualSuccessorEqualityRadius g x p) := by
  let candidates : Set ℝ :=
    insert (0 : ℝ)
      (locallyPersistentActualSuccessorEqualityRadiusCandidates g (x, p))
  have hnonempty : candidates.Nonempty := by
    exact ⟨0, by simp [candidates]⟩
  have hpositive :=
    canonicalLocallyPersistentActualSuccessorEqualityRadius_pos
      hstable x p
  have hbelowSup : sSup candidates / 2 < sSup candidates := by
    have hsupPositive : 0 < sSup candidates := by
      dsimp [canonicalLocallyPersistentActualSuccessorEqualityRadius]
        at hpositive
      simpa [candidates] using (show 0 <
        sSup
          (insert (0 : ℝ)
            (locallyPersistentActualSuccessorEqualityRadiusCandidates
              g (x, p))) by
        linarith)
    linarith
  rcases exists_lt_of_lt_csSup hnonempty hbelowSup with
    ⟨radius, hradius, hbelowRadius⟩
  have hradiusCandidate :
      radius ∈
        locallyPersistentActualSuccessorEqualityRadiusCandidates
          g (x, p) := by
    change radius ∈
      insert (0 : ℝ)
        (locallyPersistentActualSuccessorEqualityRadiusCandidates
          g (x, p)) at hradius
    rcases Set.mem_insert_iff.mp hradius with hradius | hradius
    · subst radius
      have hsupNonneg : 0 ≤ sSup candidates := by
        have hbdd : BddAbove candidates := by
          simpa [candidates] using
            locallyPersistentActualSuccessorEqualityRadiusCandidates_bddAbove
              g (x, p)
        exact le_csSup hbdd (by simp [candidates])
      have : 0 ≤ sSup candidates / 2 :=
        div_nonneg hsupNonneg (by norm_num)
      exact (not_lt_of_ge this hbelowRadius).elim
    · exact hradius
  have hradiusAdmissible :
      ActualSuccessorEqualityRadiusAdmissible g x p radius :=
    hradiusCandidate.2.2.self_of_nhds
  apply hradiusAdmissible.mono
  dsimp [canonicalLocallyPersistentActualSuccessorEqualityRadius]
  simpa [candidates] using le_of_lt hbelowRadius

/-- A positive lower-semicontinuous actual-successor equality-radius
certificate on the compact source-target parameter space. -/
def LowerSemicontinuousActualSuccessorEqualityRadius
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ radius : M × RoundSphere3 → ℝ,
    LowerSemicontinuous radius ∧
      (∀ xp, 0 < radius xp) ∧
      ∀ xp, ActualSuccessorEqualityRadiusAdmissible
        g xp.1 xp.2 (radius xp)

/-- Local persistence canonically produces a positive lower-semicontinuous
actual-successor equality-radius certificate. -/
theorem lowerSemicontinuousActualSuccessorEqualityRadius_of_localPersistence
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hstable : ActualSuccessorEqualityRadiusLocalPersistence g) :
    LowerSemicontinuousActualSuccessorEqualityRadius g := by
  refine ⟨
    (fun xp : M × RoundSphere3 ↦
      canonicalLocallyPersistentActualSuccessorEqualityRadius
        g xp.1 xp.2),
    canonicalLocallyPersistentActualSuccessorEqualityRadius_lowerSemicontinuous
      g,
    ?_, ?_⟩
  · intro xp
    exact
      canonicalLocallyPersistentActualSuccessorEqualityRadius_pos
        hstable xp.1 xp.2
  · intro xp
    exact
      canonicalLocallyPersistentActualSuccessorEqualityRadius_admissible
        hstable xp.1 xp.2

/-- Compactness turns any positive lower-semicontinuous admissible radius on
the full source-target parameter space into one global actual-successor
equality ball. -/
theorem uniformActualSuccessorEquality_of_lowerSemicontinuousRadius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hradius : LowerSemicontinuousActualSuccessorEqualityRadius g) :
    UniformActualSuccessorEquality g := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases hradius with ⟨radius, hlower, hpositive, hadmissible⟩
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
      letI : IsEmpty M := hEmpty
      refine ⟨1, zero_lt_one, ?_⟩
      intro s
      exact isEmptyElim s.anchor
  | inr hNonempty =>
      letI : Nonempty M := hNonempty
      rcases
          hlower.lowerSemicontinuousOn Set.univ |>.exists_isMinOn
            Set.univ_nonempty isCompact_univ with
        ⟨xpmin, _hxpmin, hminimum⟩
      let eta : ℝ := radius xpmin
      refine ⟨eta, hpositive xpmin, ?_⟩
      intro s z d hzx
      cases s with
      | mk x p L =>
          have hetaLe : eta ≤ radius (x, p) :=
            hminimum (Set.mem_univ (x, p))
          exact
            (hadmissible (x, p)).mono hetaLe L z d hzx

/-- The locally persistent geometric radius contract is sufficient for the
uniform actual-successor equality used by the differential mesh. -/
theorem uniformActualSuccessorEquality_of_localPersistence
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hstable : ActualSuccessorEqualityRadiusLocalPersistence g) :
    UniformActualSuccessorEquality g := by
  exact
    uniformActualSuccessorEquality_of_lowerSemicontinuousRadius g
      (lowerSemicontinuousActualSuccessorEqualityRadius_of_localPersistence
        g hstable)

/-- A global uniform equality ball is, conversely, a locally persistent
actual-successor equality radius: the same radius works on every neighborhood
because it works at every source-target pair. -/
theorem actualSuccessorEqualityRadiusLocalPersistence_of_uniform
    (g : ClosedSmoothRiemannianMetric 3 M)
    (huniform : UniformActualSuccessorEquality g) :
    ActualSuccessorEqualityRadiusLocalPersistence g := by
  letI : MetricSpace M := g.toMetricSpace
  rcases huniform with ⟨eta, heta, hEq⟩
  intro xp
  refine ⟨eta, heta, Filter.Eventually.of_forall ?_⟩
  intro yq L z d hzx
  exact
    hEq (CartanChain.ChainState.mk yq.1 yq.2 L) d hzx

/-- On a compact closed manifold the local-persistence interface is exactly
equivalent to the raw uniform equality ball, while exposing the geometric
regularity input pointwise on `M × RoundSphere3`. -/
theorem actualSuccessorEqualityRadiusLocalPersistence_iff_uniform
    (g : ClosedSmoothRiemannianMetric 3 M) :
    ActualSuccessorEqualityRadiusLocalPersistence g ↔
      UniformActualSuccessorEquality g := by
  constructor
  · exact uniformActualSuccessorEquality_of_localPersistence g
  · exact actualSuccessorEqualityRadiusLocalPersistence_of_uniform g

/-- The exact cross-history premise used by controlled adjacent continuation.

It is required only at equality points away from the canonical successor
anchor and only inside the connected component of the coordinate-controlled
common source.  In particular it assumes neither equality on an overlap nor
preconnectedness of the full overlap. -/
def ControlledEqualityPointSuccessorPathIndependence
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (rhoS rhoN : ℝ) : Prop :=
  ∀ q ∈ connectedComponentIn
      (CoordinateControlledCommonSource s d.successor rhoS rhoN) z,
    s.germ q = d.successor.germ q → q ≠ z →
      CrossHistorySuccessorAgreement s d.successor q

/-- Constant curvature and the narrow controlled equality-point
path-independence contract close the whole controlled anchor component and
therefore produce a metric equality ball.

The two radii retain their honest dependent order: the predecessor radius is
chosen before the actual successor, while the successor radius is chosen
after it. -/
theorem exists_metricBall_eqOn_coordinateControlled_of_controlledPathIndependence
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            ControlledEqualityPointSuccessorPathIndependence
                s d rhoS rhoN →
              ∃ r > (0 : ℝ),
                Metric.ball z r ⊆
                    CoordinateControlledCommonSource
                      s d.successor rhoS rhoN ∧
                  EqOn s.germ d.successor.germ (Metric.ball z r) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      DifferentialSuccessorAdjacentContinuation.exists_metricBall_eqOn_coordinateControlled_of_pathIndependence
        g hcurv s with
    ⟨rhoS, hrhoS, hlocal⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hlocal d hd with ⟨rhoN, hrhoN, hlocalN⟩
  exact ⟨rhoN, hrhoN, hlocalN⟩

/-- The direct Cartan recognition theorem can consume the exact uniform-ball
contract, without exposing `UniversalSuccessorEqualityNeighborhood` in a
selected package.  By the equivalence above this is an interface reduction,
not a hidden mathematical strengthening. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_uniformActualSuccessorEquality
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (comparedStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalComparedSuccessorLocus g ∈
          nhdsSet (successorParameterDiagonal (M := M)))
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniformActualSuccessorEquality g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_jointEqualityNeighborhood
      comparedStability
  intro g hcurv
  rcases equalityStability g hcurv with ⟨eta, heta, huniform⟩
  exact
    universalSuccessorEqualityNeighborhood_of_uniformSuccessorEqOnBall
      g heta huniform

/-- The direct recognition theorem with the raw uniform equality-ball field
replaced by the locally persistent actual-successor equality-radius field. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_localPersistentActualSuccessorEqualityRadius
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (comparedStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalComparedSuccessorLocus g ∈
          nhdsSet (successorParameterDiagonal (M := M)))
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        ActualSuccessorEqualityRadiusLocalPersistence g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_uniformActualSuccessorEquality
      comparedStability
  intro g hcurv
  exact
    uniformActualSuccessorEquality_of_localPersistence g
      (equalityStability g hcurv)

end DifferentialSuccessorEqualityStabilityReduction
end Poincare
