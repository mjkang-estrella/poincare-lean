import Poincare.Global.CartanCanonicalRootedEndpointAssembly

/-!
# Restricted canonical rooted endpoint gluing

This module combines canonical rooted realization with the restricted Cartan
gluing consumer.  Pairwise adaptive closeness is required only on selected
open anchor neighborhoods.  A second interface replaces terminal
second-closeness by an accumulated scalar mesh bound and shrinks every right
anchor domain into the uniform terminal-distance ball constructed upstream.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanCanonicalRootedEndpointAssembly
namespace CanonicalRootedRealizationPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedReachableEndpointTransport
open CartanAtlasRootedAdaptiveClosenessTransport
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}

/--
Adaptive rooted overlap coherence on selected open anchor neighborhoods.

Unlike full `AdaptiveOverlapCoherence`, schedules and both dependent
closeness stages are requested only when the overlap point lies in the chosen
domain intersection.  The domains still contain their anchors and lie inside
the corresponding full endpoint-germ sources.
-/
structure RestrictedAdaptiveOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1) where
  domain : M → Set M
  isOpen_domain : ∀ x : M, IsOpen (domain x)
  anchor_mem_domain : ∀ x : M, x ∈ domain x
  domain_subset_source : ∀ x : M,
    domain x ⊆ (package.endpoint.terminalState x).germ.source
  schedule : ∀ x y z : M,
    z ∈ domain x ∩ domain y →
      RootedOverlapStrictFactorSchedule package.endpoint x y z
  firstClose : ∀ x y z : M,
    ∀ hz : z ∈ domain x ∩ domain y,
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        (schedule x y z hz) hcurv
  secondClose : ∀ x y z : M,
    ∀ hz : z ∈ domain x ∩ domain y,
      RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
        (schedule x y z hz) hcurv (firstClose x y z hz)

/-- Restricted adaptive coherence constructs exactly the restricted compatible
Cartan atlas consumed by diagonal gluing. -/
def RestrictedAdaptiveOverlapCoherence.toRestrictedCompatibleCartanAtlasData3
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (coherence : RestrictedAdaptiveOverlapCoherence package hcurv) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := package.endpoint.target
  alignment := package.endpoint.alignment
  domain := coherence.domain
  isOpen_domain := coherence.isOpen_domain
  anchor_mem_domain := coherence.anchor_mem_domain
  domain_subset_source := by
    intro x z hz
    have hterminal :
        z ∈ (package.endpoint.terminalState x).germ.source :=
      coherence.domain_subset_source x hz
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    let schedule := coherence.schedule x y z hz
    let hfirst := coherence.firstClose x y z hz
    have htransport :=
      RootedOverlapStrictFactorSchedule.toCommonRootTerminalTransport_of_adaptiveCloseness
        schedule hcurv hfirst (coherence.secondClose x y z hz)
    have hvalue :=
      CartanAtlasRealizedEndpointTransport.germ_value_eq_of_commonRootTerminalTransport
        (package.endpoint.terminalState x)
        (package.endpoint.terminalState y) z htransport
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ z =
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/--
The distance-shrunk sufficient interface.

It retains explicit schedules, first closeness, and the finite accumulated
scalar mesh inequalities.  There is no terminal normal, path, distance, or
second-closeness field: every chosen domain lies in the uniform terminal ball
at its own anchor, so those conclusions are derived.
-/
structure RestrictedAccumulatedMeshOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh) where
  domain : M → Set M
  isOpen_domain : ∀ x : M, IsOpen (domain x)
  anchor_mem_domain : ∀ x : M, x ∈ domain x
  domain_subset_source : ∀ x : M,
    domain x ⊆ (package.endpoint.terminalState x).germ.source
  domain_subset_terminalBall :
    letI : MetricSpace M := g.toMetricSpace
    ∀ y : M,
      domain y ⊆ Metric.ball y (terminalDistanceRadius g y hmesh)
  schedule : ∀ x y z : M,
    z ∈ domain x ∩ domain y →
      RootedOverlapStrictFactorSchedule package.endpoint x y z
  firstClose : ∀ x y z : M,
    ∀ hz : z ∈ domain x ∩ domain y,
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        (schedule x y z hz) hcurv
  accumulatedScalar :
    letI : MetricSpace M := g.toMetricSpace
    ∀ x y z : M,
      ∀ hz : z ∈ domain x ∩ domain y,
        ∀ n : Fin (schedule x y z hz).length,
          ∀ i : Fin
            (factorGapNodes (schedule x y z hz).refined
              (schedule x y z hz).factor n).length,
            ((((schedule x y z hz).factor (n + 1) -
                ((schedule x y z hz).factor n + i + 1) : ℕ) : ℝ) *
                mesh) <
              RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
                (schedule x y z hz) hcurv (firstClose x y z hz) n i

/--
The minimal accumulated-mesh payload on the canonical shrunken domains.

All domain topology, anchor membership, full-source inclusion, and terminal
ball inclusion are now automatic from `terminalRestrictedDomain`; only the
actual finite overlap data remain as fields.
-/
structure TerminalRestrictedAccumulatedMeshOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh) where
  schedule : ∀ x y z : M,
    z ∈ package.terminalRestrictedDomain hmesh x ∩
        package.terminalRestrictedDomain hmesh y →
      RootedOverlapStrictFactorSchedule package.endpoint x y z
  firstClose : ∀ x y z : M,
    ∀ hz : z ∈ package.terminalRestrictedDomain hmesh x ∩
        package.terminalRestrictedDomain hmesh y,
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        (schedule x y z hz) hcurv
  accumulatedScalar :
    letI : MetricSpace M := g.toMetricSpace
    ∀ x y z : M,
      ∀ hz : z ∈ package.terminalRestrictedDomain hmesh x ∩
          package.terminalRestrictedDomain hmesh y,
        ∀ n : Fin (schedule x y z hz).length,
          ∀ i : Fin
            (factorGapNodes (schedule x y z hz).refined
              (schedule x y z hz).factor n).length,
            ((((schedule x y z hz).factor (n + 1) -
                ((schedule x y z hz).factor n + i + 1) : ℕ) : ℝ) *
                mesh) <
              RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
                (schedule x y z hz) hcurv (firstClose x y z hz) n i

/-- The finitely many first-stage radii of one fixed realized schedule have a
common positive lower bound.  The empty insertion-index case is handled by
the arbitrary positive bound `1`. -/
theorem exists_common_adaptiveFirstRadius
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          epsilon ≤
            RootedOverlapStrictFactorSchedule.adaptiveFirstRadius
              schedule hcurv n i := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let A := Σ n : Fin schedule.length,
    Fin (factorGapNodes schedule.refined schedule.factor n).length
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      refine ⟨1, zero_lt_one, ?_⟩
      intro n i
      exact isEmptyElim (α := A) (⟨n, i⟩ : A)
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      let epsilon : ℝ :=
        Finset.univ.inf' Finset.univ_nonempty
          (fun a : A ↦
            RootedOverlapStrictFactorSchedule.adaptiveFirstRadius
              schedule hcurv a.1 a.2)
      have hepsilon : 0 < epsilon := by
        dsimp [epsilon]
        apply (Finset.lt_inf'_iff _).2
        intro a _ha
        exact
          RootedOverlapStrictFactorSchedule.adaptiveFirstRadius_pos
            schedule hcurv a.1 a.2
      refine ⟨epsilon, hepsilon, ?_⟩
      intro n i
      exact
        Finset.inf'_le
          (fun a : A ↦
            RootedOverlapStrictFactorSchedule.adaptiveFirstRadius
              schedule hcurv a.1 a.2)
          (Finset.mem_univ (⟨n, i⟩ : A))

/-- The selected common first-stage cutoff for one fixed schedule. -/
def commonAdaptiveFirstRadius
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose (exists_common_adaptiveFirstRadius schedule hcurv)

/-- The selected common first-stage cutoff is positive. -/
theorem commonAdaptiveFirstRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < commonAdaptiveFirstRadius schedule hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_common_adaptiveFirstRadius schedule hcurv)).1

/-- The selected common first-stage cutoff lies below every dependent first
radius of the schedule. -/
theorem commonAdaptiveFirstRadius_le
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
        commonAdaptiveFirstRadius schedule hcurv ≤
          RootedOverlapStrictFactorSchedule.adaptiveFirstRadius
            schedule hcurv n i := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_common_adaptiveFirstRadius schedule hcurv)).2

/-- After first-stage closeness has been fixed, the finitely many second
radii have one positive mesh cutoff.  Multiplying this cutoff by any
remaining factor-gap edge count is still strictly below the corresponding
dependent second radius. -/
theorem exists_common_accumulatedSecondMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ delta > (0 : ℝ),
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          ((schedule.factor (n + 1) -
              (schedule.factor n + i + 1) : ℕ) : ℝ) * delta <
            RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
              schedule hcurv hfirst n i := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let A := Σ n : Fin schedule.length,
    Fin (factorGapNodes schedule.refined schedule.factor n).length
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      refine ⟨1, zero_lt_one, ?_⟩
      intro n i
      exact isEmptyElim (α := A) (⟨n, i⟩ : A)
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      let countAt : A → ℝ := fun a ↦
        ((schedule.factor (a.1 + 1) -
          (schedule.factor a.1 + a.2 + 1) : ℕ) : ℝ)
      let cutoffAt : A → ℝ := fun a ↦
        RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
            schedule hcurv hfirst a.1 a.2 /
          (countAt a + 1)
      have hcutoffAt : ∀ a : A, 0 < cutoffAt a := by
        intro a
        apply div_pos
        · exact
            RootedOverlapStrictFactorSchedule.adaptiveSecondRadius_pos
              schedule hcurv hfirst a.1 a.2
        · positivity
      let delta : ℝ :=
        Finset.univ.inf' Finset.univ_nonempty cutoffAt
      have hdelta : 0 < delta := by
        dsimp [delta]
        apply (Finset.lt_inf'_iff _).2
        intro a _ha
        exact hcutoffAt a
      refine ⟨delta, hdelta, ?_⟩
      intro n i
      let a : A := ⟨n, i⟩
      let count : ℝ :=
        ((schedule.factor (n + 1) -
          (schedule.factor n + i + 1) : ℕ) : ℝ)
      have hcount : 0 ≤ count := by positivity
      have hden : 0 < count + 1 := by positivity
      have hdeltaLe : delta ≤ cutoffAt a := by
        dsimp only [delta]
        exact Finset.inf'_le cutoffAt (Finset.mem_univ a)
      have hcutoffPos : 0 < cutoffAt a := hcutoffAt a
      change count * delta <
        RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
          schedule hcurv hfirst n i
      calc
        count * delta ≤ count * cutoffAt a :=
          mul_le_mul_of_nonneg_left hdeltaLe hcount
        _ < (count + 1) * cutoffAt a :=
          mul_lt_mul_of_pos_right (by linarith) hcutoffPos
        _ = RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
              schedule hcurv hfirst n i := by
          dsimp only [cutoffAt, countAt, a, count]
          field_simp

/-- The selected accumulated second-stage mesh cutoff for one fixed schedule
and one fixed proof of first-stage closeness. -/
def commonAccumulatedSecondMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose
    (exists_common_accumulatedSecondMeshRadius schedule hcurv hfirst)

/-- The selected accumulated second-stage mesh cutoff is positive. -/
theorem commonAccumulatedSecondMeshRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) :
    0 < commonAccumulatedSecondMeshRadius schedule hcurv hfirst := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_common_accumulatedSecondMeshRadius
        schedule hcurv hfirst)).1

/-- The selected second-stage cutoff satisfies every weighted accumulated
mesh inequality of its fixed schedule. -/
theorem commonAccumulatedSecondMeshRadius_weighted_lt
    [CompactSpace M] [ConnectedSpace M]
    {endpoint : RootedPathContinuedEndpointFamily g} {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst :
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        schedule hcurv) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
        ((schedule.factor (n + 1) -
            (schedule.factor n + i + 1) : ℕ) : ℝ) *
            commonAccumulatedSecondMeshRadius schedule hcurv hfirst <
          RootedOverlapStrictFactorSchedule.adaptiveSecondRadius
            schedule hcurv hfirst n i := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (exists_common_accumulatedSecondMeshRadius
        schedule hcurv hfirst)).2

/-- A prescribed mesh below the selected fixed-schedule first cutoff supplies
the complete first-stage closeness proof. -/
def adaptiveFirstCloseness_of_mesh_lt_commonAdaptiveFirstRadius
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ}
    (certificate : PrescribedMeshCertificate package.realization mesh)
    {x y z : M}
    (schedule : RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hsmall :
      letI : MetricSpace M := g.toMetricSpace
      mesh < commonAdaptiveFirstRadius schedule hcurv) :
    RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
      schedule hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  apply package.adaptiveFirstCloseness_of_mesh_le_adaptiveFirstRadius
    certificate schedule hcurv
  intro n i
  exact (le_of_lt hsmall).trans
    (commonAdaptiveFirstRadius_le schedule hcurv n i)

/-- A supplied family of terminal-domain schedules gives the complete minimal
coherence package whenever the already-chosen package mesh lies below the
schedule-dependent first cutoff and, after first closeness is fixed, below
the schedule-dependent accumulated second cutoff.

This constructor deliberately preserves the adaptive quantifier order; it
does not assert a mesh uniform over schedules or construct the schedules. -/
def terminalRestrictedAccumulatedMeshOverlapCoherence_of_schedule_of_mesh_lt_cutoffs
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh)
    (schedule : ∀ x y z : M,
      z ∈ package.terminalRestrictedDomain hmesh x ∩
          package.terminalRestrictedDomain hmesh y →
        RootedOverlapStrictFactorSchedule package.endpoint x y z)
    (hfirstSmall :
      letI : MetricSpace M := g.toMetricSpace
      ∀ x y z : M,
        ∀ hz : z ∈ package.terminalRestrictedDomain hmesh x ∩
            package.terminalRestrictedDomain hmesh y,
          mesh < commonAdaptiveFirstRadius (schedule x y z hz) hcurv)
    (hsecondSmall :
      letI : MetricSpace M := g.toMetricSpace
      ∀ x y z : M,
        ∀ hz : z ∈ package.terminalRestrictedDomain hmesh x ∩
            package.terminalRestrictedDomain hmesh y,
          ∀ hfirst :
              RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
                (schedule x y z hz) hcurv,
            mesh ≤ commonAccumulatedSecondMeshRadius
              (schedule x y z hz) hcurv hfirst) :
    TerminalRestrictedAccumulatedMeshOverlapCoherence
      package hcurv hmesh certificate := by
  letI : MetricSpace M := g.toMetricSpace
  let firstClose : ∀ x y z : M,
      ∀ hz : z ∈ package.terminalRestrictedDomain hmesh x ∩
          package.terminalRestrictedDomain hmesh y,
        RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
          (schedule x y z hz) hcurv := fun x y z hz ↦
    package.adaptiveFirstCloseness_of_mesh_lt_commonAdaptiveFirstRadius
      certificate (schedule x y z hz) hcurv (hfirstSmall x y z hz)
  exact
    { schedule := schedule
      firstClose := firstClose
      accumulatedScalar := by
        intro x y z hz n i
        let count : ℝ :=
          (((schedule x y z hz).factor (n + 1) -
            ((schedule x y z hz).factor n + i + 1) : ℕ) : ℝ)
        have hcount : 0 ≤ count := by positivity
        have hscaled : count * mesh ≤
            count * commonAccumulatedSecondMeshRadius
              (schedule x y z hz) hcurv (firstClose x y z hz) :=
          mul_le_mul_of_nonneg_left
            (hsecondSmall x y z hz (firstClose x y z hz)) hcount
        exact hscaled.trans_lt
          (commonAccumulatedSecondMeshRadius_weighted_lt
            (schedule x y z hz) hcurv (firstClose x y z hz) n i) }

/-- The canonical terminal-domain interface supplies the more general
distance-shrunk interface without any additional hypotheses. -/
def TerminalRestrictedAccumulatedMeshOverlapCoherence.toRestrictedAccumulatedMeshOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh)
    (coherence :
      TerminalRestrictedAccumulatedMeshOverlapCoherence
        package hcurv hmesh certificate) :
    RestrictedAccumulatedMeshOverlapCoherence
      package hcurv hmesh certificate where
  domain := package.terminalRestrictedDomain hmesh
  isOpen_domain := package.isOpen_terminalRestrictedDomain hmesh
  anchor_mem_domain := package.anchor_mem_terminalRestrictedDomain hmesh
  domain_subset_source := package.terminalRestrictedDomain_subset_source hmesh
  domain_subset_terminalBall := by
    letI : MetricSpace M := g.toMetricSpace
    intro y z hz
    exact hz.2
  schedule := coherence.schedule
  firstClose := coherence.firstClose
  accumulatedScalar := coherence.accumulatedScalar

/-- Distance shrinking and the accumulated scalar bounds derive the complete
restricted adaptive coherence, including every second-closeness field. -/
def RestrictedAccumulatedMeshOverlapCoherence.toRestrictedAdaptiveOverlapCoherence
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (certificate : PrescribedMeshCertificate package.realization mesh)
    (coherence :
      RestrictedAccumulatedMeshOverlapCoherence
        package hcurv hmesh certificate) :
    RestrictedAdaptiveOverlapCoherence package hcurv where
  domain := coherence.domain
  isOpen_domain := coherence.isOpen_domain
  anchor_mem_domain := coherence.anchor_mem_domain
  domain_subset_source := coherence.domain_subset_source
  schedule := coherence.schedule
  firstClose := coherence.firstClose
  secondClose := by
    letI : MetricSpace M := g.toMetricSpace
    intro x y z hz
    let schedule := coherence.schedule x y z hz
    let hfirst := coherence.firstClose x y z hz
    have hzBall :
        z ∈ Metric.ball y (terminalDistanceRadius g y hmesh) :=
      coherence.domain_subset_terminalBall y hz.2
    have hdist : dist z y < terminalDistanceRadius g y hmesh := by
      simpa only [Metric.mem_ball] using hzBall
    rcases
        package.terminalShortPathCertificate_of_dist_lt_terminalDistanceRadius
          hmesh schedule hdist with
      ⟨terminalPath⟩
    exact
      package.adaptiveSecondCloseness_of_terminalPathELength_lt_mesh_of_accumulatedMesh
        certificate schedule hcurv hfirst terminalPath
          (coherence.accumulatedScalar x y z hz)

/-- Canonical rooted restricted adaptive coherence supplies the unit-curvature
recognition interface through restricted diagonal Cartan gluing. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedAdaptiveOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            Nonempty (RestrictedAdaptiveOverlapCoherence package hcurv)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, coherence⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3 package hcurv⟩

/-- The distance-shrunk accumulated-mesh interface therefore suffices for the
complete unit-curvature recognition conclusion. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedAccumulatedMeshOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                ∃ certificate :
                    PrescribedMeshCertificate package.realization mesh,
                  Nonempty
                    (RestrictedAccumulatedMeshOverlapCoherence
                      package hcurv hmesh certificate)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedAdaptiveOverlapCoherence
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, mesh, hmesh, certificate, coherence⟩
  refine ⟨skeleton, package, ?_⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedAdaptiveOverlapCoherence
      package hcurv hmesh certificate⟩

/-- The minimal finite payload on the canonical terminal-restricted domains
already suffices for the complete unit-curvature recognition conclusion. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedTerminalRestrictedAccumulatedMeshOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                ∃ certificate :
                    PrescribedMeshCertificate package.realization mesh,
                  Nonempty
                    (TerminalRestrictedAccumulatedMeshOverlapCoherence
                      package hcurv hmesh certificate)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedAccumulatedMeshOverlapCoherence
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, mesh, hmesh, certificate, coherence⟩
  refine ⟨skeleton, package, mesh, hmesh, certificate, ?_⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedAccumulatedMeshOverlapCoherence
      package hcurv hmesh certificate⟩

end CanonicalRootedRealizationPackage
end CartanCanonicalRootedEndpointAssembly
end Poincare
