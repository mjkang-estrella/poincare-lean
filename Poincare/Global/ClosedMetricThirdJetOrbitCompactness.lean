import Poincare.Global.ClosedMetricThirdJetTopology
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciPositiveEinstein

/-!
# Covariant-Ricci bounds from compact third-jet metric orbits

The scalar metric-entry third-jet topology makes the intrinsic squared
covariant-Ricci norm continuous on the closure of any metric orbit.  If that
orbit closure is compact, the existing compact-family maximum theorem gives
a uniform covariant-Ricci derivative bound for the original real-time family.

Both results install the third-jet topology locally.  They do not assert that
an arbitrary orbit closure is compact.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v w

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "G" => ClosedSmoothRiemannianMetric n M

/-- In the explicit scalar metric-entry third-jet topology, the squared
intrinsic covariant-Ricci norm is jointly continuous on any metric-orbit
closure times the manifold. -/
theorem continuous_covRicciNormSqAt_joint_on_closedMetricThirdJetOrbitClosure
    {I : Type v} (gt : I → G) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    Continuous (fun p : closure (Set.range gt) × M ↦
      covRicciNormSqAt (p.1 : G) p.2) := by
  letI : TopologicalSpace G :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  exact continuous_covRicciNormSqAt_joint_of_metricFamilyEntryThirdJets
    (fun k x ↦
      metricFamilyBlendedMetricEntryThirdJetContinuousAt_subtype
        (closure (Set.range gt)) k x)

omit [T2Space M] in
/-- A continuous compact family in the scalar third-jet topology has compact
orbit closure whenever every orbit value is realized by that family.  The
indexing map needs no continuity because only its range inclusion is used. -/
theorem isCompact_closedMetricThirdJetOrbitClosure_of_compact_realization
    {I : Type w} {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : I → G) (metric : K → G) (parameter : I → K)
    (hmetric :
      letI : TopologicalSpace G :=
        closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
      Continuous metric)
    (hrealize : ∀ i, metric (parameter i) = gt i) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    IsCompact (closure (Set.range gt)) := by
  letI : TopologicalSpace G :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  letI : T2Space G :=
    (metricEntryThirdJetProfile_isEmbedding (n := n) (M := M)).t2Space
  have hmetric' : Continuous metric := hmetric
  have hfamily : IsCompact (Set.range metric) := isCompact_range hmetric'
  have horbit : Set.range gt ⊆ Set.range metric := by
    rintro _ ⟨i, rfl⟩
    exact ⟨parameter i, hrealize i⟩
  exact hfamily.of_isClosed_subset isClosed_closure
    (closure_minimal horbit hfamily.isClosed)

omit [T2Space M] in
/-- Compactness of a metric-orbit closure in the explicit third-jet topology
is exactly compactness of the ambient profile closure after restricting to
profiles that are realized by actual metrics.  The intersection with the
profile range is essential: the profile is an embedding, but its range need
not be closed in the ambient compact-open product. -/
theorem isCompact_closedMetricThirdJetOrbitClosure_iff_profileClosure_inter_range
    {I : Type v} (gt : I → G) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    IsCompact (closure (Set.range gt)) ↔
      IsCompact
        (closure
            (Set.range
              (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)) ∩
          Set.range (metricEntryThirdJetProfile (n := n) (M := M))) := by
  letI : TopologicalSpace G :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  let profile := metricEntryThirdJetProfile (n := n) (M := M)
  have hprofile : Topology.IsEmbedding profile :=
    metricEntryThirdJetProfile_isEmbedding (n := n) (M := M)
  rw [hprofile.isCompact_iff]
  rw [hprofile.closure_eq_preimage_closure_image]
  rw [Set.image_preimage_eq_inter_range]
  simp only [profile, Set.range_comp]

omit [T2Space M] in
/-- Ambient compactness of the profile-orbit closure descends to compactness
of the metric-orbit closure when every profile limit is realized by an actual
metric.  The realized-limit hypothesis cannot be dropped merely because the
profile map is a topological embedding: an embedded range need not be closed. -/
theorem isCompact_closedMetricThirdJetOrbitClosure_of_compact_profileClosure
    {I : Type v} (gt : I → G)
    (hProfileCompact :
      IsCompact
        (closure
          (Set.range
            (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))))
    (hLimitsRealized :
      closure
          (Set.range
            (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)) ⊆
        Set.range (metricEntryThirdJetProfile (n := n) (M := M))) :
    letI : TopologicalSpace G :=
      closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
    IsCompact (closure (Set.range gt)) := by
  letI : TopologicalSpace G :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  rw [isCompact_closedMetricThirdJetOrbitClosure_iff_profileClosure_inter_range
    (n := n) (M := M) gt]
  rwa [inter_eq_left.mpr hLimitsRealized]

section DimensionThree

variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]

local notation "G3" => ClosedSmoothRiemannianMetric 3 M

/-- Compactness of a nonempty metric-family orbit closure in the explicit
scalar metric-entry third-jet topology supplies a uniform full
covariant-Ricci derivative bound for the original family. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_compact_closedMetricThirdJetOrbitClosure
    {I : Type v} [Nonempty I]
    (gt : I → G3)
    (hOrbitCompact :
      letI : TopologicalSpace G3 :=
        closedSmoothRiemannianMetricEntryThirdJetTopology (n := 3) (M := M)
      IsCompact (closure (Set.range gt))) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  letI : TopologicalSpace G3 :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := 3) (M := M)
  let K := closure (Set.range gt)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hOrbitCompact
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  letI : Nonempty K :=
    ⟨⟨gt i₀, subset_closure ⟨i₀, rfl⟩⟩⟩
  have hJoint : Continuous (fun p : K × M ↦
      covRicciNormSqAt (p.1 : G3) p.2) :=
    continuous_covRicciNormSqAt_joint_on_closedMetricThirdJetOrbitClosure gt
  obtain ⟨D, hDpos, hBound⟩ :=
    exists_pos_uniform_covRicciNormSqAt_bound_of_compact_joint
      (fun k : K ↦ (k : G3)) hJoint
  refine ⟨D, hDpos, ?_⟩
  intro t x
  exact hBound ⟨gt t, subset_closure ⟨t, rfl⟩⟩ x

end DimensionThree

end Poincare
