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

universe u v

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

section DimensionThree

variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]

local notation "G3" => ClosedSmoothRiemannianMetric 3 M

/-- Compactness of the real-time metric orbit closure in the explicit scalar
metric-entry third-jet topology supplies a uniform full covariant-Ricci
derivative bound for the original family. -/
theorem exists_uniformCovariantRicciDerivativeNormBound_of_compact_closedMetricThirdJetOrbitClosure
    (gt : ℝ → G3)
    (hOrbitCompact :
      letI : TopologicalSpace G3 :=
        closedSmoothRiemannianMetricEntryThirdJetTopology (n := 3) (M := M)
      IsCompact (closure (Set.range gt))) :
    ∃ D : ℝ, UniformCovariantRicciDerivativeNormBound gt D := by
  letI : TopologicalSpace G3 :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := 3) (M := M)
  let K := closure (Set.range gt)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hOrbitCompact
  letI : Nonempty K :=
    ⟨⟨gt 0, subset_closure ⟨0, rfl⟩⟩⟩
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
