import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary
import Poincare.Global.DifferentialSuccessorAdaptiveFeedbackIteration

/-!
# Compact-history reduction for generic post-realization grids

The finite post-realization recognition boundary asks for an actual grid
certificate on every restricted overlap.  This file separates that
certificate into two honest layers.

First, a *precertificate* stores only the geometric information needed to
realize the differential grid from the uniform generic successor radius:
the common predecessor, the two terminal-index bounds, and horizontal and
vertical half-radius smallness.  The resulting grid is therefore an actual
`genericRealizedGridFromUniformRadius`, not an independently supplied grid.
Its horizontal and vertical defects are the maxima of the actual finite edge
families.  Each maximum is below a radius exactly when the corresponding
mesh-smallness predicate holds.

Second, a compact-history package supplies a sequence of these geometric
precertificates.  Their common mesh radii are the values of one positive
lower-semicontinuous function on a compact history set, while both actual
finite defect maxima tend uniformly to zero.  The existing two-stage
compact-history theorem applies with the second radius equal to the first.
Consequently some realized stage is small at its own post-realization radius
and hence gives the required grid certificate.

No grid certificate, endpoint equality, germ equality, compatible atlas, or
sphere-recognition conclusion is stored in the compact-history package.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanGenericPostRealizationCompactHistoryReduction

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedDirectGenericNeighborhoodRecognition
open CartanFixedTargetMovingAdaptiveRecognitionBoundary
open CartanGenericRootedAdaptiveFiniteGridRecognition
open CartanRootedOverlapReparameterizedGridRealization
open CartanRootedOverlapReparameterizedHomotopyGrid
open DifferentialSuccessorAdaptiveFeedbackIteration

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-! ## Geometric precertificates and actual finite defects -/

/-- The geometric part of one generic post-realization grid certificate.

These four fields are exactly the data used to realize the differential
grid.  In particular, neither post-realization smallness nor any equality
conclusion is retained here. -/
structure GenericUniformRadiusPostRealizationGridPrecertificate
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y) where
  commonPredecessor : ℕ
  left_terminalIndex_le :
    endpoint.terminalIndex x ≤ commonPredecessor
  right_terminalIndex_le :
    endpoint.terminalIndex y ≤ commonPredecessor
  horizontalHalfRadius : HorizontalHalfRadiusSmall endpoint
    (genericTerminalCertificate endpoint hmesh hz.1)
    (genericTerminalCertificate endpoint hmesh hz.2)
    commonPredecessor successor.radius
  verticalHalfRadius : VerticalHalfRadiusSmall endpoint
    (genericTerminalCertificate endpoint hmesh hz.1)
    (genericTerminalCertificate endpoint hmesh hz.2)
    commonPredecessor successor.radius

namespace GenericUniformRadiusPostRealizationGridPrecertificate

/-- The actual differential grid computed from the geometric precertificate. -/
noncomputable def grid
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid endpoint
      (genericTerminalCertificate endpoint hmesh hz.1)
      (genericTerminalCertificate endpoint hmesh hz.2)
      precertificate.commonPredecessor :=
  genericRealizedGridFromUniformRadius successor endpoint hmesh hz
    precertificate.commonPredecessor
      precertificate.left_terminalIndex_le
      precertificate.right_terminalIndex_le
      precertificate.horizontalHalfRadius
      precertificate.verticalHalfRadius

/-- One actual horizontal edge length of the realized grid. -/
def horizontalEdgeDistance
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz)
    (a : Fin (precertificate.commonPredecessor + 3) ×
      Fin (precertificate.commonPredecessor + 2)) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    dist
      (reparameterizedOverlapGridRow endpoint
        (genericTerminalCertificate endpoint hmesh hz.1)
        (genericTerminalCertificate endpoint hmesh hz.2)
        precertificate.commonPredecessor a.1 (a.2 + 1))
      (reparameterizedOverlapGridRow endpoint
        (genericTerminalCertificate endpoint hmesh hz.1)
        (genericTerminalCertificate endpoint hmesh hz.2)
        precertificate.commonPredecessor a.1 a.2)

/-- One actual vertical edge length of the realized grid. -/
def verticalEdgeDistance
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz)
    (a : Fin (precertificate.commonPredecessor + 2) ×
      Fin (precertificate.commonPredecessor + 2)) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    dist
      (reparameterizedOverlapGridRow endpoint
        (genericTerminalCertificate endpoint hmesh hz.1)
        (genericTerminalCertificate endpoint hmesh hz.2)
        precertificate.commonPredecessor (a.1 + 1) (a.2 + 1))
      (reparameterizedOverlapGridRow endpoint
        (genericTerminalCertificate endpoint hmesh hz.1)
        (genericTerminalCertificate endpoint hmesh hz.2)
        precertificate.commonPredecessor a.1 (a.2 + 1))

/-- The maximum of all actual horizontal edge lengths in the finite grid. -/
def horizontalDefect
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    precertificate.horizontalEdgeDistance

/-- The maximum of all actual vertical edge lengths in the finite grid. -/
def verticalDefect
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    precertificate.verticalEdgeDistance

/-- The horizontal defect maximum is below `eta` exactly when every actual
horizontal edge of the computed grid is below `eta`. -/
theorem horizontalDefect_lt_iff
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz)
    (eta : ℝ) :
    precertificate.horizontalDefect < eta ↔
      precertificate.grid.HorizontalSmall eta := by
  letI : MetricSpace M := g.toMetricSpace
  change precertificate.horizontalDefect < eta ↔
    ∀ m : Fin (precertificate.commonPredecessor + 3),
      ∀ j : Fin (precertificate.commonPredecessor + 2),
        precertificate.horizontalEdgeDistance (m, j) < eta
  rw [horizontalDefect, Finset.sup'_lt_iff]
  constructor
  · intro h m j
    exact h (m, j) (Finset.mem_univ _)
  · intro h a _ha
    exact h a.1 a.2

/-- The vertical defect maximum is below `eta` exactly when every actual
vertical edge of the computed grid is below `eta`. -/
theorem verticalDefect_lt_iff
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz)
    (eta : ℝ) :
    precertificate.verticalDefect < eta ↔
      precertificate.grid.VerticalSmall eta := by
  letI : MetricSpace M := g.toMetricSpace
  change precertificate.verticalDefect < eta ↔
    ∀ m : Fin (precertificate.commonPredecessor + 2),
      ∀ j : Fin (precertificate.commonPredecessor + 2),
        precertificate.verticalEdgeDistance (m, j) < eta
  rw [verticalDefect, Finset.sup'_lt_iff]
  constructor
  · intro h m j
    exact h (m, j) (Finset.mem_univ _)
  · intro h a _ha
    exact h a.1 a.2

/-- Post-realization smallness upgrades the geometric precertificate to the
existing proof-bearing finite-grid certificate. -/
def toGridCertificate
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (precertificate : GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz)
    (hhorizontal : precertificate.grid.HorizontalSmall
      (precertificate.grid.commonMeshRadius hcurv))
    (hvertical : precertificate.grid.VerticalSmall
      (precertificate.grid.commonMeshRadius hcurv)) :
    GenericUniformRadiusPostRealizationGridCertificate
      successor endpoint hcurv hmesh x y z hz where
  commonPredecessor := precertificate.commonPredecessor
  left_terminalIndex_le := precertificate.left_terminalIndex_le
  right_terminalIndex_le := precertificate.right_terminalIndex_le
  horizontalHalfRadius := precertificate.horizontalHalfRadius
  verticalHalfRadius := precertificate.verticalHalfRadius
  horizontalSmall := hhorizontal
  verticalSmall := hvertical

end GenericUniformRadiusPostRealizationGridPrecertificate

/-! ## Compact histories of actual precertificates -/

/-- A compactly parameterized sequence of actual geometric
precertificates for one restricted overlap.

The common mesh radius at every stage is the restriction of one positive
lower-semicontinuous threshold on a fixed compact history set.  The two
vanishing fields concern the actual finite defect maxima defined above. -/
structure GenericUniformRadiusPostRealizationCompactHistory
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y) where
  History : Type u
  [historyTopology : TopologicalSpace History]
  compactHistory : Set History
  isCompact_compactHistory : IsCompact compactHistory
  stage : ℕ → History
  stage_mem_compactHistory : ∀ n, stage n ∈ compactHistory
  threshold : History → ℝ
  threshold_lowerSemicontinuous :
    LowerSemicontinuousOn threshold compactHistory
  threshold_pos : ∀ a ∈ compactHistory, 0 < threshold a
  precertificate : ℕ →
    GenericUniformRadiusPostRealizationGridPrecertificate
      successor endpoint hmesh x y z hz
  commonMeshRadius_eq_threshold : ∀ n,
    (precertificate n).grid.commonMeshRadius hcurv = threshold (stage n)
  defects_vanish : ∀ delta > (0 : ℝ), ∃ N, ∀ n ≥ N,
    (precertificate n).horizontalDefect < delta ∧
      (precertificate n).verticalDefect < delta

namespace GenericUniformRadiusPostRealizationCompactHistory

/-- Compact lower-semicontinuity and vanishing actual finite defects select
one stage that is small at its own post-realization common radius. -/
theorem nonempty_gridCertificate
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (history : GenericUniformRadiusPostRealizationCompactHistory
      successor endpoint hcurv hmesh x y z hz) :
    Nonempty
      (GenericUniformRadiusPostRealizationGridCertificate
        successor endpoint hcurv hmesh x y z hz) := by
  letI : TopologicalSpace history.History := history.historyTopology
  let epsilon : ℕ → ℝ := fun n ↦
    (history.precertificate n).grid.commonMeshRadius hcurv
  let firstDefect : ℕ → ℝ := fun n ↦
    (history.precertificate n).horizontalDefect
  let secondDefect : ℕ → ℝ := fun n ↦
    (history.precertificate n).verticalDefect
  let radius : ∀ n, firstDefect n < epsilon n → ℝ :=
    fun n _hfirst ↦ epsilon n
  have hactive : ∀ n,
      twoStageActiveThreshold epsilon firstDefect radius n = epsilon n := by
    intro n
    by_cases hfirst : firstDefect n < epsilon n
    · simp [twoStageActiveThreshold, hfirst, radius]
    · simp [twoStageActiveThreshold, hfirst]
  have hparameterized : ∀ n,
      twoStageActiveThreshold epsilon firstDefect radius n =
        history.threshold (history.stage n) := by
    intro n
    exact (hactive n).trans (history.commonMeshRadius_eq_threshold n)
  have hvanish : ∀ delta > (0 : ℝ), ∃ N, ∀ n ≥ N,
      firstDefect n < delta ∧ secondDefect n < delta := by
    simpa [firstDefect, secondDefect] using history.defects_vanish
  rcases
      exists_twoStageValidated_of_compact_history_lowerSemicontinuous_threshold
        history.isCompact_compactHistory history.stage
          history.stage_mem_compactHistory history.threshold
          history.threshold_lowerSemicontinuous history.threshold_pos
          epsilon firstDefect secondDefect radius hparameterized hvanish with
    ⟨n, hvalidated⟩
  rcases hvalidated with ⟨hfirst, hsecond⟩
  have hhorizontal :
      (history.precertificate n).grid.HorizontalSmall
        ((history.precertificate n).grid.commonMeshRadius hcurv) :=
    ((history.precertificate n).horizontalDefect_lt_iff _).1 (by
      simpa [firstDefect, epsilon] using hfirst)
  have hvertical :
      (history.precertificate n).grid.VerticalSmall
        ((history.precertificate n).grid.commonMeshRadius hcurv) :=
    ((history.precertificate n).verticalDefect_lt_iff _).1 (by
      simpa [secondDefect, radius, epsilon] using hsecond)
  exact
    ⟨(history.precertificate n).toGridCertificate hhorizontal hvertical⟩

end GenericUniformRadiusPostRealizationCompactHistory

/-! ## Per-overlap and fixed-target lifts -/

/-- Compact-history feedback data for every overlap in one selected generic
restricted endpoint atlas. -/
structure GenericUniformRadiusPostRealizationCompactHistoryCoherence
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapHistory : ∀ x y z : M,
    ∀ hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y,
      GenericUniformRadiusPostRealizationCompactHistory
        successor endpoint hcurv hmesh x y z hz

/-- Every per-overlap compact-history payload terminates, giving the existing
post-realization grid-coherence record. -/
noncomputable def
    GenericUniformRadiusPostRealizationCompactHistoryCoherence.toGridCoherence
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    (coherence : GenericUniformRadiusPostRealizationCompactHistoryCoherence
      successor endpoint hcurv hmesh) :
    GenericUniformRadiusPostRealizationGridCoherence
      successor endpoint hcurv hmesh where
  overlapCertificate := by
    intro x y z hz
    exact Classical.choice
      (coherence.overlapHistory x y z hz).nonempty_gridCertificate

/-- Fixed-target compact-history feedback at the exact successor and endpoint
selected from the moving-chart generic-data inputs. -/
def FixedTargetMovingCompactHistoryPostRealizationFeedback3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (inputs : FixedTargetMovingGenericSuccessorInputs3 M) : Prop :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (g : ClosedSmoothRiemannianMetric 3 M),
        ∀ hcurv : HasConstantSectionalCurvature3 g 1,
          let dataStability :=
            localGenericSuccessorDataCover_of_fixedTargetMovingInputs3
              inputs g hcurv
          let successor :=
            uniformGenericSuccessorRadiusCertificateOfNeighborhood
              g dataStability.toUniversalSuccessorDataNeighborhood
          let endpoint := rootedEndpointOfUniformGenericSuccessorRadius
            successor
          ∃ mesh : ℝ,
            ∃ hmesh : 0 < mesh,
              Nonempty
                (GenericUniformRadiusPostRealizationCompactHistoryCoherence
                  successor endpoint hcurv hmesh)

/-- Compact-history feedback supplies the existing fixed-target
post-realization grid-coherence completion. -/
theorem fixedTargetMovingPostRealizationGridCoherence3_of_compactHistoryFeedback
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    {inputs : FixedTargetMovingGenericSuccessorInputs3 M}
    (feedback :
      FixedTargetMovingCompactHistoryPostRealizationFeedback3 M inputs) :
    FixedTargetMovingPostRealizationGridCoherence3 M inputs := by
  intro _chartedSpace _smoothManifold _secondCountable _connected g hcurv
  rcases feedback g hcurv with ⟨mesh, hmesh, compactCoherence⟩
  rcases compactCoherence with ⟨compactCoherence⟩
  exact ⟨mesh, hmesh, ⟨compactCoherence.toGridCoherence⟩⟩

end CartanGenericPostRealizationCompactHistoryReduction
end Poincare
