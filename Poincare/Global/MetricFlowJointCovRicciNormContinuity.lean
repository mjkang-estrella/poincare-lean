import Poincare.Global.CovRicciNormBasis
import Poincare.Global.MetricFlowJointCovRicciEntryRegularity

/-!
# Joint continuity of the coordinate covariant Ricci norm

This module forms the full fixed-basis contraction of the coordinate
covariant Ricci entries.  It proves continuity of that coordinate expression
at the time-space anchor.  No equality with the intrinsic covariant Ricci
norm is asserted here.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The full fixed-basis contraction of two coordinate covariant Ricci
entries against three inverse-metric coefficient fields. -/
noncomputable def anchorChartCovRicciNormSqFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) : ℝ :=
  let e := Module.finBasis ℝ E
  ∑ a, ∑ i, ∑ j, ∑ b, ∑ k, ∑ l,
    anchorChartInverseMetricCoeffFlow gt x t z a b *
      anchorChartInverseMetricCoeffFlow gt x t z i k *
      anchorChartInverseMetricCoeffFlow gt x t z j l *
      anchorChartCovRicciEntryFlow gt x t z (e b) (e k) (e l) *
      anchorChartCovRicciEntryFlow gt x t z (e a) (e i) (e j)

private theorem continuousAt_finset_sum_real
    {X ι : Type*} [TopologicalSpace X] {p : X}
    (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ r ∈ s, ContinuousAt (f r) p) :
    ContinuousAt (fun q ↦ ∑ r ∈ s, f r q) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) p)
  | @insert r s hr ih =>
      have hrCont : ContinuousAt (f r) p :=
        hf r (Finset.mem_insert_self r s)
      have hsCont : ContinuousAt (fun q ↦ ∑ k ∈ s, f k q) p :=
        ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hr] using hrCont.add hsCont

/-- Joint `C³` metric entries make the full coordinate covariant Ricci norm
contraction jointly continuous at the time-space anchor. -/
theorem anchorChartCovRicciNormSqFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt
      (Function.uncurry (anchorChartCovRicciNormSqFlow gt x))
      (t₀, extChartAt I x x) := by
  classical
  let e := Module.finBasis ℝ E
  unfold anchorChartCovRicciNormSqFlow
  dsimp only
  apply continuousAt_finset_sum_real Finset.univ
  intro a _ha
  apply continuousAt_finset_sum_real Finset.univ
  intro i _hi
  apply continuousAt_finset_sum_real Finset.univ
  intro j _hj
  apply continuousAt_finset_sum_real Finset.univ
  intro b _hb
  apply continuousAt_finset_sum_real Finset.univ
  intro k _hk
  apply continuousAt_finset_sum_real Finset.univ
  intro l _hl
  have hab : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z a b))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint a b).continuousAt
  have hik : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z i k))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint i k).continuousAt
  have hjl : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z j l))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint j l).continuousAt
  have hbkl : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z
          (e b) (e k) (e l)))
      (t₀, extChartAt I x x) :=
    anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
      hJoint (e b) (e k) (e l)
  have haij : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z
          (e a) (e i) (e j)))
      (t₀, extChartAt I x x) :=
    anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
      hJoint (e a) (e i) (e j)
  exact ((((hab.mul hik).mul hjl).mul hbkl).mul haij)

end Poincare
