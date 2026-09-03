import Poincare.Global.MetricFlowJointPinchingEvolution

/-!
# Joint continuity of coordinate covariant Ricci entries

This module expands one coordinate component of the covariant derivative of
Ricci in a fixed anchor chart. The result stays at the coordinate level; no
identification with the intrinsic covariant derivative is made here.
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

/-- A fixed-coordinate component of the anchor-chart covariant derivative of
Ricci. The Christoffel field keeps its section-first argument order. -/
noncomputable def anchorChartCovRicciEntryFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z a i j : E) : ℝ :=
  let b := Module.finBasis ℝ E
  fderiv ℝ (fun z' : E ↦ anchorChartRicciEntryFlow gt x t z' i j) z a -
    (∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (anchorChartChristoffelFieldFlow gt x t z i a) *
      anchorChartRicciEntryFlow gt x t z (b r) j) -
    ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (anchorChartChristoffelFieldFlow gt x t z j a) *
      anchorChartRicciEntryFlow gt x t z i (b r)

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

/-- Joint `C³` metric entries make each fixed-coordinate covariant Ricci
entry jointly continuous in time and anchor-chart position. -/
theorem anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (a i j : E) :
    ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z a i j))
      (t₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have hDMap : ContinuousAt
      (fun p : ℝ × E ↦
        fderiv ℝ
          (fun z : E ↦ anchorChartRicciEntryFlow gt x p.1 z i j) p.2)
      (t₀, q) := by
    simpa [q] using
      anchorChartRicciEntryFlow_spatialFDeriv_continuousAt_of_metricEntries
        hJoint i j
  have hD : ContinuousAt
      (fun p : ℝ × E ↦
        fderiv ℝ
          (fun z : E ↦ anchorChartRicciEntryFlow gt x p.1 z i j) p.2 a)
      (t₀, q) :=
    hDMap.clm_apply continuousAt_const
  have hGamma : ContDiffAt ℝ 2
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries
        hJoint
  have hGammaIA : ContinuousAt
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow gt x p.1 p.2 i a) (t₀, q) := by
    simpa [Function.uncurry] using
      ((hGamma.clm_apply (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ i) (t₀, q))).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ a) (t₀, q))).continuousAt
  have hGammaJA : ContinuousAt
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow gt x p.1 p.2 j a) (t₀, q) := by
    simpa [Function.uncurry] using
      ((hGamma.clm_apply (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ j) (t₀, q))).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ a) (t₀, q))).continuousAt
  have hFirstCorrection : ContinuousAt
      (fun p : ℝ × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFlow gt x p.1 p.2 i a) *
          anchorChartRicciEntryFlow gt x p.1 p.2 (b r) j)
      (t₀, q) := by
    apply continuousAt_finset_sum_real Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x p.1 p.2 i a)) (t₀, q) := by
      exact (continuousAt_const.clm_apply hGammaIA)
    have hRic : ContinuousAt
        (fun p : ℝ × E ↦
          anchorChartRicciEntryFlow gt x p.1 p.2 (b r) j) (t₀, q) := by
      simpa [Function.uncurry] using
        (anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
          hJoint (b r) j).continuousAt
    exact hcoord.mul hRic
  have hSecondCorrection : ContinuousAt
      (fun p : ℝ × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFlow gt x p.1 p.2 j a) *
          anchorChartRicciEntryFlow gt x p.1 p.2 i (b r))
      (t₀, q) := by
    apply continuousAt_finset_sum_real Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x p.1 p.2 j a)) (t₀, q) := by
      exact (continuousAt_const.clm_apply hGammaJA)
    have hRic : ContinuousAt
        (fun p : ℝ × E ↦
          anchorChartRicciEntryFlow gt x p.1 p.2 i (b r)) (t₀, q) := by
      simpa [Function.uncurry] using
        (anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
          hJoint i (b r)).continuousAt
    exact hcoord.mul hRic
  unfold anchorChartCovRicciEntryFlow
  dsimp only
  simpa [Function.uncurry, q, b] using
    (hD.sub hFirstCorrection).sub hSecondCorrection

end Poincare
