import Poincare.Global.MetricFamilyCovRicciNormContinuity

/-!
# Coordinate covariant Ricci continuity for metric families

This module gives a concrete producer for the chartwise covariant-Ricci
continuity interface over an arbitrary topological parameter space.  The
inputs stop one derivative earlier: inverse-metric coefficients, Christoffel
values, Ricci entries, and the spatial derivative of each Ricci entry.
-/

noncomputable section

open Bundle Filter Function
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The anchor-chart Christoffel field for a metric family, obtained by
viewing one family member as a constant real-parameter flow. -/
noncomputable def anchorChartChristoffelFieldFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z u w : E) : E :=
  anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ g k) x 0 z u w

omit [T2Space M] in
/-- Continuity of a family metric and its first spatial chart derivative
constructs continuity of every fixed Christoffel value. -/
theorem anchorChartChristoffelFieldFamily_continuousAt_of_blendedMetric
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (hG : ContinuousAt
      (Function.uncurry (anchorBlendedMetricFamily g x))
      (k₀, extChartAt I x x))
    (hD : ContinuousAt
      (fun p : K × E ↦
        fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2)
      (k₀, extChartAt I x x))
    (u w : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w)
      (k₀, extChartAt I x x) := by
  let q : E := extChartAt I x x
  have hInvMap : ContinuousAt ContinuousLinearMap.inverse
      (anchorBlendedMetricFamily g x k₀ q) :=
    ((anchorBlendedMetricFamily_isInvertible g x k₀ q)
      |>.contDiffAt_map_inverse (n := 0)).continuousAt
  have hInv : ContinuousAt
      (fun p : K × E ↦
        (anchorBlendedMetricFamily g x p.1 p.2).inverse)
      (k₀, q) := by
    simpa [Function.comp_def, q] using hInvMap.comp_of_eq hG rfl
  have hDflip : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2).flip)
      (k₀, q) := by
    exact
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
        |>.continuousAt.comp_of_eq hD rfl
  have hDflipW : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2).flip w)
      (k₀, q) :=
    hDflip.clm_apply continuousAt_const
  have hDflipWFlip : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip)
      (k₀, q) := by
    exact
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
        |>.continuousAt.comp_of_eq hDflipW rfl
  have hThird : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ
          (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u)
      (k₀, q) :=
    hDflipWFlip.clm_apply continuousAt_const
  have hDw : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) w)
      (k₀, q) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) w).continuous
      |>.continuousAt.comp_of_eq hD rfl
  have hFirst : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) w) u)
      (k₀, q) :=
    hDw.clm_apply continuousAt_const
  have hDu : ContinuousAt
      (fun p : K × E ↦
        (fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) u)
      (k₀, q) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) u).continuous
      |>.continuousAt.comp_of_eq hD rfl
  have hSecond : ContinuousAt
      (fun p : K × E ↦
        ((fderiv ℝ (anchorBlendedMetricFamily g x p.1) p.2) u) w)
      (k₀, q) :=
    hDu.clm_apply continuousAt_const
  have hKoszul : ContinuousAt
      (fun p : K × E ↦
        (1 / 2 : ℝ) •
          (((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2) w) u
            + ((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2) u) w
            - ((fderiv ℝ
              (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u))
      (k₀, q) :=
    (hFirst.add hSecond |>.sub hThird).const_smul (1 / 2 : ℝ)
  have hResult := hInv.clm_apply hKoszul
  have heq :
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w) =
      fun p : K × E ↦
        (anchorBlendedMetricFamily g x p.1 p.2).inverse
          ((1 / 2 : ℝ) •
            (((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2) w) u
              + ((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2) u) w
              - ((fderiv ℝ
                (anchorBlendedMetricFamily g x p.1) p.2).flip w).flip u)) := by
    funext p
    rw [anchorChartChristoffelFieldFamily,
      anchorChartChristoffelFieldFlow_apply,
      anchorChartChristoffelFlow_apply_eq_inverse_koszul]
    rfl
  rw [heq]
  exact hResult

/-- A coordinate Ricci entry for a metric family, obtained by viewing one
family member as a constant real-parameter flow. -/
noncomputable def anchorChartRicciEntryFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z i j : E) : ℝ :=
  anchorChartRicciEntryFlow (fun _ : ℝ ↦ g k) x 0 z i j

/-- The spatial derivative of a family Ricci entry in one anchor chart. -/
noncomputable def anchorChartRicciEntrySpatialFDerivFamily
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M) (x : M)
    (k : K) (z i j : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun z' : E ↦ anchorChartRicciEntryFamily g x k z' i j) z

/-- Chart data sufficient to construct continuous coordinate covariant-Ricci
entries for a metric family at one parameter and manifold anchor. -/
structure MetricFamilyRicciJetChartContinuousAt
    {K : Type v} [TopologicalSpace K]
    (g : K → ClosedSmoothRiemannianMetric n M) (k₀ : K) (x : M) : Prop where
  inverseCoeff : ∀ i j : Fin (Module.finrank ℝ E),
    ContinuousAt
      (fun p : K × E ↦
        anchorChartInverseMetricCoeffFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)
  christoffel : ∀ u w : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 u w)
      (k₀, extChartAt I x x)
  ricciEntry : ∀ i j : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntryFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)
  ricciSpatialFDeriv : ∀ i j : E,
    ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
      (k₀, extChartAt I x x)

private theorem continuousAt_finset_sum_ricci_jet
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

omit [T2Space M] in
/-- The lower-order chart data constructs every continuous coordinate
covariant-Ricci entry. -/
theorem anchorChartCovRicciEntryFamily_continuousAt_of_ricciJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt g k₀ x)
    (a i j : E) :
    ContinuousAt
      (fun p : K × E ↦
        anchorChartCovRicciEntryFamily g x p.1 p.2 a i j)
      (k₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have hDMap : ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j)
      (k₀, q) := by
    simpa [q] using h.ricciSpatialFDeriv i j
  have hD : ContinuousAt
      (fun p : K × E ↦
        anchorChartRicciEntrySpatialFDerivFamily g x p.1 p.2 i j a)
      (k₀, q) :=
    hDMap.clm_apply continuousAt_const
  have hGammaIA : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 i a)
      (k₀, q) := by
    simpa [q] using h.christoffel i a
  have hGammaJA : ContinuousAt
      (fun p : K × E ↦
        anchorChartChristoffelFieldFamily g x p.1 p.2 j a)
      (k₀, q) := by
    simpa [q] using h.christoffel j a
  have hFirstCorrection : ContinuousAt
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFamily g x p.1 p.2 i a) *
          anchorChartRicciEntryFamily g x p.1 p.2 (b r) j)
      (k₀, q) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : K × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFamily g x p.1 p.2 i a))
        (k₀, q) :=
      continuousAt_const.clm_apply hGammaIA
    have hRic : ContinuousAt
        (fun p : K × E ↦
          anchorChartRicciEntryFamily g x p.1 p.2 (b r) j)
        (k₀, q) := by
      simpa [q] using h.ricciEntry (b r) j
    exact hcoord.mul hRic
  have hSecondCorrection : ContinuousAt
      (fun p : K × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFamily g x p.1 p.2 j a) *
          anchorChartRicciEntryFamily g x p.1 p.2 i (b r))
      (k₀, q) := by
    apply continuousAt_finset_sum_ricci_jet Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : K × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFamily g x p.1 p.2 j a))
        (k₀, q) :=
      continuousAt_const.clm_apply hGammaJA
    have hRic : ContinuousAt
        (fun p : K × E ↦
          anchorChartRicciEntryFamily g x p.1 p.2 i (b r))
        (k₀, q) := by
      simpa [q] using h.ricciEntry i (b r)
    exact hcoord.mul hRic
  unfold anchorChartCovRicciEntryFamily anchorChartCovRicciEntryFlow
  dsimp only
  simpa [anchorChartRicciEntrySpatialFDerivFamily,
    anchorChartChristoffelFieldFamily, anchorChartRicciEntryFamily, q, b] using
    (hD.sub hFirstCorrection).sub hSecondCorrection

omit [T2Space M] in
/-- The Ricci-jet chart data supplies the chart interface used by the
coordinate norm contraction. -/
theorem metricFamilyCovRicciChartContinuousAt_of_ricciJet
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
    (h : MetricFamilyRicciJetChartContinuousAt g k₀ x) :
    MetricFamilyCovRicciChartContinuousAt g k₀ x where
  inverseCoeff := h.inverseCoeff
  covRicciEntry :=
    anchorChartCovRicciEntryFamily_continuousAt_of_ricciJet h

/-- Ricci-jet chart data at every point gives global joint continuity of the
intrinsic squared covariant Ricci norm. -/
theorem continuous_covRicciNormSqAt_joint_of_ricciJetChartContinuous
    {K : Type v} [TopologicalSpace K]
    {g : K → ClosedSmoothRiemannianMetric n M}
    (h : ∀ k : K, ∀ x : M,
      MetricFamilyRicciJetChartContinuousAt g k x) :
    Continuous (fun p : K × M ↦ covRicciNormSqAt (g p.1) p.2) :=
  continuous_covRicciNormSqAt_joint_of_chartContinuous
    (fun k x ↦ metricFamilyCovRicciChartContinuousAt_of_ricciJet (h k x))

end Poincare
