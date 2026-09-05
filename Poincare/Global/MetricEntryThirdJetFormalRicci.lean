import Poincare.Global.MetricEntryThirdJetFormalChristoffel

/-!
# Formal Ricci algebra from scalar third-jet profiles

This module continues the finite-basis reconstruction through curvature,
Ricci, its first coordinate derivative, covariant Ricci, and the full squared
norm contraction.  Every expression is a finite rational or polynomial
formula in the formal metric, its inverse, and the raw metric jets through
order three.

The definitions make sense for arbitrary profiles.  Their continuity is
proved only where the reconstructed metric is invertible.  Agreement with
the intrinsic geometric quantities on genuine profiles is kept as a separate
interface, so no smooth realization claim is hidden here.
-/

noncomputable section

open Bundle Function
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "P" => MetricEntryThirdJetProfileTarget n M

/-- Canonical-basis coordinates of the first formal Christoffel jet. -/
noncomputable def formalProfileChristoffelFirstCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun a i j k => b.coord k
    (formalProfileChristoffelFirstVectorAt p x z a i j)

/-- Canonical-basis coordinates of the second formal Christoffel jet. -/
noncomputable def formalProfileChristoffelSecondCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun a u i j k => b.coord k
    (formalProfileChristoffelSecondVectorAt p x z a u i j)

/-- Curvature coordinates in the convention obtained from the repository's
section-first Christoffel field. -/
noncomputable def formalProfileCurvatureCoordinatesAt
    (p : P) (x : M) (z : E)
    (u v w k : Fin (Module.finrank ℝ E)) : ℝ :=
  let Γ := formalProfileChristoffelCoordinatesAt p x z
  let DΓ := formalProfileChristoffelFirstCoordinatesAt p x z
  DΓ u w v k - DΓ v w u k +
      (∑ l, Γ w v l * Γ l u k) -
    ∑ l, Γ w u l * Γ l v k

/-- First coordinate derivative of the formal curvature array. -/
noncomputable def formalProfileCurvatureFirstCoordinatesAt
    (p : P) (x : M) (z : E)
    (a u v w k : Fin (Module.finrank ℝ E)) : ℝ :=
  let Γ := formalProfileChristoffelCoordinatesAt p x z
  let DΓ := formalProfileChristoffelFirstCoordinatesAt p x z
  let D2Γ := formalProfileChristoffelSecondCoordinatesAt p x z
  D2Γ a u w v k - D2Γ a v w u k +
      (∑ l, (DΓ a w v l * Γ l u k + Γ w v l * DΓ a l u k)) -
    ∑ l, (DΓ a w u l * Γ l v k + Γ w u l * DΓ a l v k)

/-- Formal Ricci entries obtained by the fixed-basis curvature trace. -/
noncomputable def formalProfileRicciCoordinatesAt
    (p : P) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ r, formalProfileCurvatureCoordinatesAt p x z r i j r

/-- First coordinate derivative of the formal Ricci entries. -/
noncomputable def formalProfileRicciFirstCoordinatesAt
    (p : P) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ r, formalProfileCurvatureFirstCoordinatesAt p x z a r i j r

/-- Formal covariant derivative of Ricci in canonical-basis coordinates. -/
noncomputable def formalProfileCovRicciCoordinatesAt
    (p : P) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) : ℝ :=
  let Γ := formalProfileChristoffelCoordinatesAt p x z
  formalProfileRicciFirstCoordinatesAt p x z a i j -
      (∑ r, Γ a i r * formalProfileRicciCoordinatesAt p x z r j) -
    ∑ r, Γ a j r * formalProfileRicciCoordinatesAt p x z i r

/-- Canonical-basis coefficients of the inverse formal metric. -/
noncomputable def formalProfileInverseMetricCoordinatesAt
    (p : P) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  let b := Module.finBasis ℝ E
  b.coord j ((formalProfileMetricAt p x z).inverse
    (LinearMap.toContinuousLinearMap (b.coord i)))

/-- The sixfold fixed-basis contraction giving the squared norm of formal
covariant Ricci. -/
noncomputable def formalProfileCovRicciNormSqAt
    (p : P) (x : M) (z : E) : ℝ :=
  ∑ a, ∑ i, ∑ j, ∑ b, ∑ k, ∑ l,
    formalProfileInverseMetricCoordinatesAt p x z a b *
      formalProfileInverseMetricCoordinatesAt p x z i k *
      formalProfileInverseMetricCoordinatesAt p x z j l *
      formalProfileCovRicciCoordinatesAt p x z b k l *
      formalProfileCovRicciCoordinatesAt p x z a i j

/-- Genuine profiles recover the first Christoffel-jet coordinates. -/
@[simp] theorem formalProfileChristoffelFirstCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileChristoffelFirstCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun a i j k => (Module.finBasis ℝ E).coord k
        (RicciFlow.christoffelDeriv
          (anchorBlendedMetricFamily (fun h : G => h) x g)
          (fun y => fderiv ℝ
            (anchorBlendedMetricFamily (fun h : G => h) x g) y
              ((Module.finBasis ℝ E) a)) z
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  funext a i j k
  simp [formalProfileChristoffelFirstCoordinatesAt]

/-- Genuine profiles recover the second Christoffel-jet coordinates. -/
@[simp] theorem formalProfileChristoffelSecondCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileChristoffelSecondCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun a u i j k => (Module.finBasis ℝ E).coord k
        (christoffelSecondFormula
          (anchorBlendedMetricFamily (fun h : G => h) x g) z
          ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) u)
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  funext a u i j k
  simp [formalProfileChristoffelSecondCoordinatesAt]

/-- Genuine profiles recover the inverse-metric coefficients used by the
existing family contraction. -/
@[simp] theorem formalProfileInverseMetricCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) :
    formalProfileInverseMetricCoordinatesAt
        (metricEntryThirdJetProfile g) x z i j =
      anchorChartInverseMetricCoeffFamily (fun h : G => h) x g z i j := by
  simp [formalProfileInverseMetricCoordinatesAt,
    anchorChartInverseMetricCoeffFamily, anchorChartInverseMetricCoeffFlow,
    anchorBlendedMetricFamily]

private theorem finBasis_coord_clm_apply
    (L : E →L[ℝ] E) (v : E) (k : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).coord k (L v) =
      ∑ l, (Module.finBasis ℝ E).coord l v *
        (Module.finBasis ℝ E).coord k (L ((Module.finBasis ℝ E) l)) := by
  let b := Module.finBasis ℝ E
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum, map_sum]
  simp [b, map_smul, smul_eq_mul, Module.Basis.coord_apply]

/-- On genuine profiles, formal Christoffel coordinates are the coordinates
of the repository's section-first chart Christoffel field, with the two
vector slots reversed. -/
theorem formalProfileChristoffelCoordinate_profile_eq_field
    (g : G) (x : M) (z : E)
    (i j k : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelCoordinatesAt
        (metricEntryThirdJetProfile g) x z i j k =
      (Module.finBasis ℝ E).coord k
        (anchorChartChristoffelFieldOperatorFamily
          (fun h : G => h) x g z
          ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) i)) := by
  rw [anchorChartChristoffelFieldOperatorFamily_apply_eq_christoffelClosedOp]
  simp [formalProfileChristoffelCoordinatesAt]

/-- On genuine profiles, formal first-Christoffel coordinates agree with the
section-first spatial Christoffel derivative. -/
theorem formalProfileChristoffelFirstCoordinate_profile_eq_field
    (g : G) (x : M) (z : E)
    (a i j k : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelFirstCoordinatesAt
        (metricEntryThirdJetProfile g) x z a i j k =
      (Module.finBasis ℝ E).coord k
        (anchorChartChristoffelFieldSpatialFDerivFamily
          (fun h : G => h) x g z ((Module.finBasis ℝ E) a)
          ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) i)) := by
  rw [anchorChartChristoffelFieldSpatialFDerivFamily_apply_eq_christoffelDeriv]
  simp [formalProfileChristoffelFirstCoordinatesAt]

/-- On genuine profiles, formal second-Christoffel coordinates agree with
the section-first second spatial Christoffel derivative. -/
theorem formalProfileChristoffelSecondCoordinate_profile_eq_field
    (g : G) (x : M) (z : E)
    (a u i j k : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelSecondCoordinatesAt
        (metricEntryThirdJetProfile g) x z a u i j k =
      (Module.finBasis ℝ E).coord k
        (anchorChartChristoffelFieldSecondSpatialFDerivFamily
          (fun h : G => h) x g z
          ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) u)
          ((Module.finBasis ℝ E) j) ((Module.finBasis ℝ E) i)) := by
  rw [anchorChartChristoffelFieldSecondSpatialFDerivFamily_apply_eq_metricThirdJetFormula]
  simp [formalProfileChristoffelSecondCoordinatesAt]

/-- On a genuine metric profile, the formal curvature array is the canonical
basis coordinate array of the existing anchor-chart curvature. -/
@[simp] theorem formalProfileCurvatureCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (u v w k : Fin (Module.finrank ℝ E)) :
    formalProfileCurvatureCoordinatesAt
        (metricEntryThirdJetProfile g) x z u v w k =
      (Module.finBasis ℝ E).coord k
        (anchorChartCurvatureFamily (fun h : G => h) x g z
          ((Module.finBasis ℝ E) u) ((Module.finBasis ℝ E) v)
          ((Module.finBasis ℝ E) w)) := by
  classical
  let b := Module.finBasis ℝ E
  let Γ := anchorChartChristoffelFieldOperatorFamily (fun h : G => h) x g
  have hFirst :
      formalProfileChristoffelFirstCoordinatesAt
          (metricEntryThirdJetProfile g) x z u w v k =
        b.coord k ((fderiv ℝ Γ z (b u)) (b v) (b w)) := by
    simpa [Γ, anchorChartChristoffelFieldSpatialFDerivFamily] using
      formalProfileChristoffelFirstCoordinate_profile_eq_field
        g x z u w v k
  have hSecond :
      formalProfileChristoffelFirstCoordinatesAt
          (metricEntryThirdJetProfile g) x z v w u k =
        b.coord k ((fderiv ℝ Γ z (b v)) (b u) (b w)) := by
    simpa [Γ, anchorChartChristoffelFieldSpatialFDerivFamily] using
      formalProfileChristoffelFirstCoordinate_profile_eq_field
        g x z v w u k
  have hThird :
      (∑ l,
        formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z w v l *
          formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z l u k) =
        b.coord k (Γ z (b u) (Γ z (b v) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelCoordinate_profile_eq_field,
      formalProfileChristoffelCoordinate_profile_eq_field]
  have hFourth :
      (∑ l,
        formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z w u l *
          formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z l v k) =
        b.coord k (Γ z (b v) (Γ z (b u) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelCoordinate_profile_eq_field,
      formalProfileChristoffelCoordinate_profile_eq_field]
  rw [formalProfileCurvatureCoordinatesAt]
  rw [hFirst, hSecond, hThird, hFourth]
  rw [← map_sub, ← map_add, ← map_sub]
  rfl

/-- On a genuine metric profile, the first formal curvature array is the
canonical-basis coordinate array of the spatial curvature derivative. -/
@[simp] theorem formalProfileCurvatureFirstCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (a u v w k : Fin (Module.finrank ℝ E)) :
    formalProfileCurvatureFirstCoordinatesAt
        (metricEntryThirdJetProfile g) x z a u v w k =
      (Module.finBasis ℝ E).coord k
        (fderiv ℝ
          (fun y : E => anchorChartCurvatureFamily
            (fun h : G => h) x g y
            ((Module.finBasis ℝ E) u) ((Module.finBasis ℝ E) v)
            ((Module.finBasis ℝ E) w)) z
          ((Module.finBasis ℝ E) a)) := by
  classical
  let b := Module.finBasis ℝ E
  let Γ := anchorChartChristoffelFieldOperatorFamily (fun h : G => h) x g
  let DΓa := fderiv ℝ Γ z (b a)
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hΓ : ContDiff ℝ 2 Γ := by
    simpa [Γ, anchorChartChristoffelFieldOperatorFamily,
      anchorChartChristoffelFieldFlow] using
      (GeodesicTransport.chartChristoffelField_contDiff_top g x).of_le
        htwo_le_top
  have hFirst :
      formalProfileChristoffelSecondCoordinatesAt
          (metricEntryThirdJetProfile g) x z a u w v k =
        b.coord k
          ((fderiv ℝ (fun y => fderiv ℝ Γ y (b u)) z (b a))
            (b v) (b w)) := by
    simpa [Γ, anchorChartChristoffelFieldSecondSpatialFDerivFamily,
      anchorChartChristoffelFieldSpatialFDerivFamily] using
      formalProfileChristoffelSecondCoordinate_profile_eq_field
        g x z a u w v k
  have hSecond :
      formalProfileChristoffelSecondCoordinatesAt
          (metricEntryThirdJetProfile g) x z a v w u k =
        b.coord k
          ((fderiv ℝ (fun y => fderiv ℝ Γ y (b v)) z (b a))
            (b u) (b w)) := by
    simpa [Γ, anchorChartChristoffelFieldSecondSpatialFDerivFamily,
      anchorChartChristoffelFieldSpatialFDerivFamily] using
      formalProfileChristoffelSecondCoordinate_profile_eq_field
        g x z a v w u k
  have hThirdA :
      (∑ l,
        formalProfileChristoffelFirstCoordinatesAt
            (metricEntryThirdJetProfile g) x z a w v l *
          formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z l u k) =
        b.coord k (Γ z (b u) (DΓa (b v) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelFirstCoordinate_profile_eq_field,
      formalProfileChristoffelCoordinate_profile_eq_field]
    rfl
  have hThirdB :
      (∑ l,
        formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z w v l *
          formalProfileChristoffelFirstCoordinatesAt
            (metricEntryThirdJetProfile g) x z a l u k) =
        b.coord k (DΓa (b u) (Γ z (b v) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelCoordinate_profile_eq_field,
      formalProfileChristoffelFirstCoordinate_profile_eq_field]
    rfl
  have hFourthA :
      (∑ l,
        formalProfileChristoffelFirstCoordinatesAt
            (metricEntryThirdJetProfile g) x z a w u l *
          formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z l v k) =
        b.coord k (Γ z (b v) (DΓa (b u) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelFirstCoordinate_profile_eq_field,
      formalProfileChristoffelCoordinate_profile_eq_field]
    rfl
  have hFourthB :
      (∑ l,
        formalProfileChristoffelCoordinatesAt
            (metricEntryThirdJetProfile g) x z w u l *
          formalProfileChristoffelFirstCoordinatesAt
            (metricEntryThirdJetProfile g) x z a l v k) =
        b.coord k (DΓa (b v) (Γ z (b u) (b w))) := by
    rw [finBasis_coord_clm_apply]
    apply Finset.sum_congr rfl
    intro l _hl
    rw [formalProfileChristoffelCoordinate_profile_eq_field,
      formalProfileChristoffelFirstCoordinate_profile_eq_field]
    rfl
  rw [formalProfileCurvatureFirstCoordinatesAt,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    hFirst, hSecond, hThirdA, hThirdB, hFourthA, hFourthB]
  change _ = b.coord k
    (fderiv ℝ (fun y => chartCurvatureOf Γ y (b u) (b v) (b w))
      z (b a))
  rw [fderiv_chartCurvatureOf_apply_component Γ hΓ]
  simp only [map_sub, map_add]
  ring

/-- Genuine profiles recover the existing anchor-chart Ricci entries. -/
@[simp] theorem formalProfileRicciCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) :
    formalProfileRicciCoordinatesAt
        (metricEntryThirdJetProfile g) x z i j =
      anchorChartRicciEntryFamily (fun h : G => h) x g z
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) := by
  rw [formalProfileRicciCoordinatesAt, anchorChartRicciEntryFamily,
    anchorChartRicciEntryFlow]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [formalProfileCurvatureCoordinatesAt_profile]
  rfl

/-- Genuine profiles recover the existing first spatial derivative of each
anchor-chart Ricci entry. -/
@[simp] theorem formalProfileRicciFirstCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) :
    formalProfileRicciFirstCoordinatesAt
        (metricEntryThirdJetProfile g) x z a i j =
      anchorChartRicciEntrySpatialFDerivFamily
        (fun h : G => h) x g z
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
        ((Module.finBasis ℝ E) a) := by
  rw [formalProfileRicciFirstCoordinatesAt,
    anchorChartRicciEntrySpatialFDerivFamily_apply_eq_basis_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [formalProfileCurvatureFirstCoordinatesAt_profile]
  rfl

/-- Genuine profiles recover the existing coordinate covariant-Ricci
entries. -/
@[simp] theorem formalProfileCovRicciCoordinatesAt_profile
    (g : G) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) :
    formalProfileCovRicciCoordinatesAt
        (metricEntryThirdJetProfile g) x z a i j =
      anchorChartCovRicciEntryFamily (fun h : G => h) x g z
        ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) i)
        ((Module.finBasis ℝ E) j) := by
  rw [formalProfileCovRicciCoordinatesAt]
  rw [formalProfileRicciFirstCoordinatesAt_profile]
  simp_rw [formalProfileChristoffelCoordinate_profile_eq_field,
    formalProfileRicciCoordinatesAt_profile]
  rfl

/-- Genuine profiles recover the existing sixfold coordinate contraction for
the squared covariant-Ricci norm. -/
@[simp] theorem formalProfileCovRicciNormSqAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileCovRicciNormSqAt (metricEntryThirdJetProfile g) x z =
      anchorChartCovRicciNormSqFamily (fun h : G => h) x g z := by
  rw [formalProfileCovRicciNormSqAt]
  simp_rw [formalProfileInverseMetricCoordinatesAt_profile,
    formalProfileCovRicciCoordinatesAt_profile]
  rfl

private theorem continuousAt_finsetSum_real
    {X ι : Type*} [TopologicalSpace X] {q : X}
    (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) q) :
    ContinuousAt (fun p => ∑ i ∈ s, f i p) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) q)
  | @insert i s hi ih =>
      have hiCont : ContinuousAt (f i) q :=
        hf i (Finset.mem_insert_self i s)
      have hsCont : ContinuousAt (fun p => ∑ j ∈ s, f j p) q :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using hiCont.add hsCont

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The first Christoffel coordinate array is continuous at every invertible
formal metric. -/
theorem continuousAt_formalProfileChristoffelFirstCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstCoordinatesAt r.1 x r.2) q := by
  rw [continuousAt_pi]
  intro a
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  rw [continuousAt_pi]
  intro k
  exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)).continuous.continuousAt.comp
    (continuousAt_formalProfileChristoffelFirstVectorAt x a i j q hq)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The second Christoffel coordinate array is continuous at every invertible
formal metric. -/
theorem continuousAt_formalProfileChristoffelSecondCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelSecondCoordinatesAt r.1 x r.2) q := by
  rw [continuousAt_pi]
  intro a
  rw [continuousAt_pi]
  intro u
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  rw [continuousAt_pi]
  intro k
  exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)).continuous.continuousAt.comp
    (continuousAt_formalProfileChristoffelSecondVectorAt x a u i j q hq)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
private theorem continuousAt_formalProfileChristoffelCoordinate
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelCoordinatesAt r.1 x r.2 i j k) q :=
  (continuous_apply k).continuousAt.comp
    ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp
        (continuousAt_formalProfileChristoffelCoordinatesAt x q hq)))

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
private theorem continuousAt_formalProfileChristoffelFirstCoordinate
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (a i j k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstCoordinatesAt r.1 x r.2 a i j k) q :=
  (continuous_apply k).continuousAt.comp
    ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp
        ((continuous_apply a).continuousAt.comp
          (continuousAt_formalProfileChristoffelFirstCoordinatesAt x q hq))))

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
private theorem continuousAt_formalProfileChristoffelSecondCoordinate
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (a u i j k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelSecondCoordinatesAt r.1 x r.2 a u i j k) q :=
  (continuous_apply k).continuousAt.comp
    ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp
        ((continuous_apply u).continuousAt.comp
          ((continuous_apply a).continuousAt.comp
            (continuousAt_formalProfileChristoffelSecondCoordinatesAt
              x q hq)))))

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every formal curvature coordinate is continuous at an invertible formal
metric. -/
theorem continuousAt_formalProfileCurvatureCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (u v w k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileCurvatureCoordinatesAt r.1 x r.2 u v w k) q := by
  have hFirst := continuousAt_formalProfileChristoffelFirstCoordinate
    x q hq u w v k
  have hSecond := continuousAt_formalProfileChristoffelFirstCoordinate
    x q hq v w u k
  have hThird : ContinuousAt (fun r : P × E =>
      ∑ l, formalProfileChristoffelCoordinatesAt r.1 x r.2 w v l *
        formalProfileChristoffelCoordinatesAt r.1 x r.2 l u k) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro l _hl
    exact (continuousAt_formalProfileChristoffelCoordinate x q hq w v l).mul
      (continuousAt_formalProfileChristoffelCoordinate x q hq l u k)
  have hFourth : ContinuousAt (fun r : P × E =>
      ∑ l, formalProfileChristoffelCoordinatesAt r.1 x r.2 w u l *
        formalProfileChristoffelCoordinatesAt r.1 x r.2 l v k) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro l _hl
    exact (continuousAt_formalProfileChristoffelCoordinate x q hq w u l).mul
      (continuousAt_formalProfileChristoffelCoordinate x q hq l v k)
  simpa [formalProfileCurvatureCoordinatesAt] using
    ((hFirst.sub hSecond).add hThird).sub hFourth

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every first formal curvature coordinate is continuous at an invertible
formal metric. -/
theorem continuousAt_formalProfileCurvatureFirstCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (a u v w k : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileCurvatureFirstCoordinatesAt r.1 x r.2 a u v w k) q := by
  have hFirst := continuousAt_formalProfileChristoffelSecondCoordinate
    x q hq a u w v k
  have hSecond := continuousAt_formalProfileChristoffelSecondCoordinate
    x q hq a v w u k
  have hThird : ContinuousAt (fun r : P × E =>
      ∑ l,
        (formalProfileChristoffelFirstCoordinatesAt r.1 x r.2 a w v l *
            formalProfileChristoffelCoordinatesAt r.1 x r.2 l u k +
          formalProfileChristoffelCoordinatesAt r.1 x r.2 w v l *
            formalProfileChristoffelFirstCoordinatesAt r.1 x r.2 a l u k)) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro l _hl
    exact
      ((continuousAt_formalProfileChristoffelFirstCoordinate x q hq a w v l).mul
        (continuousAt_formalProfileChristoffelCoordinate x q hq l u k)).add
      ((continuousAt_formalProfileChristoffelCoordinate x q hq w v l).mul
        (continuousAt_formalProfileChristoffelFirstCoordinate x q hq a l u k))
  have hFourth : ContinuousAt (fun r : P × E =>
      ∑ l,
        (formalProfileChristoffelFirstCoordinatesAt r.1 x r.2 a w u l *
            formalProfileChristoffelCoordinatesAt r.1 x r.2 l v k +
          formalProfileChristoffelCoordinatesAt r.1 x r.2 w u l *
            formalProfileChristoffelFirstCoordinatesAt r.1 x r.2 a l v k)) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro l _hl
    exact
      ((continuousAt_formalProfileChristoffelFirstCoordinate x q hq a w u l).mul
        (continuousAt_formalProfileChristoffelCoordinate x q hq l v k)).add
      ((continuousAt_formalProfileChristoffelCoordinate x q hq w u l).mul
        (continuousAt_formalProfileChristoffelFirstCoordinate x q hq a l v k))
  simpa [formalProfileCurvatureFirstCoordinatesAt] using
    ((hFirst.sub hSecond).add hThird).sub hFourth

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every formal Ricci coordinate is continuous at an invertible formal
metric. -/
theorem continuousAt_formalProfileRicciCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileRicciCoordinatesAt r.1 x r.2 i j) q := by
  unfold formalProfileRicciCoordinatesAt
  apply continuousAt_finsetSum_real Finset.univ
  intro r _hr
  exact continuousAt_formalProfileCurvatureCoordinatesAt x q hq r i j r

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every first formal Ricci coordinate is continuous at an invertible formal
metric. -/
theorem continuousAt_formalProfileRicciFirstCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (a i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileRicciFirstCoordinatesAt r.1 x r.2 a i j) q := by
  unfold formalProfileRicciFirstCoordinatesAt
  apply continuousAt_finsetSum_real Finset.univ
  intro r _hr
  exact continuousAt_formalProfileCurvatureFirstCoordinatesAt
    x q hq a r i j r

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every formal covariant-Ricci coordinate is continuous at an invertible
formal metric. -/
theorem continuousAt_formalProfileCovRicciCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (a i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileCovRicciCoordinatesAt r.1 x r.2 a i j) q := by
  have hFirst := continuousAt_formalProfileRicciFirstCoordinatesAt
    x q hq a i j
  have hSecond : ContinuousAt (fun r : P × E =>
      ∑ s, formalProfileChristoffelCoordinatesAt r.1 x r.2 a i s *
        formalProfileRicciCoordinatesAt r.1 x r.2 s j) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro s _hs
    exact (continuousAt_formalProfileChristoffelCoordinate x q hq a i s).mul
      (continuousAt_formalProfileRicciCoordinatesAt x q hq s j)
  have hThird : ContinuousAt (fun r : P × E =>
      ∑ s, formalProfileChristoffelCoordinatesAt r.1 x r.2 a j s *
        formalProfileRicciCoordinatesAt r.1 x r.2 i s) q := by
    apply continuousAt_finsetSum_real Finset.univ
    intro s _hs
    exact (continuousAt_formalProfileChristoffelCoordinate x q hq a j s).mul
      (continuousAt_formalProfileRicciCoordinatesAt x q hq i s)
  simpa [formalProfileCovRicciCoordinatesAt] using
    (hFirst.sub hSecond).sub hThird

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Every inverse formal-metric coefficient is continuous at an invertible
formal metric. -/
theorem continuousAt_formalProfileInverseMetricCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun r : P × E =>
      formalProfileInverseMetricCoordinatesAt r.1 x r.2 i j) q := by
  have hInv : ContinuousAt
      (fun r : P × E => (formalProfileMetricAt r.1 x r.2).inverse) q := by
    simpa [Function.comp_def] using
      ((hq.contDiffAt_map_inverse (n := 0)).continuousAt).comp_of_eq
        (continuous_formalProfileMetricAt x).continuousAt rfl
  exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord j)).continuous.continuousAt.comp
    (hInv.clm_apply continuousAt_const)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The complete formal covariant-Ricci norm contraction is continuous at
every invertible formal metric. -/
theorem continuousAt_formalProfileCovRicciNormSqAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileCovRicciNormSqAt r.1 x r.2) q := by
  unfold formalProfileCovRicciNormSqAt
  apply continuousAt_finsetSum_real Finset.univ
  intro a _ha
  apply continuousAt_finsetSum_real Finset.univ
  intro i _hi
  apply continuousAt_finsetSum_real Finset.univ
  intro j _hj
  apply continuousAt_finsetSum_real Finset.univ
  intro b _hb
  apply continuousAt_finsetSum_real Finset.univ
  intro k _hk
  apply continuousAt_finsetSum_real Finset.univ
  intro l _hl
  exact
    (((continuousAt_formalProfileInverseMetricCoordinatesAt x q hq a b).mul
      (continuousAt_formalProfileInverseMetricCoordinatesAt x q hq i k)).mul
      (continuousAt_formalProfileInverseMetricCoordinatesAt x q hq j l)).mul
      (continuousAt_formalProfileCovRicciCoordinatesAt x q hq b k l) |>.mul
      (continuousAt_formalProfileCovRicciCoordinatesAt x q hq a i j)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The formal covariant-Ricci contraction is continuous on a set where every
reconstructed metric is invertible. -/
theorem continuousOn_formalProfileCovRicciNormSqAt_of_invertible
    (x : M) {S : Set P} {Q : Set E}
    (hnd : ∀ p ∈ S, ∀ z ∈ Q, (formalProfileMetricAt p x z).IsInvertible) :
    ContinuousOn (fun q : P × E =>
      formalProfileCovRicciNormSqAt q.1 x q.2) (S ×ˢ Q) := by
  intro q hq
  exact (continuousAt_formalProfileCovRicciNormSqAt x q
    (hnd q.1 hq.1 q.2 hq.2)).continuousWithinAt

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Compact formal-profile and coordinate sets have compact covariant-Ricci
contraction image when the formal metric stays invertible. -/
theorem isCompact_formalProfileCovRicciNormSqAt_image
    (x : M) {S : Set P} {Q : Set E}
    (hS : IsCompact S) (hQ : IsCompact Q)
    (hnd : ∀ p ∈ S, ∀ z ∈ Q, (formalProfileMetricAt p x z).IsInvertible) :
    IsCompact ((fun q : P × E =>
      formalProfileCovRicciNormSqAt q.1 x q.2) '' (S ×ˢ Q)) :=
  (hS.prod hQ).image_of_continuousOn
    (continuousOn_formalProfileCovRicciNormSqAt_of_invertible x hnd)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Compactness and invertibility give one real upper bound for the formal
covariant-Ricci contraction on the full product set. -/
theorem exists_uniformFormalProfileCovRicciNormSqBound
    (x : M) {S : Set P} {Q : Set E}
    (hS : IsCompact S) (hQ : IsCompact Q)
    (hnd : ∀ p ∈ S, ∀ z ∈ Q, (formalProfileMetricAt p x z).IsInvertible) :
    ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ Q,
      formalProfileCovRicciNormSqAt p x z ≤ C := by
  have hCompact :=
    isCompact_formalProfileCovRicciNormSqAt_image x hS hQ hnd
  rcases bddAbove_def.mp hCompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro p hp z hz
  exact hC _ ⟨(p, z), ⟨hp, hz⟩, rfl⟩

/-- A compact scalar-profile closure yields a uniform bound for the genuine
metric family's fixed-chart covariant-Ricci contraction.  Unlike the earlier
orbit-compactness route, no profile limit must be realized by a smooth metric;
only invertibility of the reconstructed formal metrics on the chosen compact
coordinate set is required. -/
theorem exists_uniformAnchorChartCovRicciNormSqFamilyBound_of_compact_profileClosure
    {J : Type*} (gt : J → G) (x : M) {Q : Set E}
    (hProfileCompact : IsCompact
      (closure (Set.range
        (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))))
    (hQ : IsCompact Q)
    (hnd : ∀ p ∈ closure (Set.range
        (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)),
      ∀ z ∈ Q, (formalProfileMetricAt p x z).IsInvertible) :
    ∃ C : ℝ, ∀ t : J, ∀ z ∈ Q,
      anchorChartCovRicciNormSqFamily gt x t z ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniformFormalProfileCovRicciNormSqBound x
      hProfileCompact hQ hnd
  refine ⟨C, ?_⟩
  intro t z hz
  have ht : metricEntryThirdJetProfile (gt t) ∈
      closure (Set.range
        (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)) :=
    subset_closure ⟨t, rfl⟩
  simpa using hC (metricEntryThirdJetProfile (gt t)) ht z hz

end Poincare
