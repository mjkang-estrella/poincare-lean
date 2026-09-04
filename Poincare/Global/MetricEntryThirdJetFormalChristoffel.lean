import Poincare.Global.MetricEntryThirdJetFormalRawCoordinates

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

/-- The Koszul covector for two canonical basis directions, reconstructed
from the raw first-coordinate array of a formal profile. -/
noncomputable def formalProfileChristoffelCovectorAt
    (p : P) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ k, ((1 / 2 : ℝ) *
      (formalProfileMetricFirstJetCoordinatesAt p x z i j k +
       formalProfileMetricFirstJetCoordinatesAt p x z j i k -
       formalProfileMetricFirstJetCoordinatesAt p x z k i j)) •
    LinearMap.toContinuousLinearMap (b.coord k)

/-- Formal Christoffel vector in two canonical basis directions.  The
definition is meaningful for every profile; invertibility is required for
its continuity and geometric interpretation. -/
noncomputable def formalProfileChristoffelVectorAt
    (p : P) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) : E :=
  (formalProfileMetricAt p x z).inverse
    (formalProfileChristoffelCovectorAt p x z i j)

/-- Coordinate array of the formal Christoffel vector. -/
noncomputable def formalProfileChristoffelCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun i j k => b.coord k (formalProfileChristoffelVectorAt p x z i j)

/-- The bilinear metric derivative in one canonical direction, reconstructed
from a formal profile's raw first-coordinate array. -/
noncomputable def formalProfileMetricFirstDirectionAt
    (p : P) (x : M) (z : E)
    (a : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, ∑ j,
    formalProfileMetricFirstJetCoordinatesAt p x z a i j •
      (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
        (LinearMap.toContinuousLinearMap (b.coord j))

/-- The Koszul covector of the directional metric derivative in one
canonical direction, reconstructed from raw second-coordinate entries. -/
noncomputable def formalProfileChristoffelFirstCovectorAt
    (p : P) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ k, ((1 / 2 : ℝ) *
      (formalProfileMetricSecondJetCoordinatesAt p x z a i j k +
       formalProfileMetricSecondJetCoordinatesAt p x z a j i k -
       formalProfileMetricSecondJetCoordinatesAt p x z a k i j)) •
    LinearMap.toContinuousLinearMap (b.coord k)

/-- The first spatial Christoffel jet in canonical directions, written as
the rational metric-jet formula `δΓ`. -/
noncomputable def formalProfileChristoffelFirstVectorAt
    (p : P) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) : E :=
  let A := (formalProfileMetricAt p x z).inverse
  let H := formalProfileMetricFirstDirectionAt p x z a
  let KG := formalProfileChristoffelCovectorAt p x z i j
  let KH := formalProfileChristoffelFirstCovectorAt p x z a i j
  (-(A.comp (H.comp A))) KG + A KH

/-- The bilinear second metric derivative in two ordered canonical
directions, reconstructed from a formal profile's raw array. -/
noncomputable def formalProfileMetricSecondDirectionsAt
    (p : P) (x : M) (z : E)
    (u a : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, ∑ j,
    formalProfileMetricSecondJetCoordinatesAt p x z u a i j •
      (LinearMap.toContinuousLinearMap (b.coord i)).smulRight
        (LinearMap.toContinuousLinearMap (b.coord j))

/-- The Koszul covector made from the ordered third metric jet. -/
noncomputable def formalProfileChristoffelSecondCovectorAt
    (p : P) (x : M) (z : E)
    (u a i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  let b := Module.finBasis ℝ E
  ∑ k, ((1 / 2 : ℝ) *
      (formalProfileMetricThirdJetCoordinatesAt p x z u a i j k +
       formalProfileMetricThirdJetCoordinatesAt p x z u a j i k -
       formalProfileMetricThirdJetCoordinatesAt p x z u a k i j)) •
    LinearMap.toContinuousLinearMap (b.coord k)

/-- The second spatial Christoffel jet in ordered canonical directions,
written entirely in terms of the inverse metric and raw metric jets through
order three. -/
noncomputable def formalProfileChristoffelSecondVectorAt
    (p : P) (x : M) (z : E)
    (a u i j : Fin (Module.finrank ℝ E)) : E :=
  let A := (formalProfileMetricAt p x z).inverse
  let H := formalProfileMetricFirstDirectionAt p x z u
  let Ha := formalProfileMetricFirstDirectionAt p x z a
  let J := formalProfileMetricSecondDirectionsAt p x z u a
  let KG := formalProfileChristoffelCovectorAt p x z i j
  let KH := formalProfileChristoffelFirstCovectorAt p x z u i j
  let KJ := formalProfileChristoffelSecondCovectorAt p x z u a i j
  let dGammaG := formalProfileChristoffelFirstVectorAt p x z a i j
  let gammaG := A KG
  let psi := H gammaG
  let dpsi := J gammaG + H dGammaG
  (-(A dpsi - A (Ha (A psi))) + A KJ - A (Ha (A KH)))

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuous_formalProfileChristoffelCovectorAt
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun q : P × E =>
      formalProfileChristoffelCovectorAt q.1 x q.2 i j) := by
  unfold formalProfileChristoffelCovectorAt
  apply continuous_finsetSum Finset.univ
  intro k hk
  apply Continuous.smul
  · have h := continuous_formalProfileMetricFirstJetCoordinatesAt (n := n) x
    have hijk := (continuous_apply k).comp
      ((continuous_apply j).comp ((continuous_apply i).comp h))
    have hjik := (continuous_apply k).comp
      ((continuous_apply i).comp ((continuous_apply j).comp h))
    have hkij := (continuous_apply j).comp
      ((continuous_apply i).comp ((continuous_apply k).comp h))
    exact ((hijk.add hjik).sub hkij).const_mul
        (1 / 2 : ℝ)
  · exact continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuous_formalProfileMetricFirstDirectionAt
    (x : M) (a : Fin (Module.finrank ℝ E)) :
    Continuous (fun q : P × E =>
      formalProfileMetricFirstDirectionAt q.1 x q.2 a) := by
  unfold formalProfileMetricFirstDirectionAt
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply continuous_finsetSum Finset.univ
  intro j hj
  apply Continuous.smul
  · have h := continuous_formalProfileMetricFirstJetCoordinatesAt (n := n) x
    exact (continuous_apply j).comp
      ((continuous_apply i).comp ((continuous_apply a).comp h))
  · exact continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuous_formalProfileChristoffelFirstCovectorAt
    (x : M) (a i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun q : P × E =>
      formalProfileChristoffelFirstCovectorAt q.1 x q.2 a i j) := by
  unfold formalProfileChristoffelFirstCovectorAt
  apply continuous_finsetSum Finset.univ
  intro k hk
  apply Continuous.smul
  · have h := continuous_formalProfileMetricSecondJetCoordinatesAt (n := n) x
    have haijk := (continuous_apply k).comp ((continuous_apply j).comp
      ((continuous_apply i).comp ((continuous_apply a).comp h)))
    have hajik := (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply j).comp ((continuous_apply a).comp h)))
    have hakij := (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply k).comp ((continuous_apply a).comp h)))
    exact ((haijk.add hajik).sub hakij).const_mul (1 / 2 : ℝ)
  · exact continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuous_formalProfileMetricSecondDirectionsAt
    (x : M) (u a : Fin (Module.finrank ℝ E)) :
    Continuous (fun q : P × E =>
      formalProfileMetricSecondDirectionsAt q.1 x q.2 u a) := by
  unfold formalProfileMetricSecondDirectionsAt
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply continuous_finsetSum Finset.univ
  intro j hj
  apply Continuous.smul
  · have h := continuous_formalProfileMetricSecondJetCoordinatesAt (n := n) x
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply a).comp ((continuous_apply u).comp h)))
  · exact continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuous_formalProfileChristoffelSecondCovectorAt
    (x : M) (u a i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun q : P × E =>
      formalProfileChristoffelSecondCovectorAt q.1 x q.2 u a i j) := by
  unfold formalProfileChristoffelSecondCovectorAt
  apply continuous_finsetSum Finset.univ
  intro k hk
  apply Continuous.smul
  · have h := continuous_formalProfileMetricThirdJetCoordinatesAt (n := n) x
    have huaijk := (continuous_apply k).comp ((continuous_apply j).comp
      ((continuous_apply i).comp ((continuous_apply a).comp
        ((continuous_apply u).comp h))))
    have huajik := (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply j).comp ((continuous_apply a).comp
        ((continuous_apply u).comp h))))
    have huakij := (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply k).comp ((continuous_apply a).comp
        ((continuous_apply u).comp h))))
    exact ((huaijk.add huajik).sub huakij).const_mul (1 / 2 : ℝ)
  · exact continuous_const

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuousAt_formalProfileChristoffelVectorAt
    (x : M) (i j : Fin (Module.finrank ℝ E)) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelVectorAt r.1 x r.2 i j) q := by
  have hInv : ContinuousAt
      (fun r : P × E => (formalProfileMetricAt r.1 x r.2).inverse) q := by
    simpa [Function.comp_def] using
      ((hq.contDiffAt_map_inverse (n := 0)).continuousAt).comp_of_eq
        (continuous_formalProfileMetricAt x).continuousAt rfl
  exact hInv.clm_apply
    (continuous_formalProfileChristoffelCovectorAt x i j).continuousAt

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuousAt_formalProfileChristoffelCoordinatesAt
    (x : M) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelCoordinatesAt r.1 x r.2) q := by
  rw [continuousAt_pi]
  intro i
  rw [continuousAt_pi]
  intro j
  rw [continuousAt_pi]
  intro k
  exact (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord k)).continuous.continuousAt.comp
    (continuousAt_formalProfileChristoffelVectorAt x i j q hq)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuousAt_formalProfileChristoffelFirstVectorAt
    (x : M) (a i j : Fin (Module.finrank ℝ E)) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstVectorAt r.1 x r.2 a i j) q := by
  have hA : ContinuousAt
      (fun r : P × E => (formalProfileMetricAt r.1 x r.2).inverse) q := by
    simpa [Function.comp_def] using
      ((hq.contDiffAt_map_inverse (n := 0)).continuousAt).comp_of_eq
        (continuous_formalProfileMetricAt x).continuousAt rfl
  have hH : ContinuousAt (fun r : P × E =>
      formalProfileMetricFirstDirectionAt r.1 x r.2 a) q :=
    (continuous_formalProfileMetricFirstDirectionAt x a).continuousAt
  have hKG : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelCovectorAt r.1 x r.2 i j) q :=
    (continuous_formalProfileChristoffelCovectorAt x i j).continuousAt
  have hKH : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstCovectorAt r.1 x r.2 a i j) q :=
    (continuous_formalProfileChristoffelFirstCovectorAt x a i j).continuousAt
  exact ((hA.clm_comp (hH.clm_comp hA)).neg.clm_apply hKG).add
    (hA.clm_apply hKH)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
theorem continuousAt_formalProfileChristoffelSecondVectorAt
    (x : M) (a u i j : Fin (Module.finrank ℝ E)) (q : P × E)
    (hq : (formalProfileMetricAt q.1 x q.2).IsInvertible) :
    ContinuousAt (fun r : P × E =>
      formalProfileChristoffelSecondVectorAt r.1 x r.2 a u i j) q := by
  have hA : ContinuousAt
      (fun r : P × E => (formalProfileMetricAt r.1 x r.2).inverse) q := by
    simpa [Function.comp_def] using
      ((hq.contDiffAt_map_inverse (n := 0)).continuousAt).comp_of_eq
        (continuous_formalProfileMetricAt x).continuousAt rfl
  have hH : ContinuousAt (fun r : P × E =>
      formalProfileMetricFirstDirectionAt r.1 x r.2 u) q :=
    (continuous_formalProfileMetricFirstDirectionAt x u).continuousAt
  have hHa : ContinuousAt (fun r : P × E =>
      formalProfileMetricFirstDirectionAt r.1 x r.2 a) q :=
    (continuous_formalProfileMetricFirstDirectionAt x a).continuousAt
  have hJ : ContinuousAt (fun r : P × E =>
      formalProfileMetricSecondDirectionsAt r.1 x r.2 u a) q :=
    (continuous_formalProfileMetricSecondDirectionsAt x u a).continuousAt
  have hKG : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelCovectorAt r.1 x r.2 i j) q :=
    (continuous_formalProfileChristoffelCovectorAt x i j).continuousAt
  have hKH : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstCovectorAt r.1 x r.2 u i j) q :=
    (continuous_formalProfileChristoffelFirstCovectorAt x u i j).continuousAt
  have hKJ : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelSecondCovectorAt r.1 x r.2 u a i j) q :=
    (continuous_formalProfileChristoffelSecondCovectorAt x u a i j).continuousAt
  have hdGamma : ContinuousAt (fun r : P × E =>
      formalProfileChristoffelFirstVectorAt r.1 x r.2 a i j) q :=
    continuousAt_formalProfileChristoffelFirstVectorAt x a i j q hq
  have hgamma := hA.clm_apply hKG
  have hpsi := hH.clm_apply hgamma
  have hdpsi := (hJ.clm_apply hgamma).add (hH.clm_apply hdGamma)
  have hApsi := hA.clm_apply hpsi
  have hAKH := hA.clm_apply hKH
  exact ((hA.clm_apply hdpsi).sub
      (hA.clm_apply (hHa.clm_apply hApsi))).neg.add
      (hA.clm_apply hKJ) |>.sub
      (hA.clm_apply (hHa.clm_apply hAKH))

@[simp] theorem formalProfileChristoffelCovectorAt_profile
    (g : G) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelCovectorAt
        (metricEntryThirdJetProfile g) x z i j =
      LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional
          (anchorBlendedMetricFamily (fun h : G => h) x g) z
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  let b := Module.finBasis ℝ E
  let A := anchorBlendedMetricFamily (fun h : G => h) x g
  have hlin :
      (formalProfileChristoffelCovectorAt
        (metricEntryThirdJetProfile g) x z i j).toLinearMap =
      (LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional A z (b i) (b j))).toLinearMap := by
    apply Module.Basis.ext b
    intro k
    simp [formalProfileChristoffelCovectorAt,
      formalProfileMetricFirstJetCoordinatesAt_profile,
      CovariantDerivative.christoffelFunctional, b, A]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' hk' hne
      simp [hne]
    · simp
  apply ContinuousLinearMap.ext
  intro w
  exact DFunLike.congr_fun hlin w

@[simp] theorem formalProfileChristoffelVectorAt_profile
    (g : G) (x : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelVectorAt
        (metricEntryThirdJetProfile g) x z i j =
      RicciFlow.RicciFlow.christoffelClosedOp
        (anchorBlendedMetricFamily (fun h : G => h) x g) z
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) := by
  simp [formalProfileChristoffelVectorAt,
    RicciFlow.RicciFlow.christoffelClosedOp_apply]

@[simp] theorem formalProfileMetricFirstDirectionAt_profile
    (g : G) (x : M) (z : E)
    (a : Fin (Module.finrank ℝ E)) :
    formalProfileMetricFirstDirectionAt
        (metricEntryThirdJetProfile g) x z a =
      fderiv ℝ (anchorBlendedMetricFamily (fun h : G => h) x g) z
        ((Module.finBasis ℝ E) a) := by
  let b := Module.finBasis ℝ E
  let A := fderiv ℝ
    (anchorBlendedMetricFamily (fun h : G => h) x g) z (b a)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp [formalProfileMetricFirstDirectionAt,
    formalProfileMetricFirstJetCoordinatesAt_profile]
  change ∑ i, ∑ j, A (b i) (b j) * (b.coord i u * b.coord j v) = A u v
  calc
    _ = ∑ i, b.coord i u * (∑ j, b.coord j v * A (b i) (b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, b.coord i u * A (b i) v := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      conv_rhs => rw [← b.sum_repr v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, smul_eq_mul, Module.Basis.coord_apply]
    _ = A u v := by
      conv_rhs => rw [← b.sum_repr u]
      rw [map_sum, ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Module.Basis.coord_apply]

@[simp] theorem formalProfileChristoffelFirstCovectorAt_profile
    (g : G) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelFirstCovectorAt
        (metricEntryThirdJetProfile g) x z a i j =
      LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional
          (fun y => fderiv ℝ
            (anchorBlendedMetricFamily (fun h : G => h) x g) y
              ((Module.finBasis ℝ E) a)) z
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  let b := Module.finBasis ℝ E
  let H := fun y => fderiv ℝ
    (anchorBlendedMetricFamily (fun h : G => h) x g) y (b a)
  have hlin :
      (formalProfileChristoffelFirstCovectorAt
        (metricEntryThirdJetProfile g) x z a i j).toLinearMap =
      (LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional H z (b i) (b j))).toLinearMap := by
    apply Module.Basis.ext b
    intro k
    simp [formalProfileChristoffelFirstCovectorAt,
      formalProfileMetricSecondJetCoordinatesAt_profile,
      CovariantDerivative.christoffelFunctional, b, H]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' hk' hne
      simp [hne]
    · simp
  apply ContinuousLinearMap.ext
  intro w
  exact DFunLike.congr_fun hlin w

@[simp] theorem formalProfileChristoffelFirstVectorAt_profile
    (g : G) (x : M) (z : E)
    (a i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelFirstVectorAt
        (metricEntryThirdJetProfile g) x z a i j =
      RicciFlow.christoffelDeriv
        (anchorBlendedMetricFamily (fun h : G => h) x g)
        (fun y => fderiv ℝ
          (anchorBlendedMetricFamily (fun h : G => h) x g) y
            ((Module.finBasis ℝ E) a)) z
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) := by
  simp [formalProfileChristoffelFirstVectorAt,
    RicciFlow.christoffelDeriv]

@[simp] theorem formalProfileMetricSecondDirectionsAt_profile
    (g : G) (x : M) (z : E)
    (u a : Fin (Module.finrank ℝ E)) :
    formalProfileMetricSecondDirectionsAt
        (metricEntryThirdJetProfile g) x z u a =
      fderiv ℝ
        (fun y => fderiv ℝ
          (anchorBlendedMetricFamily (fun h : G => h) x g) y
            ((Module.finBasis ℝ E) u)) z
        ((Module.finBasis ℝ E) a) := by
  let b := Module.finBasis ℝ E
  let A := fderiv ℝ
    (fun y => fderiv ℝ
      (anchorBlendedMetricFamily (fun h : G => h) x g) y (b u)) z (b a)
  apply ContinuousLinearMap.ext
  intro s
  apply ContinuousLinearMap.ext
  intro t
  simp [formalProfileMetricSecondDirectionsAt,
    formalProfileMetricSecondJetCoordinatesAt_profile]
  change ∑ i, ∑ j, A (b i) (b j) * (b.coord i s * b.coord j t) = A s t
  calc
    _ = ∑ i, b.coord i s * (∑ j, b.coord j t * A (b i) (b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, b.coord i s * A (b i) t := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      conv_rhs => rw [← b.sum_repr t]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, smul_eq_mul, Module.Basis.coord_apply]
    _ = A s t := by
      conv_rhs => rw [← b.sum_repr s]
      rw [map_sum, ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        Module.Basis.coord_apply]

@[simp] theorem formalProfileChristoffelSecondCovectorAt_profile
    (g : G) (x : M) (z : E)
    (u a i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelSecondCovectorAt
        (metricEntryThirdJetProfile g) x z u a i j =
      LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional
          (fun y => fderiv ℝ
            (fun w => fderiv ℝ
              (anchorBlendedMetricFamily (fun h : G => h) x g) w
                ((Module.finBasis ℝ E) u)) y
              ((Module.finBasis ℝ E) a)) z
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  let b := Module.finBasis ℝ E
  let J := fun y => fderiv ℝ
    (fun w => fderiv ℝ
      (anchorBlendedMetricFamily (fun h : G => h) x g) w (b u)) y (b a)
  have hlin :
      (formalProfileChristoffelSecondCovectorAt
        (metricEntryThirdJetProfile g) x z u a i j).toLinearMap =
      (LinearMap.toContinuousLinearMap
        (CovariantDerivative.christoffelFunctional J z (b i) (b j))).toLinearMap := by
    apply Module.Basis.ext b
    intro k
    simp [formalProfileChristoffelSecondCovectorAt,
      formalProfileMetricThirdJetCoordinatesAt_profile,
      CovariantDerivative.christoffelFunctional, b, J]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' hk' hne
      simp [hne]
    · simp
  apply ContinuousLinearMap.ext
  intro w
  exact DFunLike.congr_fun hlin w

@[simp] theorem formalProfileChristoffelSecondVectorAt_profile
    (g : G) (x : M) (z : E)
    (a u i j : Fin (Module.finrank ℝ E)) :
    formalProfileChristoffelSecondVectorAt
        (metricEntryThirdJetProfile g) x z a u i j =
      christoffelSecondFormula
        (anchorBlendedMetricFamily (fun h : G => h) x g) z
        ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) u)
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) := by
  simp [formalProfileChristoffelSecondVectorAt,
    christoffelSecondFormula, RicciFlow.christoffelDeriv]

@[simp] theorem formalProfileChristoffelCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileChristoffelCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun i j k => (Module.finBasis ℝ E).coord k
        (RicciFlow.RicciFlow.christoffelClosedOp
          (anchorBlendedMetricFamily (fun h : G => h) x g) z
          ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)) := by
  funext i j k
  simp [formalProfileChristoffelCoordinatesAt]


end Poincare
