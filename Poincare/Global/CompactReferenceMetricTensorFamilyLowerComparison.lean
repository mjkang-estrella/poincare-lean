import Poincare.Global.ContinuousWithDensityOrder
import Poincare.Global.HausdorffInverseChartAreaFormula
import Poincare.Global.HausdorffLinearPullbackAreaFormula
import Poincare.Global.MetricEntryThirdJetProfileLimitAlgebra
import Poincare.Global.NormalizedFlowFiniteTimeCurvatureCompactness
import Mathlib.Analysis.Matrix.PosDef

/-!
# Metric lower bounds from compact tensor control

The volume comparison stored by `CompactReferenceMetricTensorFamilyData` is
an inequality for all measurable subsets of the manifold.  The inverse-chart
area formula turns it into domination between two coordinate measures with
continuous densities.  Full support of coordinate Lebesgue measure then
recovers the pointwise density inequality.  In dimension three, an eigenvalue
argument combines that determinant lower bound with the stored quadratic-form
upper bound.  Compactness makes both comparison factors uniform, producing a
uniform positive lower comparison for the whole metric family.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Topology
open scoped ENNReal Manifold MeasureTheory NNReal Topology
  ComplexOrder

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3)
  ((⊤ : ℕ∞) : WithTop ℕ∞) M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

/-- A real-valued lower comparison on every measurable set gives the
corresponding order between finite measures. -/
theorem ennreal_smul_measure_le_of_measureReal_mul_le
    {X : Type*} [MeasurableSpace X] (mu nu : Measure X)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ A : Set X, MeasurableSet A → c * mu.real A ≤ nu.real A) :
    ENNReal.ofReal c • mu ≤ nu := by
  rw [Measure.le_iff]
  intro A hA
  have hleft : (ENNReal.ofReal c • mu) A ≠ ⊤ := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top mu A)
  have hright : nu A ≠ ⊤ := measure_ne_top nu A
  apply (ENNReal.toReal_le_toReal hleft hright).mp
  change (ENNReal.ofReal c • mu).real A ≤ nu.real A
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]
  exact h A hA

/-- A lower comparison of manifold volume measures gives the same
comparison between the raw coordinate-density measures in every inverse
extended chart. -/
theorem inverseChart_rawHausdorffCoordinateDensityMeasure_lower
    (gref g : ClosedSmoothRiemannianMetric 3 M) {c : ℝ} (hc : 0 ≤ c)
    (hvolume : ∀ A : Set M, MeasurableSet A →
      c * (volumeMeasure gref).real A ≤ (volumeMeasure g).real A)
    (x₀ : M) :
    ENNReal.ofReal c •
        rawHausdorffCoordinateDensityMeasure (extChartAt I x₀).target
          (inverseChartPullbackVolumeDensity gref x₀) ≤
      rawHausdorffCoordinateDensityMeasure (extChartAt I x₀).target
        (inverseChartPullbackVolumeDensity g x₀) := by
  let U : Set E := (extChartAt I x₀).target
  let psi : U → M :=
    inverseExtendedChartParametrization (n := 3) (M := M) x₀
  let V : Set M := Set.range psi
  let muref : Measure M := volumeMeasure gref
  let mug : Measure M := volumeMeasure g
  let rref : Measure U :=
    rawHausdorffCoordinateDensityMeasure U
      (inverseChartPullbackVolumeDensity gref x₀)
  let rg : Measure U :=
    rawHausdorffCoordinateDensityMeasure U
      (inverseChartPullbackVolumeDensity g x₀)
  letI : IsFiniteMeasure muref := volumeMeasure_isFiniteMeasure gref
  letI : IsFiniteMeasure mug := volumeMeasure_isFiniteMeasure g
  have hglobal : ENNReal.ofReal c • muref ≤ mug :=
    ennreal_smul_measure_le_of_measureReal_mul_le muref mug hc hvolume
  have hpsiTop : IsEmbedding psi :=
    inverseExtendedChartParametrization_isEmbedding
      (n := 3) (M := M) x₀
  have hpsi : MeasurableEmbedding psi := by
    apply hpsiTop.measurableEmbedding
    rw [show Set.range psi = (extChartAt I x₀).source by
      exact range_inverseExtendedChartParametrization x₀]
    exact (isOpen_extChartAt_source x₀).measurableSet
  have href : Measure.map psi rref = muref.restrict V := by
    simpa only [U, psi, V, muref, rref] using
      inverseChart_hausdorffChartDensityEquality gref x₀
  have hg : Measure.map psi rg = mug.restrict V := by
    simpa only [U, psi, V, mug, rg] using
      inverseChart_hausdorffChartDensityEquality g x₀
  apply measure_le_of_map_le_map_of_measurableEmbedding hpsi
  calc
    Measure.map psi (ENNReal.ofReal c • rref) =
        ENNReal.ofReal c • Measure.map psi rref := by
      ext A
      rw [hpsi.map_apply]
      simp only [Measure.smul_apply, smul_eq_mul]
      rw [hpsi.map_apply]
    _ = (ENNReal.ofReal c • muref).restrict V := by
      rw [href, Measure.restrict_smul]
    _ ≤ mug.restrict V := Measure.restrict_mono_measure hglobal V
    _ = Measure.map psi rg := hg.symm

/-- A measurable-set volume lower comparison is pointwise the corresponding
inverse-chart volume-density lower comparison. -/
theorem inverseChartPullbackVolumeDensity_lower_of_volumeMeasureReal_lower
    (gref g : ClosedSmoothRiemannianMetric 3 M) {c : ℝ} (hc : 0 ≤ c)
    (hvolume : ∀ A : Set M, MeasurableSet A →
      c * (volumeMeasure gref).real A ≤ (volumeMeasure g).real A)
    (x₀ : M) (z : (extChartAt I x₀).target) :
    c * inverseChartPullbackVolumeDensity gref x₀ z ≤
      inverseChartPullbackVolumeDensity g x₀ z := by
  let U : Set E := (extChartAt I x₀).target
  let lambda : Measure U := coordinateLebesgueMeasure U
  let scale : ℝ := rawHausdorffLebesgueScale 3
  let dref : U → ℝ := inverseChartPullbackVolumeDensity gref x₀
  let dg : U → ℝ := inverseChartPullbackVolumeDensity g x₀
  let fref : U → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (scale * dref w)
  let fg : U → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (scale * dg w)
  have hUopen : IsOpen U := isOpen_extChartAt_target x₀
  letI : LocallyCompactSpace U := hUopen.locallyCompactSpace
  letI : IsFiniteMeasureOnCompacts lambda :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hUopen.measurableSet)
  letI : IsLocallyFiniteMeasure lambda :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  letI : SigmaFinite lambda := sigmaFinite_of_locallyFinite
  letI : lambda.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume
      hUopen.isOpenEmbedding_subtypeVal
  have hdref : Continuous dref := by
    simpa only [dref, U] using
      continuous_inverseChartPullbackVolumeDensity gref x₀
  have hdg : Continuous dg := by
    simpa only [dg, U] using
      continuous_inverseChartPullbackVolumeDensity g x₀
  have hfref : Continuous fref := by
    exact ENNReal.continuous_ofReal.comp (continuous_const.mul hdref)
  have hfg : Continuous fg := by
    exact ENNReal.continuous_ofReal.comp (continuous_const.mul hdg)
  have hraw :=
    inverseChart_rawHausdorffCoordinateDensityMeasure_lower
      gref g hc hvolume x₀
  have hdensityMeasure : lambda.withDensity (ENNReal.ofReal c • fref) ≤
      lambda.withDensity fg := by
    rw [withDensity_smul' (ENNReal.ofReal c) fref ENNReal.ofReal_ne_top]
    simpa only [rawHausdorffCoordinateDensityMeasure, lambda, fref, fg,
      scale, dref, dg, U] using hraw
  have hleft : Continuous (ENNReal.ofReal c • fref) := by
    change Continuous (fun w ↦ ENNReal.ofReal c * fref w)
    exact
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hfref
  have hpoint :=
    continuous_density_le_of_withDensity_le lambda
      hleft hfg hdensityMeasure z
  have hscale : 0 < scale := by
    dsimp only [scale, rawHausdorffLebesgueScale]
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (μH[(Module.finrank ℝ E : ℝ)] : Measure E)
      (volume : Measure E)
  have hrefnonneg : 0 ≤ dref z :=
    (inverseChartPullbackVolumeDensity_pos gref x₀ z).le
  have hgnonneg : 0 ≤ dg z :=
    (inverseChartPullbackVolumeDensity_pos g x₀ z).le
  change ENNReal.ofReal c * fref z ≤ fg z at hpoint
  rw [show ENNReal.ofReal c * fref z =
      ENNReal.ofReal (c * (scale * dref z)) by
    simp only [fref]
    rw [ENNReal.ofReal_mul hc]] at hpoint
  dsimp only [fg] at hpoint
  rw [ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hscale.le hgnonneg)] at hpoint
  dsimp only [dref, dg] at hrefnonneg hgnonneg hpoint ⊢
  nlinarith

/-- For a positive-definite real `3 × 3` matrix, an upper bound on every
quadratic value and a determinant lower bound force a lower bound on every
quadratic value. -/
theorem finThree_euclideanQuadratic_lower_of_det_lower_of_upper
    {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hS : S.PosDef)
    {K D c : ℝ}
    (hK : 0 ≤ K)
    (hdet : D ≤ S.det)
    (hupper : ∀ v : Fin 3 → ℝ,
      v ⬝ᵥ (S *ᵥ v) ≤ K * (v ⬝ᵥ v))
    (hcD : c * K ^ 2 ≤ D) :
    ∀ v : Fin 3 → ℝ,
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v) := by
  classical
  let hH : S.IsHermitian := hS.isHermitian
  have heigPos (i : Fin 3) : 0 < hH.eigenvalues i := by
    simpa only [hH] using hS.eigenvalues_pos i
  have heigUpper (i : Fin 3) : hH.eigenvalues i ≤ K := by
    let u : Fin 3 → ℝ := ⇑(hH.eigenvectorBasis i)
    have hu := hupper u
    have huNorm : u ⬝ᵥ u = 1 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, u,
        if_pos] using hH.eigenvectorBasis.inner_eq_ite i i
    have heq : hH.eigenvalues i = u ⬝ᵥ (S *ᵥ u) := by
      simpa only [RCLike.re_to_real, star_trivial, u] using
        hH.eigenvalues_eq i
    rw [← heq, huNorm, mul_one] at hu
    exact hu
  have hprod : D ≤
      hH.eigenvalues 0 * (hH.eigenvalues 1 * hH.eigenvalues 2) := by
    rw [hH.det_eq_prod_eigenvalues] at hdet
    simpa [Fin.prod_univ_succ] using hdet
  have heigLower (i : Fin 3) : c ≤ hH.eigenvalues i := by
    have hKpos : 0 < K := lt_of_lt_of_le (heigPos 0) (heigUpper 0)
    have hKsq : 0 < K ^ 2 := sq_pos_of_pos hKpos
    fin_cases i
    · have hp : hH.eigenvalues 1 * hH.eigenvalues 2 ≤ K ^ 2 := by
        rw [pow_two]
        exact mul_le_mul (heigUpper 1) (heigUpper 2)
          (le_of_lt (heigPos 2)) hK
      have hchain : c * K ^ 2 ≤ hH.eigenvalues 0 * K ^ 2 :=
        hcD.trans (hprod.trans
          (mul_le_mul_of_nonneg_left hp (le_of_lt (heigPos 0))))
      exact le_of_mul_le_mul_right hchain hKsq
    · have hp : hH.eigenvalues 0 * hH.eigenvalues 2 ≤ K ^ 2 := by
        rw [pow_two]
        exact mul_le_mul (heigUpper 0) (heigUpper 2)
          (le_of_lt (heigPos 2)) hK
      have hreassoc :
          hH.eigenvalues 0 * (hH.eigenvalues 1 * hH.eigenvalues 2) =
            hH.eigenvalues 1 * (hH.eigenvalues 0 * hH.eigenvalues 2) := by
        ring
      have hchain : c * K ^ 2 ≤ hH.eigenvalues 1 * K ^ 2 := by
        calc
          c * K ^ 2 ≤ D := hcD
          _ ≤ hH.eigenvalues 0 *
              (hH.eigenvalues 1 * hH.eigenvalues 2) := hprod
          _ = hH.eigenvalues 1 *
              (hH.eigenvalues 0 * hH.eigenvalues 2) := hreassoc
          _ ≤ hH.eigenvalues 1 * K ^ 2 :=
            mul_le_mul_of_nonneg_left hp (le_of_lt (heigPos 1))
      exact le_of_mul_le_mul_right hchain hKsq
    · have hp : hH.eigenvalues 0 * hH.eigenvalues 1 ≤ K ^ 2 := by
        rw [pow_two]
        exact mul_le_mul (heigUpper 0) (heigUpper 1)
          (le_of_lt (heigPos 1)) hK
      have hreassoc :
          hH.eigenvalues 0 * (hH.eigenvalues 1 * hH.eigenvalues 2) =
            hH.eigenvalues 2 * (hH.eigenvalues 0 * hH.eigenvalues 1) := by
        ring
      have hchain : c * K ^ 2 ≤ hH.eigenvalues 2 * K ^ 2 := by
        calc
          c * K ^ 2 ≤ D := hcD
          _ ≤ hH.eigenvalues 0 *
              (hH.eigenvalues 1 * hH.eigenvalues 2) := hprod
          _ = hH.eigenvalues 2 *
              (hH.eigenvalues 0 * hH.eigenvalues 1) := hreassoc
          _ ≤ hH.eigenvalues 2 * K ^ 2 :=
            mul_le_mul_of_nonneg_left hp (le_of_lt (heigPos 2))
      exact le_of_mul_le_mul_right hchain hKsq
  have hdiag :
      (Matrix.diagonal
        (fun i : Fin 3 ↦ hH.eigenvalues i - c)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (heigLower i)
  let U : Matrix.unitaryGroup (Fin 3) ℝ := hH.eigenvectorUnitary
  have hconj := hdiag.mul_mul_conjTranspose_same
    (U : Matrix (Fin 3) (Fin 3) ℝ)
  have hdiff :
      (S - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
    rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    change
      ((U : Matrix (Fin 3) (Fin 3) ℝ) *
          Matrix.diagonal (fun i ↦ hH.eigenvalues i) *
          star (U : Matrix (Fin 3) (Fin 3) ℝ) - c • 1).PosSemidef
    convert hconj using 1
    rw [show Matrix.diagonal
        (fun i : Fin 3 ↦ hH.eigenvalues i - c) =
        Matrix.diagonal hH.eigenvalues - c • 1 by
      simp only [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]]
    have hUU :
        (U : Matrix (Fin 3) (Fin 3) ℝ) *
            star (U : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
      Unitary.coe_mul_star_self U
    have hcconj :
        (U : Matrix (Fin 3) (Fin 3) ℝ) * (c • 1) *
            star (U : Matrix (Fin 3) (Fin 3) ℝ) = c • 1 := by
      simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
    rw [Matrix.star_eq_conjTranspose] at hcconj
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, hcconj]
  intro v
  have hv := hdiff.dotProduct_mulVec_nonneg v
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, star_trivial, smul_eq_mul,
    sub_nonneg] using hv

/-- A lower bound between three-dimensional Gram densities and an upper
quadratic comparison give the complementary lower quadratic comparison. -/
theorem finThree_relativeQuadratic_lower_of_density_lower_of_upper
    {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (hB : B.PosDef)
    {C d : ℝ} (hC : 0 < C) (hd : 0 < d)
    (hdensity : d * VolumeDensity.chartVolumeDensity A ≤
      VolumeDensity.chartVolumeDensity B)
    (hupper : ∀ v : Fin 3 → ℝ,
      v ⬝ᵥ (B *ᵥ v) ≤ C ^ 2 * (v ⬝ᵥ (A *ᵥ v))) :
    ∀ v : Fin 3 → ℝ,
      (d / C ^ 2) ^ 2 * (v ⬝ᵥ (A *ᵥ v)) ≤
        v ⬝ᵥ (B *ᵥ v) := by
  let e := positiveDefiniteGramLinearEquiv A hA
  let P := linearPullbackCoordinateMatrix e
  have hAeq : A = Pᵀ * P := by
    rw [← linearPullbackGramMatrix_eq_transpose_mul e]
    exact
      (linearPullbackGramMatrix_positiveDefiniteGramLinearEquiv A hA).symm
  have hPdetunit : IsUnit P.det := by
    rw [show P.det = LinearMap.det
        (e : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 3)) by
      exact det_linearPullbackCoordinateMatrix e]
    exact e.toLinearEquiv.isUnit_det'
  have hPunit : IsUnit P :=
    (Matrix.isUnit_iff_isUnit_det P).mpr hPdetunit
  let Pinv : Matrix (Fin 3) (Fin 3) ℝ := P⁻¹
  let S : Matrix (Fin 3) (Fin 3) ℝ := Pinvᵀ * B * Pinv
  have hPinvunit : IsUnit Pinv := by
    dsimp only [Pinv]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hPunit
  have hSpos : S.PosDef := by
    dsimp only [S]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit hPinvunit)
  have hquadS (y : Fin 3 → ℝ) :
      y ⬝ᵥ (S *ᵥ y) =
        (Pinv *ᵥ y) ⬝ᵥ (B *ᵥ (Pinv *ᵥ y)) := by
    dsimp only [S]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hquadA (v : Fin 3 → ℝ) :
      v ⬝ᵥ (A *ᵥ v) = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
    rw [hAeq, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hPmulPinv (y : Fin 3 → ℝ) : P *ᵥ (Pinv *ᵥ y) = y := by
    dsimp only [Pinv]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPdetunit,
      Matrix.one_mulVec]
  have hPinvmulP (v : Fin 3 → ℝ) : Pinv *ᵥ (P *ᵥ v) = v := by
    dsimp only [Pinv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hPdetunit,
      Matrix.one_mulVec]
  have hSupper (y : Fin 3 → ℝ) :
      y ⬝ᵥ (S *ᵥ y) ≤ C ^ 2 * (y ⬝ᵥ y) := by
    rw [hquadS]
    calc
      (Pinv *ᵥ y) ⬝ᵥ (B *ᵥ (Pinv *ᵥ y)) ≤
          C ^ 2 * ((Pinv *ᵥ y) ⬝ᵥ (A *ᵥ (Pinv *ᵥ y))) :=
        hupper (Pinv *ᵥ y)
      _ = C ^ 2 * (y ⬝ᵥ y) := by
        rw [hquadA, hPmulPinv]
  have hAdet : A.det = P.det ^ 2 := by
    rw [hAeq, Matrix.det_mul, Matrix.det_transpose, pow_two]
  have hSdet : S.det = Pinv.det ^ 2 * B.det := by
    dsimp only [S]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hInvDet : Pinv.det * P.det = 1 := by
    dsimp only [Pinv]
    exact Matrix.det_nonsing_inv_mul_det P hPdetunit
  have hAdetNonneg : 0 ≤ A.det := hA.det_pos.le
  have hBdetNonneg : 0 ≤ B.det := hB.det_pos.le
  have hdensitySq :=
    (sq_le_sq₀
      (mul_nonneg hd.le (VolumeDensity.chartVolumeDensity_nonneg A))
      (VolumeDensity.chartVolumeDensity_nonneg B)).2 hdensity
  have hdetrel : d ^ 2 * A.det ≤ B.det := by
    simpa only [mul_pow, VolumeDensity.chartVolumeDensity,
      VolumeDensity.chartGramDet, abs_of_nonneg hAdetNonneg,
      abs_of_nonneg hBdetNonneg, Real.sq_sqrt hAdetNonneg,
      Real.sq_sqrt hBdetNonneg] using hdensitySq
  have hdetS : d ^ 2 ≤ S.det := by
    rw [hSdet]
    have hmul := mul_le_mul_of_nonneg_left hdetrel (sq_nonneg Pinv.det)
    have hcancel : Pinv.det ^ 2 * (d ^ 2 * A.det) = d ^ 2 := by
      rw [hAdet]
      calc
        Pinv.det ^ 2 * (d ^ 2 * P.det ^ 2) =
            d ^ 2 * (Pinv.det * P.det) ^ 2 := by ring
        _ = d ^ 2 := by rw [hInvDet]; ring
    rw [hcancel] at hmul
    nlinarith
  have hscale :
      (d / C ^ 2) ^ 2 * (C ^ 2) ^ 2 = d ^ 2 := by
    field_simp [ne_of_gt hC]
  have hSlower :=
    finThree_euclideanQuadratic_lower_of_det_lower_of_upper hSpos
      (K := C ^ 2) (D := d ^ 2) (c := (d / C ^ 2) ^ 2)
      (sq_nonneg C) hdetS hSupper (le_of_eq hscale)
  intro v
  have hv := hSlower (P *ᵥ v)
  rw [hquadS, hPinvmulP] at hv
  rw [hquadA]
  exact hv

/-- Pointwise inverse-chart density control and pointwise metric upper
control imply the complementary metric lower comparison in dimension three. -/
theorem uniformClosedRiemannianMetricLowerComparison_of_inverseChartDensity
    {J : Type v}
    (gref : ClosedSmoothRiemannianMetric 3 M)
    (g : J → ClosedSmoothRiemannianMetric 3 M)
    {C d : ℝ} (hC : 0 < C) (hd : 0 < d)
    (hupper : ∀ j x
        (w : TangentSpace I x),
      (g j).inner x w w ≤ C ^ 2 * gref.inner x w w)
    (hdensity : ∀ j x₀ (z : (extChartAt I x₀).target),
      d * inverseChartPullbackVolumeDensity gref x₀ z ≤
        inverseChartPullbackVolumeDensity (g j) x₀ z) :
    UniformClosedRiemannianMetricLowerComparison
      gref g ((d / C ^ 2) ^ 2) := by
  refine ⟨sq_pos_of_pos (div_pos hd (sq_pos_of_pos hC)), ?_⟩
  intro j x w
  let z : (extChartAt I x).target :=
    ⟨(extChartAt I x) x, mem_extChartAt_target x⟩
  let b :=
    ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
      (n := 3) (M := M) x z.2
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    inverseChartPullbackGramMatrix gref x z
  let B : Matrix (Fin 3) (Fin 3) ℝ :=
    inverseChartPullbackGramMatrix (g j) x z
  have hzpoint :
      inverseExtendedChartParametrization (n := 3) (M := M) x z = x := by
    dsimp [z, inverseExtendedChartParametrization,
      inverseExtendedChartHomeomorph]
    exact (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hmatrix (g₀ : ClosedSmoothRiemannianMetric 3 M) :
      inverseChartPullbackGramMatrix g₀ x z =
        LinearMap.toMatrix₂ b b (g₀.metricBilinAt x) := by
    ext i k
    change g₀.inner
        (inverseExtendedChartParametrization (n := 3) (M := M) x z)
          (b i) (b k) =
      (LinearMap.toMatrix₂ b b) (g₀.metricBilinAt x) i k
    rw [hzpoint, LinearMap.toMatrix₂_apply]
    exact
      (ClosedSmoothRiemannianMetric.metricBilinAt_apply
        g₀ x (b i) (b k)).symm
  have hquad (g₀ : ClosedSmoothRiemannianMetric 3 M)
      (a : Fin 3 → ℝ) :
      a ⬝ᵥ (inverseChartPullbackGramMatrix g₀ x z *ᵥ a) =
        g₀.inner x (b.equivFun.symm a) (b.equivFun.symm a) := by
    rw [hmatrix g₀]
    simpa only [star_trivial,
      ClosedSmoothRiemannianMetric.metricBilinAt_apply] using
      (dotProduct_toMatrix₂_mulVec b b (g₀.metricBilinAt x) a a)
  have hA : A.PosDef := by
    exact inverseChartPullbackGramMatrix_posDef gref x z
  have hB : B.PosDef := by
    exact inverseChartPullbackGramMatrix_posDef (g j) x z
  have hmatrixUpper : ∀ a : Fin 3 → ℝ,
      a ⬝ᵥ (B *ᵥ a) ≤ C ^ 2 * (a ⬝ᵥ (A *ᵥ a)) := by
    intro a
    change
      a ⬝ᵥ (inverseChartPullbackGramMatrix (g j) x z *ᵥ a) ≤
        C ^ 2 *
          (a ⬝ᵥ (inverseChartPullbackGramMatrix gref x z *ᵥ a))
    rw [hquad (g j) a, hquad gref a]
    exact hupper j x (b.equivFun.symm a)
  have hmatrixDensity :
      d * VolumeDensity.chartVolumeDensity A ≤
        VolumeDensity.chartVolumeDensity B := by
    exact hdensity j x z
  have hlower :=
    finThree_relativeQuadratic_lower_of_density_lower_of_upper
      hA hB hC hd hmatrixDensity hmatrixUpper (b.equivFun w)
  change
    (d / C ^ 2) ^ 2 * gref.inner x w w ≤ (g j).inner x w w
  rw [← b.equivFun.symm_apply_apply w]
  exact (hquad gref (b.equivFun w)).symm ▸
    (hquad (g j) (b.equivFun w)).symm ▸ hlower

/-- Compact tensor-family volume control has one positive inverse-chart
density factor valid for the entire family. -/
theorem CompactReferenceMetricTensorFamilyData.exists_uniform_inverseChartPullbackVolumeDensity_lower
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {metric : K → ClosedSmoothRiemannianMetric 3 M}
    (data : CompactReferenceMetricTensorFamilyData K metric) :
    ∃ d : ℝ, 0 < d ∧ ∀ k x₀
        (z : (extChartAt I x₀).target),
      d * inverseChartPullbackVolumeDensity data.referenceMetric x₀ z ≤
        inverseChartPullbackVolumeDensity (metric k) x₀ z := by
  obtain ⟨kMin, _hkMin, hkMin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMinOn
      Set.univ_nonempty data.volumeFactor_continuous.continuousOn
  refine ⟨data.volumeFactor kMin, data.volumeFactor_pos kMin, ?_⟩
  intro k x₀ z
  have hfactor : data.volumeFactor kMin ≤ data.volumeFactor k :=
    hkMin (Set.mem_univ k)
  calc
    data.volumeFactor kMin *
          inverseChartPullbackVolumeDensity data.referenceMetric x₀ z ≤
        data.volumeFactor k *
          inverseChartPullbackVolumeDensity data.referenceMetric x₀ z :=
      mul_le_mul_of_nonneg_right hfactor
        (inverseChartPullbackVolumeDensity_pos
          data.referenceMetric x₀ z).le
    _ ≤ inverseChartPullbackVolumeDensity (metric k) x₀ z :=
      inverseChartPullbackVolumeDensity_lower_of_volumeMeasureReal_lower
        data.referenceMetric (metric k) (data.volumeFactor_pos k).le
        (data.volume_le k) x₀ z

/-- Compact tensor-family upper metric control and lower volume control
produce a uniform positive lower comparison with the reference metric. -/
theorem CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {metric : K → ClosedSmoothRiemannianMetric 3 M}
    (data : CompactReferenceMetricTensorFamilyData K metric) :
    ∃ c : ℝ,
      UniformClosedRiemannianMetricLowerComparison
        data.referenceMetric metric c := by
  obtain ⟨kMax, _hkMax, hkMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMaxOn
      Set.univ_nonempty data.metricFactor_continuous.continuousOn
  let C : ℝ := data.metricFactor kMax
  have hC : 0 < C := data.metricFactor_pos kMax
  have hupper : ∀ k x
      (w : TangentSpace I x),
      (metric k).inner x w w ≤
        C ^ 2 * data.referenceMetric.inner x w w := by
    intro k x w
    have hfactorSq : data.metricFactor k ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (data.metricFactor_pos k).le hC.le).2 <| by
        simpa only [C] using hkMax (Set.mem_univ k)
    exact (data.metric_le k x w).trans <|
      mul_le_mul_of_nonneg_right hfactorSq
        (data.referenceMetric.inner_nonneg x w)
  obtain ⟨d, hd, hdensity⟩ :=
    data.exists_uniform_inverseChartPullbackVolumeDensity_lower
  refine ⟨(d / C ^ 2) ^ 2, ?_⟩
  exact
    uniformClosedRiemannianMetricLowerComparison_of_inverseChartDensity
      data.referenceMetric metric hC hd hupper hdensity

end Poincare
