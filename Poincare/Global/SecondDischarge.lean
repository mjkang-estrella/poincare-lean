import Poincare.Global.SecondFlowDerivative

/-!
# Second-variation discharge at split geodesic data

This module instantiates the augmented Gronwall theorem at the
chart-Christoffel field after combining the separate geodesic and linearized
ODE facts into the augmented first-variation system.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Fixed-time second-variation derivative for the augmented chart geodesic flow,
with the augmented ODE hypotheses discharged from separate geodesic and
first-variation ODE facts.

The theorem packages `τ ↦ (α p τ, Φ p ψ τ)` as a solution of the augmented
system `(p, ψ)' = (F p, D F p ψ)`, derives the `C¹` and compact Lipschitz data
for that augmented field from the smooth chart-Christoffel field, and then
applies `augmentedFlow_hasDerivAt_of_secondVariation_gronwall`.
-/
theorem chartChristoffel_augmentedFlow_hasDerivAt_of_geodesic_linearized_data
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {α : E × E → ℝ → E × E}
    {Φ : E × E → E × E → ℝ → E × E}
    {z η : (E × E) × (E × E)}
    {Ξ : ℝ → (E × E) × (E × E)}
    {T a : ℝ} {p : (E × E) × (E × E)} {t : ℝ}
    (hT : 0 < T)
    (hbaseα0 : α z.1 0 = z.1)
    (hbaseαder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (α z.1)
        (geodesicFlowField (chartChristoffelField g x₀) (α z.1 τ))
        (Icc (0 : ℝ) T) τ)
    (hbaseΦ0 : Φ z.1 z.2 0 = z.2)
    (hbaseΦder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Φ z.1 z.2)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) (α z.1) τ (Φ z.1 z.2 τ))
        (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T,
      (α z.1 τ, Φ z.1 z.2 τ) ∈ closedBall p a)
    (hpert : ∀ᶠ s in 𝓝 (0 : ℝ),
      α (z + s • η).1 0 = (z + s • η).1 ∧
        Φ (z + s • η).1 (z + s • η).2 0 = (z + s • η).2 ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (α (z + s • η).1)
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (z + s • η).1 τ))
            (Icc (0 : ℝ) T) τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Φ (z + s • η).1 (z + s • η).2)
            (linearizedGeodesicFlowFieldAlong
              (chartChristoffelField g x₀)
              (α (z + s • η).1) τ
              (Φ (z + s • η).1 (z + s • η).2 τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          (α (z + s • η).1 τ,
            Φ (z + s • η).1 (z + s • η).2 τ) ∈ closedBall p a)
    (hΞ0 : Ξ 0 = η)
    (hΞder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ξ
        (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
          (fun r : ℝ => (α z.1 r, Φ z.1 z.2 r)) τ (Ξ τ))
        (Icc (0 : ℝ) T) τ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt
      (fun s : ℝ =>
        (α (z + s • η).1 t,
          Φ (z + s • η).1 (z + s • η).2 t))
      (Ξ t) 0 := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let β : ((E × E) × (E × E)) → ℝ → ((E × E) × (E × E)) :=
    fun y τ => (α y.1 τ, Φ y.1 y.2 τ)
  have hΓ : ContDiff ℝ 2 Γ := by
    rw [contDiff_iff_contDiffAt]
    intro q
    have hthree_le_top : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hthree_add_one_le_top : (3 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
      rw [show (3 : ℕ∞ω) + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hg3 :
        ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 3
          (fun y : M =>
            (⟨y, g.inner y⟩ :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
      simpa using g.contMDiff_inner.of_le hthree_le_top
    have hblend :
        ContDiff ℝ (2 + 1)
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀) := by
      simpa using
        (CovariantDerivative.contDiff_blendedChartMetric
          (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
          hthree_add_one_le_top (cutoff_contDiff (n := n) x₀)
          (cutoff_tsupport (n := n) x₀) hg3)
    apply contDiffAt_clm_of_apply
    intro u
    apply contDiffAt_clm_of_apply
    intro v
    simpa [Γ, chartChristoffelField] using
      (CovariantDerivative.contDiffAt_christoffelAt
        (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (k := 2) (x := q)
        hblend
        (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (CovariantDerivative.chartBilin_nondegenerate
          (cutoff (n := n) x₀) (backgroundMetric (n := n))
          (backgroundMetric_pos (n := n)) g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
          (cutoff_support_invertible (n := n) x₀))
        (fun z v w => rfl) v u)
  have hF : ContDiff ℝ 2 (geodesicFlowField Γ) := by
    have hp : ContDiff ℝ 2 (fun q : E × E => q.1) := contDiff_fst
    have hv : ContDiff ℝ 2 (fun q : E × E => q.2) := contDiff_snd
    have hΓp : ContDiff ℝ 2 (fun q : E × E => Γ q.1) := hΓ.comp hp
    have hΓpv : ContDiff ℝ 2 (fun q : E × E => Γ q.1 q.2) :=
      hΓp.clm_apply hv
    have hΓpvv : ContDiff ℝ 2 (fun q : E × E => Γ q.1 q.2 q.2) :=
      hΓpv.clm_apply hv
    simpa [geodesicFlowField, Γ] using hv.prodMk hΓpvv.neg
  let F : E × E → E × E := geodesicFlowField Γ
  have haug : ContDiff ℝ 1 (augmentedGeodesicFlowField Γ) := by
    have hbase : ContDiff ℝ 1 (fun y : (E × E) × (E × E) => F y.1) :=
      (hF.of_le (by norm_num)).comp contDiff_fst
    have hlin :
        ContDiff ℝ 1
          (fun y : (E × E) × (E × E) =>
            (fderiv ℝ F y.1 : (E × E) →L[ℝ] (E × E)) y.2) := by
      simpa [F] using
        (hF.contDiff_fderiv_apply (m := 1) (by norm_num))
    simpa [augmentedGeodesicFlowField, linearizedGeodesicFlowOperator, F, Γ] using
      hbase.prodMk hlin
  rcases haug.contDiffOn.exists_lipschitzOnWith
      (by norm_num)
      (convex_closedBall p (a + 1))
      (isCompact_closedBall p (a + 1)) with
    ⟨K, hLip⟩
  have hbase0 : β z 0 = z := by
    change (α z.1 0, Φ z.1 z.2 0) = z
    rw [hbaseα0, hbaseΦ0]
  have hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β z)
        (augmentedGeodesicFlowField Γ (β z τ)) (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    simpa [β, Γ, augmentedGeodesicFlowField, linearizedGeodesicFlowFieldAlong]
      using (hbaseαder τ hτ).prodMk (hbaseΦder τ hτ)
  have hpert_aug : ∀ᶠ s in 𝓝 (0 : ℝ),
      β (z + s • η) 0 = z + s • η ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (z + s • η))
            (augmentedGeodesicFlowField Γ (β (z + s • η) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          β (z + s • η) τ ∈ closedBall p a := by
    filter_upwards [hpert] with s hs
    rcases hs with ⟨hα0, hΦ0, hαder, hΦder, hmem⟩
    constructor
    · change
        (α (z + s • η).1 0, Φ (z + s • η).1 (z + s • η).2 0) =
          z + s • η
      rw [hα0, hΦ0]
    constructor
    · intro τ hτ
      simpa [β, Γ, augmentedGeodesicFlowField, linearizedGeodesicFlowFieldAlong]
        using (hαder τ hτ).prodMk (hΦder τ hτ)
    · intro τ hτ
      simpa [β] using hmem τ hτ
  have hΞder' : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Ξ
        (secondVariationFlowFieldAlong Γ (β z) τ (Ξ τ))
        (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    simpa [β, Γ] using hΞder τ hτ
  have hresult :=
    augmentedFlow_hasDerivAt_of_secondVariation_gronwall
      (Γ := Γ) (β := β) (z := z) (η := η) (Ξ := Ξ)
      (T := T) (a := a) (K := K) (p := p) (t := t)
      hT haug (isCompact_closedBall p (a + 1)) hLip hbase0 hbase_der
      hbase_mem hpert_aug hΞ0 hΞder' ht
  simpa [β] using hresult

end GeodesicTransport
end Poincare
