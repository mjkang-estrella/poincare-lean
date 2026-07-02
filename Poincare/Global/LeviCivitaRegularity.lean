import Poincare.Global.LeviCivitaTransport

/-!
# Local regularity bridges for the closed Levi-Civita connection

This module collects the local regularity facts needed to turn the
chart-transported Levi-Civita value identification into the global
`ContMDiffCovariantDerivative` instance.
-/

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/--
The inverse-chart pullback of a `C^m` tangent field is `C^m` at source
points after applying the chart.

This is the regularity upgrade of
`chartTransportedLeviCivitaSection_mdiffAt_apply_chart`; it isolates one
of the local-to-global gluing ingredients for the closed Levi-Civita
connection.
-/
theorem chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E]
    (x₀ : M) {X : Π y : M, TangentSpace I y} {y : M} {m : ℕ∞ω}
    (hy : y ∈ (extChartAt I x₀).source)
    (hX : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) m (T% X) y)
    (hm : m + 1 ≤ (∞ : ℕ∞ω)) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (T% (chartTransportedLeviCivitaSection (I := I) x₀ X))
      (extChartAt I x₀ y) := by
  have hleft : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  have htarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hy
  have hsmWithin :
      CMDiffAt[range I] ∞ ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) :=
    contMDiffWithinAt_extChartAt_symm_range (n := ∞) x₀ htarget
  have hsm :
      CMDiffAt ∞ ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y) := by
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at hsmWithin
  have hinv :
      (mfderiv% ((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)).IsInvertible := by
    have hinvWithin := isInvertible_mfderivWithin_extChartAt_symm htarget
    rwa [I.range_eq_univ, mfderivWithin_univ] at hinvWithin
  have hX' :
      CMDiffAt m (T% X) (((extChartAt I x₀).symm : E → M)
        (extChartAt I x₀ y)) := by
    rw [hleft]
    exact hX
  have hpull := hX'.mpullback_vectorField_preimage hsm hinv hm
  simpa [chartTransportedLeviCivitaSection, I.range_eq_univ] using hpull

section ChartHom

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/--
The hom-valued manifold section obtained by applying the chart Levi-Civita
connection to the inverse-chart pullback of a tangent field and pushing the
result back to the manifold tangent fiber.
-/
noncomputable def chartTransportedLeviCivitaHom
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y :=
  let z : E := extChartAt I x₀ y
  let D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  D.comp ((covC σc z).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y))

theorem chartTransportedLeviCivitaHom_apply
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) (v : TangentSpace I y) :
    chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp σ y v =
      chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
        hsupp σ hy v := by
  rfl

end ChartHom

end CovariantDerivative

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

namespace LeviCivitaTransport

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

theorem chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    {σ : Π y : M, TM y} {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hχone : ∀ᶠ z' in 𝓝 (extChartAt I x₀ y), χ z' = 1)
    (hσ : MDiffAtTangentField σ y) :
    CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ y =
      (LeviCivitaExistence.closedLeviCivitaConnection g) σ y := by
  ext v
  rw [CovariantDerivative.chartTransportedLeviCivitaHom_apply χ G₀ hG₀pos
    g.inner (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1
    hsupp σ hy v]
  exact chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
    g χ G₀ hG₀pos x₀ hχ0 hχ1 hsupp hbl hG₀symm hy hχone hσ v

theorem chartTransportedLeviCivitaHom_eventuallyEq_closed
    (g : ClosedSmoothRiemannianMetric n M)
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
    (hG₀symm : ∀ v w : E, G₀ v w = G₀ w v)
    {σ : Π y : M, TM y}
    (hχone : ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀), χ z = 1)
    (hσ : ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) Set.univ) :
    (fun y : M =>
      (⟨y,
        (CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀ hχ0 hχ1 hsupp σ y)⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
      =ᶠ[𝓝 x₀]
    (fun y : M =>
      (⟨y, (LeviCivitaExistence.closedLeviCivitaConnection g) σ y⟩ :
        TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y))) := by
  let oneLocus : Set E := {z | ∀ᶠ z' in 𝓝 z, χ z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ 𝓝 (extChartAt I x₀ x₀) :=
    hopen.mem_nhds hχone
  have hcont : ContinuousAt (fun y : M => extChartAt I x₀ y) x₀ := by
    simpa only using (continuousAt_extChartAt x₀)
  have hone_pre : (extChartAt I x₀) ⁻¹' oneLocus ∈ 𝓝 x₀ :=
    hcont.preimage_mem_nhds hone_mem
  have hsource : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
    extChartAt_source_mem_nhds x₀
  filter_upwards [hsource, hone_pre] with y hy hyloc
  have hσy : MDiffAtTangentField σ y := by
    simpa [MDiffAtTangentField] using
      ((hσ.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp))
  have hclm := chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one
    g χ G₀ hG₀pos x₀ hχ0 hχ1 hsupp hbl hG₀symm hy hyloc hσy
  simp [hclm]

end LeviCivitaTransport

/-!
The full theorem
`closedLeviCivitaConnection_contMDiff` is not introduced here yet: the
remaining step is to prove the local `ContMDiffAt` regularity of the
chart-transported hom-bundle section, then combine it with
`chartTransportedLeviCivitaHom_eventuallyEq_closed` by
`ContMDiffAt.congr_of_eventuallyEq`.
-/

end Poincare
