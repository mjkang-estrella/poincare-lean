import Poincare.Global.LeviCivitaTransport
import Poincare.LocalConnectionRegularity

/-!
# Local regularity bridges for the closed Levi-Civita connection

This module collects the local regularity facts needed to turn the
chart-transported Levi-Civita value identification into the global
`ContMDiffCovariantDerivative` instance.
-/

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

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

theorem chartTransportedLeviCivitaHom_inCoordinates_apply_chart
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x₀ y x₀ y
        (chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
          hsupp σ y) =
      (chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)
        (chartTransportedLeviCivitaSection (I := I) x₀ σ)
        (extChartAt I x₀ y) := by
  have hy_chart : y ∈ (chartAt H x₀).source := by
    simpa [extChartAt_source] using hy
  have hround :
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y).comp
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (Set.range I) (extChartAt I x₀ y)) =
        ContinuousLinearMap.id ℝ E := by
    simpa using mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
      (I := I) hy
  ext v
  rw [ContinuousLinearMap.inCoordinates]
  simp only [chartTransportedLeviCivitaHom]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy_chart,
    TangentBundle.symmL_trivializationAt hy_chart]
  let A : TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, E) (extChartAt I x₀ y) :=
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y
  let D : TangentSpace 𝓘(ℝ, E) (extChartAt I x₀ y) →L[ℝ] TangentSpace I y :=
    mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
      (Set.range I) (extChartAt I x₀ y)
  let C : TangentSpace 𝓘(ℝ, E) (extChartAt I x₀ y) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (extChartAt I x₀ y) :=
    (chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)
      (chartTransportedLeviCivitaSection (I := I) x₀ σ) (extChartAt I x₀ y)
  change (A.comp D) (C ((A.comp D) v)) = C v
  have hAD : A.comp D = ContinuousLinearMap.id ℝ E := by
    simpa [A, D] using hround
  rw [hAD]
  change C ((ContinuousLinearMap.id ℝ E) v) = C v
  rw [ContinuousLinearMap.id_apply]

/--
The chart Levi-Civita hom applied to the inverse-chart transport of a
manifold field is locally `C¹` in model coordinates.  The transported field is
only known locally, so the proof globalizes it by a bump function and then
uses germ locality of covariant derivatives to return to the original field.
-/
theorem chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt
    [IsManifold I ∞ M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hσ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) y) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
      (fun z =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z
          ((chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)
            (chartTransportedLeviCivitaSection (I := I) x₀ σ) z))
      (extChartAt I x₀ y) := by
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  have hσc :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (T% σc) (extChartAt I x₀ y) := by
    simpa [σc] using
      chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
        (I := I) x₀ hy hσ (by
          rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
            show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
          exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨v, hv, hσcv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hσc
  set u : Set E := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hzu : extChartAt I x₀ y ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hσcu : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (T% σc) u :=
    hσcv.mono interior_subset
  obtain ⟨ψ, -, hψsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E))
        (extChartAt I x₀ y)).mem_iff.mp (hu_open.mem_nhds hzu))
  set τ : Π z : E, TangentSpace 𝓘(ℝ, E) z := (ψ : E → ℝ) • σc with hτ
  have hτglob : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (T% τ) :=
    ContMDiffOn.smul_section_of_tsupport
      ((ψ.contMDiff.of_le (by
        rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn)
      hu_open hψsupp hσcu
  haveI hcovC : ContMDiffCovariantDerivative covC 1 :=
    chartLeviCivita_contMDiff χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
      (k := 1) (by
        rw [show (1 : ℕ∞ω) + 1 + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top) hχ htsupp hg
  have hτhomOn :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := covC) (k := 1)).contMDiff
      (σ := τ) hτglob.contMDiffOn
  have hτhomAt :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        (extChartAt I x₀ y) :=
    hτhomOn.contMDiffAt Filter.univ_mem
  have hτcoord :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
        (fun z : E =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z))
        (extChartAt I x₀ y) :=
    (contMDiffAt_hom_bundle
      (fun z : E =>
        (⟨z, covC τ z⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun z : E =>
              TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                TangentSpace 𝓘(ℝ, E) z)))).mp hτhomAt |>.2
  set w : Set E := interior {z | (ψ : E → ℝ) z = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hzw : extChartAt I x₀ y ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr ψ.eventuallyEq_one, hzu⟩
  have hστ : ∀ z ∈ interior {z | (ψ : E → ℝ) z = 1}, σc z = τ z := by
    intro z hz
    have h1 : z ∈ {z | (ψ : E → ℝ) z = 1} := interior_subset hz
    have h1eq : (ψ : E → ℝ) z = 1 := by
      simpa using h1
    rw [hτ]
    change σc z = (ψ : E → ℝ) z • σc z
    rw [h1eq]
    simp
  have hev :
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC σc z))
        =ᶠ[𝓝 (extChartAt I x₀ y)]
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z)) := by
    filter_upwards [hw_open.mem_nhds hzw] with z hz
    have hσcz : MDiffAt (T% σc) z :=
      ((hσcu z hz.2).contMDiffAt (hu_open.mem_nhds hz.2)).mdifferentiableAt
        two_ne_zero
    have hτz : MDiffAt (T% τ) z :=
      (hτglob z).mdifferentiableAt two_ne_zero
    have hcongr : covC σc z = covC τ z := by
      apply covC.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσcz hτz
        Filter.univ_mem
      filter_upwards [isOpen_interior.mem_nhds hz.1] with z' hz'
      exact hστ z' hz'
    rw [hcongr]
  exact hτcoord.congr_of_eventuallyEq hev

/--
The chart-transported hom section is locally `C¹` as a section of the
manifold hom-bundle.
-/
theorem chartTransportedLeviCivitaHom_contMDiffAt
    [IsManifold I ∞ M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (σ : Π y : M, TangentSpace I y)
    (hσ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y : M =>
        (⟨y,
          chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀
            hχ0 hχ1 hsupp σ y⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun y : M =>
              TangentSpace I y →L[ℝ] TangentSpace I y)))
      x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  have hmodel :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
        (fun z =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) z (extChartAt I x₀ x₀) z
            (covC σc z))
        (extChartAt I x₀ x₀) := by
    simpa [covC, σc] using
      chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt
        (I := I) χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp hχ htsupp hg
        σ (mem_extChartAt_source x₀) hσ
  have hcomp :
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) 1
        (fun y : M =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (covC σc (extChartAt I x₀ y)))
        x₀ :=
    hmodel.comp x₀ (contMDiffAt_extChartAt (I := I) (n := 1) (x := x₀))
  exact hcomp.congr_of_eventuallyEq (by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with y hy
    have hchart :
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
            x₀ y x₀ y
            (chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀
              hχ0 hχ1 hsupp σ y)
          = covC σc (extChartAt I x₀ y) := by
        simpa [covC, σc] using
          chartTransportedLeviCivitaHom_inCoordinates_apply_chart
            (I := I) χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp σ hy
    have hmodel_id :
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (covC σc (extChartAt I x₀ y))
          = covC σc (extChartAt I x₀ y) :=
        inCoordinates_tangent_bundle_core_model_space
          (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
          (x₀ := extChartAt I x₀ x₀) (x := extChartAt I x₀ y)
          (y₀ := extChartAt I x₀ x₀) (y := extChartAt I x₀ y)
          (ϕ := covC σc (extChartAt I x₀ y))
    exact hchart.trans hmodel_id.symm)

/--
The chart Levi-Civita hom applied to the inverse-chart transport of a
manifold field is locally `C²` in model coordinates.
-/
theorem chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₂
    [IsManifold I ∞ M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hσ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% σ) y) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 2
      (fun z =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z
          ((chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)
            (chartTransportedLeviCivitaSection (I := I) x₀ σ) z))
      (extChartAt I x₀ y) := by
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  have hσc :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 3
        (T% σc) (extChartAt I x₀ y) := by
    simpa [σc] using
      chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
        (I := I) x₀ hy hσ (by
          rw [show (3 : ℕ∞ω) + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
            show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
          exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨v, hv, hσcv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 3) (by norm_num)).mp hσc
  set u : Set E := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hzu : extChartAt I x₀ y ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hσcu : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 3
      (T% σc) u :=
    hσcv.mono interior_subset
  obtain ⟨ψ, -, hψsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E))
        (extChartAt I x₀ y)).mem_iff.mp (hu_open.mem_nhds hzu))
  set τ : Π z : E, TangentSpace 𝓘(ℝ, E) z := (ψ : E → ℝ) • σc with hτ
  have hτglob : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 3
      (T% τ) :=
    ContMDiffOn.smul_section_of_tsupport
      ((ψ.contMDiff.of_le (by
        rw [show (3 : ℕ∞ω) = ((3 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn)
      hu_open hψsupp hσcu
  haveI hcovC : ContMDiffCovariantDerivative covC 2 :=
    chartLeviCivita_contMDiff χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
      (k := 2) (by
        rw [show (2 : ℕ∞ω) + 1 + 1 = ((4 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top) hχ htsupp hg
  have hτhomOn :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := covC) (k := 2)).contMDiff
      (σ := τ) hτglob.contMDiffOn
  have hτhomAt :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        (extChartAt I x₀ y) :=
    hτhomOn.contMDiffAt Filter.univ_mem
  have hτcoord :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 2
        (fun z : E =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z))
        (extChartAt I x₀ y) :=
    (contMDiffAt_hom_bundle
      (fun z : E =>
        (⟨z, covC τ z⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun z : E =>
              TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                TangentSpace 𝓘(ℝ, E) z)))).mp hτhomAt |>.2
  set w : Set E := interior {z | (ψ : E → ℝ) z = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hzw : extChartAt I x₀ y ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr ψ.eventuallyEq_one, hzu⟩
  have hστ : ∀ z ∈ interior {z | (ψ : E → ℝ) z = 1}, σc z = τ z := by
    intro z hz
    have h1 : z ∈ {z | (ψ : E → ℝ) z = 1} := interior_subset hz
    have h1eq : (ψ : E → ℝ) z = 1 := by
      simpa using h1
    rw [hτ]
    change σc z = (ψ : E → ℝ) z • σc z
    rw [h1eq]
    simp
  have hev :
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC σc z))
        =ᶠ[𝓝 (extChartAt I x₀ y)]
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z)) := by
    filter_upwards [hw_open.mem_nhds hzw] with z hz
    have hσcz : MDiffAt (T% σc) z :=
      ((hσcu z hz.2).contMDiffAt (hu_open.mem_nhds hz.2)).mdifferentiableAt
        (by norm_num)
    have hτz : MDiffAt (T% τ) z :=
      (hτglob z).mdifferentiableAt (by norm_num)
    have hcongr : covC σc z = covC τ z := by
      apply covC.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσcz hτz
        Filter.univ_mem
      filter_upwards [isOpen_interior.mem_nhds hz.1] with z' hz'
      exact hστ z' hz'
    rw [hcongr]
  exact hτcoord.congr_of_eventuallyEq hev

/--
The chart Levi-Civita hom applied to the inverse-chart transport of a
manifold field is locally `C³` in model coordinates.
-/
theorem chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₃
    [IsManifold I ∞ M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 4
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (σ : Π y : M, TangentSpace I y) {y : M}
    (hy : y ∈ (extChartAt I x₀).source)
    (hσ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 4 (T% σ) y) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 3
      (fun z =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z
          ((chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp)
            (chartTransportedLeviCivitaSection (I := I) x₀ σ) z))
      (extChartAt I x₀ y) := by
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  have hσc :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 4
        (T% σc) (extChartAt I x₀ y) := by
    simpa [σc] using
      chartTransportedLeviCivitaSection_contMDiffAt_apply_chart
        (I := I) x₀ hy hσ (by
          rw [show (4 : ℕ∞ω) + 1 = ((5 : ℕ∞) : ℕ∞ω) from rfl,
            show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
          exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨v, hv, hσcv⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 4) (by norm_num)).mp hσc
  set u : Set E := interior v with hu
  have hu_open : IsOpen u := isOpen_interior
  have hzu : extChartAt I x₀ y ∈ u := mem_interior_iff_mem_nhds.mpr hv
  have hσcu : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 4
      (T% σc) u :=
    hσcv.mono interior_subset
  obtain ⟨ψ, -, hψsupp⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E))
        (extChartAt I x₀ y)).mem_iff.mp (hu_open.mem_nhds hzu))
  set τ : Π z : E, TangentSpace 𝓘(ℝ, E) z := (ψ : E → ℝ) • σc with hτ
  have hτglob : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 4
      (T% τ) :=
    ContMDiffOn.smul_section_of_tsupport
      ((ψ.contMDiff.of_le (by
        rw [show (4 : ℕ∞ω) = ((4 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top)).contMDiffOn)
      hu_open hψsupp hσcu
  haveI hcovC : ContMDiffCovariantDerivative covC 3 :=
    chartLeviCivita_contMDiff χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
      (k := 3) (by
        rw [show (3 : ℕ∞ω) + 1 + 1 = ((5 : ℕ∞) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top) hχ htsupp hg
  have hτhomOn :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 3
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        Set.univ :=
    (ContMDiffCovariantDerivative.contMDiff (cov := covC) (k := 3)).contMDiff
      (σ := τ) hτglob.contMDiffOn
  have hτhomAt :
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) 3
        (fun z : E =>
          (⟨z, covC τ z⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun z : E =>
                TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                  TangentSpace 𝓘(ℝ, E) z)))
        (extChartAt I x₀ y) :=
    hτhomOn.contMDiffAt Filter.univ_mem
  have hτcoord :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 3
        (fun z : E =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z))
        (extChartAt I x₀ y) :=
    (contMDiffAt_hom_bundle
      (fun z : E =>
        (⟨z, covC τ z⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun z : E =>
              TangentSpace 𝓘(ℝ, E) z →L[ℝ]
                TangentSpace 𝓘(ℝ, E) z)))).mp hτhomAt |>.2
  set w : Set E := interior {z | (ψ : E → ℝ) z = 1} ∩ u with hw
  have hw_open : IsOpen w := isOpen_interior.inter hu_open
  have hzw : extChartAt I x₀ y ∈ w :=
    ⟨mem_interior_iff_mem_nhds.mpr ψ.eventuallyEq_one, hzu⟩
  have hστ : ∀ z ∈ interior {z | (ψ : E → ℝ) z = 1}, σc z = τ z := by
    intro z hz
    have h1 : z ∈ {z | (ψ : E → ℝ) z = 1} := interior_subset hz
    have h1eq : (ψ : E → ℝ) z = 1 := by
      simpa using h1
    rw [hτ]
    change σc z = (ψ : E → ℝ) z • σc z
    rw [h1eq]
    simp
  have hev :
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC σc z))
        =ᶠ[𝓝 (extChartAt I x₀ y)]
      (fun z : E =>
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
          E (TangentSpace 𝓘(ℝ, E))
          (extChartAt I x₀ y) z (extChartAt I x₀ y) z (covC τ z)) := by
    filter_upwards [hw_open.mem_nhds hzw] with z hz
    have hσcz : MDiffAt (T% σc) z :=
      ((hσcu z hz.2).contMDiffAt (hu_open.mem_nhds hz.2)).mdifferentiableAt
        (by norm_num)
    have hτz : MDiffAt (T% τ) z :=
      (hτglob z).mdifferentiableAt (by norm_num)
    have hcongr : covC σc z = covC τ z := by
      apply covC.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσcz hτz
        Filter.univ_mem
      filter_upwards [isOpen_interior.mem_nhds hz.1] with z' hz'
      exact hστ z' hz'
    rw [hcongr]
  exact hτcoord.congr_of_eventuallyEq hev

/--
The chart-transported hom section is locally `C²` as a section of the
manifold hom-bundle.
-/
theorem chartTransportedLeviCivitaHom_contMDiffAt₂
    [IsManifold I ∞ M] [I.Boundaryless]
    (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v)
    (g : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (hgpos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 → 0 < g y u u)
    (x₀ : M) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible)
    (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    (hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        y (g y)))
    (σ : Π y : M, TangentSpace I y)
    (hσ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% σ) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y : M =>
        (⟨y,
          chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀
            hχ0 hχ1 hsupp σ y⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun y : M =>
              TangentSpace I y →L[ℝ] TangentSpace I y)))
      x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let covC :=
    chartLeviCivita χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp
  let σc : Π z : E, TangentSpace 𝓘(ℝ, E) z :=
    chartTransportedLeviCivitaSection (I := I) x₀ σ
  have hmodel :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 2
        (fun z =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) z (extChartAt I x₀ x₀) z
            (covC σc z))
        (extChartAt I x₀ x₀) := by
    simpa [covC, σc] using
      chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₂
        (I := I) χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp hχ htsupp hg
        σ (mem_extChartAt_source x₀) hσ
  have hcomp :
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) 2
        (fun y : M =>
          ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (covC σc (extChartAt I x₀ y)))
        x₀ :=
    hmodel.comp x₀ (contMDiffAt_extChartAt (I := I) (n := 2) (x := x₀))
  exact hcomp.congr_of_eventuallyEq (by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with y hy
    have hchart :
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
            x₀ y x₀ y
            (chartTransportedLeviCivitaHom χ G₀ hG₀pos g hgpos x₀
              hχ0 hχ1 hsupp σ y)
          = covC σc (extChartAt I x₀ y) := by
        simpa [covC, σc] using
          chartTransportedLeviCivitaHom_inCoordinates_apply_chart
            (I := I) χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1 hsupp σ hy
    have hmodel_id :
        ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E))
            E (TangentSpace 𝓘(ℝ, E))
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (extChartAt I x₀ x₀) (extChartAt I x₀ y)
            (covC σc (extChartAt I x₀ y))
          = covC σc (extChartAt I x₀ y) :=
        inCoordinates_tangent_bundle_core_model_space
          (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
          (x₀ := extChartAt I x₀ x₀) (x := extChartAt I x₀ y)
          (y₀ := extChartAt I x₀ x₀) (y := extChartAt I x₀ y)
          (ϕ := covC σc (extChartAt I x₀ y))
    exact hchart.trans hmodel_id.symm)

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

namespace LeviCivitaExistence

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
The closed smooth Levi-Civita connection is a `C¹` covariant derivative.

The proof localizes at an arbitrary chart center, globalizes the chart metric
with a bump cutoff, applies the chart-side Levi-Civita regularity theorem, and
then transfers the resulting hom-bundle regularity back to the closed Koszul
connection by germ equality.
-/
@[instance]
theorem closedLeviCivitaConnection_contMDiff
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (closedLeviCivitaConnection g) 1 := by
  haveI : ModelWithCorners.Boundaryless I := by
    infer_instance
  constructor
  constructor
  intro σ hσ
  intro x₀ _
  let G₀ : ClosedSmoothModel n →L[ℝ] ClosedSmoothModel n →L[ℝ] ℝ := innerSL ℝ
  have hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v := by
    intro v hv
    change 0 < ((innerSL ℝ) v) v
    rw [innerSL_apply_apply]
    exact (real_inner_self_pos).2 hv
  have hG₀symm : ∀ v w : E, G₀ v w = G₀ w v := by
    intro v w
    change ((innerSL ℝ) v) w = ((innerSL ℝ) w) v
    rw [innerSL_apply_apply, innerSL_apply_apply]
    exact real_inner_comm w v
  obtain ⟨χ, hχ, hχ0, hχ1, hχsupp, hχone, _hχcanonical⟩ :=
    @CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀
  have hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible := by
    intro z hz
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hz)))
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend :
      ContDiff ℝ 2
        (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀) :=
    CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x₀
      htwo_add_one_le_top hχ hχsupp hg2
  have hbl :
      Differentiable ℝ
        (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀) :=
    hblend.differentiable (by norm_num)
  have hσAt :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) x₀ := by
    simpa using (hσ.contMDiffAt Filter.univ_mem)
  have hσOn :
      ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) Set.univ := by
    simpa using hσ
  have htrans :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun y : M =>
          (⟨y,
            CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos
              g.inner (fun y u hu => g.inner_pos y (v := u) hu)
              x₀ hχ0 hχ1 hsupp σ y⟩ :
            TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        x₀ :=
    CovariantDerivative.chartTransportedLeviCivitaHom_contMDiffAt
      χ G₀ hG₀pos g.inner
      (fun y u hu => g.inner_pos y (v := u) hu)
      x₀ hχ0 hχ1 hsupp hχ hχsupp hg2 σ hσAt
  have hev :
      (fun y : M =>
        (⟨y,
          CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos
            g.inner (fun y u hu => g.inner_pos y (v := u) hu)
            x₀ hχ0 hχ1 hsupp σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        =ᶠ[𝓝 x₀]
      (fun y : M =>
        (⟨y, closedLeviCivitaConnection g σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y))) :=
    LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed
      g χ G₀ hG₀pos x₀ hχ0 hχ1 hsupp hbl hG₀symm hχone hσOn
  have hclosedAt :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 1
        (fun y : M =>
          (⟨y, closedLeviCivitaConnection g σ y⟩ :
            TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        x₀ :=
    htrans.congr_of_eventuallyEq hev.symm
  simpa using hclosedAt.contMDiffWithinAt

/--
The closed smooth Levi-Civita connection is a `C²` covariant derivative.
-/
theorem closedLeviCivitaConnection_contMDiff₂
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (closedLeviCivitaConnection g) 2 := by
  haveI : ModelWithCorners.Boundaryless I := by
    infer_instance
  constructor
  constructor
  intro σ hσ
  intro x₀ _
  let G₀ : ClosedSmoothModel n →L[ℝ] ClosedSmoothModel n →L[ℝ] ℝ := innerSL ℝ
  have hG₀pos : ∀ v : E, v ≠ 0 → 0 < G₀ v v := by
    intro v hv
    change 0 < ((innerSL ℝ) v) v
    rw [innerSL_apply_apply]
    exact (real_inner_self_pos).2 hv
  have hG₀symm : ∀ v w : E, G₀ v w = G₀ w v := by
    intro v w
    change ((innerSL ℝ) v) w = ((innerSL ℝ) w) v
    rw [innerSL_apply_apply, innerSL_apply_apply]
    exact real_inner_comm w v
  obtain ⟨χ, hχ, hχ0, hχ1, hχsupp, hχone, _hχcanonical⟩ :=
    @CovariantDerivative.exists_blending_cutoff E _ _ E _ I M _ _ _ _ _ x₀
  have hsupp : ∀ z, χ z ≠ 0 →
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (Set.range I) z).IsInvertible := by
    intro z hz
    exact isInvertible_mfderivWithin_extChartAt_symm
      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hz)))
  have htwo_le_three : (2 : ℕ∞ω) ≤ (3 : ℕ∞ω) := by
    norm_num
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
              (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le hthree_le_top
  have hblend :
      ContDiff ℝ 3
        (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀) :=
    CovariantDerivative.contDiff_blendedChartMetric χ G₀ g.inner x₀
      hthree_add_one_le_top hχ hχsupp hg3
  have hbl :
      Differentiable ℝ
        (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀) :=
    hblend.differentiable (by norm_num)
  have hσAt :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% σ) x₀ := by
    simpa using (hσ.contMDiffAt Filter.univ_mem)
  have hσOn :
      ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 3 (T% σ) Set.univ := by
    simpa using hσ
  have hσOn2 :
      ContMDiffOn I ((I).prod 𝓘(ℝ, E)) 2 (T% σ) Set.univ :=
    hσOn.of_le htwo_le_three
  have htrans :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun y : M =>
          (⟨y,
            CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos
              g.inner (fun y u hu => g.inner_pos y (v := u) hu)
              x₀ hχ0 hχ1 hsupp σ y⟩ :
            TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        x₀ :=
    CovariantDerivative.chartTransportedLeviCivitaHom_contMDiffAt₂
      χ G₀ hG₀pos g.inner
      (fun y u hu => g.inner_pos y (v := u) hu)
      x₀ hχ0 hχ1 hsupp hχ hχsupp hg3 σ hσAt
  have hev :
      (fun y : M =>
        (⟨y,
          CovariantDerivative.chartTransportedLeviCivitaHom χ G₀ hG₀pos
            g.inner (fun y u hu => g.inner_pos y (v := u) hu)
            x₀ hχ0 hχ1 hsupp σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        =ᶠ[𝓝 x₀]
      (fun y : M =>
        (⟨y, closedLeviCivitaConnection g σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y))) :=
    LeviCivitaTransport.chartTransportedLeviCivitaHom_eventuallyEq_closed
      g χ G₀ hG₀pos x₀ hχ0 hχ1 hsupp hbl hG₀symm hχone hσOn2
  have hclosedAt :
      ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun y : M =>
          (⟨y, closedLeviCivitaConnection g σ y⟩ :
            TotalSpace (E →L[ℝ] E) (fun y : M => TM y →L[ℝ] TM y)))
        x₀ :=
    htrans.congr_of_eventuallyEq hev.symm
  simpa using hclosedAt.contMDiffWithinAt

end LeviCivitaExistence

end Poincare
