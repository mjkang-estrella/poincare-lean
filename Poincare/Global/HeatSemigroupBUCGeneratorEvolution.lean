import Poincare.Global.HeatSemigroupBUCGeneratorCore

/-!
# Evolution of the strong `BUC` heat generator

The strong-generator domain is invariant under the heat semigroup.  Moreover,
an orbit starting in that domain has the expected right derivative at every
nonnegative time.  These are the semigroup-theoretic regularity facts needed
to pass from the initial generator calculation to a classical positive-time
evolution; they use only the proved `BUC` semigroup law.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- The strong generator value at a datum is unique.  Although the defining
derivative is one-sided, the half-line has a unique tangent at its endpoint. -/
theorem IsInBUCHeatGeneratorDomain.unique
    {u Au Av : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au)
    (hv : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Av) :
    Au = Av := by
  have h := (uniqueDiffOn_Ici (0 : ℝ)).eq Set.self_mem_Ici hu hv
  simpa using congrArg (fun L : ℝ →L[ℝ] BUC => L 1) h

/-- The closed strong-generator graph, represented as an actual linear map on
its (dense) domain submodule. -/
noncomputable def bucHeatGenerator :
    bucHeatGeneratorDomain (E := E) (F := F) →ₗ[ℝ] BUC where
  toFun u := Classical.choose u.property
  map_add' u v := by
    have hsum : IsInBUCHeatGeneratorDomain (E := E) (F := F)
        ((u : BUC) + (v : BUC))
        (Classical.choose u.property + Classical.choose v.property) := by
      have h := (Classical.choose_spec u.property).add
        (Classical.choose_spec v.property)
      apply h.congr
      · intro t ht
        simp
      · simp
    apply IsInBUCHeatGeneratorDomain.unique
      (Classical.choose_spec (u + v).property)
    simpa using hsum
  map_smul' c u := by
    have hsmul : IsInBUCHeatGeneratorDomain (E := E) (F := F)
        (c • (u : BUC)) (c • Classical.choose u.property) := by
      have h := (Classical.choose_spec u.property).const_smul c
      apply h.congr
      · intro t ht
        simp
      · simp
    apply IsInBUCHeatGeneratorDomain.unique
      (Classical.choose_spec (c • u).property)
    simpa using hsmul

/-- The chosen linear generator realizes the unique derivative encoded by its
domain membership. -/
theorem bucHeatGenerator_spec
    (u : bucHeatGeneratorDomain (E := E) (F := F)) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F) u
      (bucHeatGenerator (E := E) (F := F) u) :=
  Classical.choose_spec u.property

/-- Any separately supplied generator value agrees with the graph operator. -/
theorem bucHeatGenerator_eq_of_mem
    (u : bucHeatGeneratorDomain (E := E) (F := F)) {Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au) :
    bucHeatGenerator (E := E) (F := F) u = Au :=
  (bucHeatGenerator_spec (E := E) (F := F) u).unique hu

/-- Integration of a heat orbit over a fixed nonnegative interval is a
continuous linear operator on `BUC`. -/
noncomputable def integratedHeatOrbitBUCCLM (ε : ℝ≥0) : BUC →L[ℝ] BUC := by
  let L : BUC →ₗ[ℝ] BUC :=
    { toFun := integratedHeatOrbitBUC ε
      map_add' := by
        intro f g
        have hf : IntervalIntegrable
            (fun s : ℝ =>
              vectorHeatSemigroupBUCExtended (E := E) (F := F) s f)
            volume 0 (ε : ℝ) :=
          (continuous_vectorHeatSemigroupBUCExtended_apply
            (E := E) (F := F) f).intervalIntegrable _ _
        have hg : IntervalIntegrable
            (fun s : ℝ =>
              vectorHeatSemigroupBUCExtended (E := E) (F := F) s g)
            volume 0 (ε : ℝ) :=
          (continuous_vectorHeatSemigroupBUCExtended_apply
            (E := E) (F := F) g).intervalIntegrable _ _
        simpa [integratedHeatOrbitBUC] using
          (intervalIntegral.integral_add hf hg)
      map_smul' := by
        intro c f
        simp [integratedHeatOrbitBUC, intervalIntegral.integral_smul] }
  refine L.mkContinuous (ε : ℝ) ?_
  intro f
  have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) (ε : ℝ),
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) s f‖ ≤ ‖f‖ := by
    intro s hs
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) s f‖ ≤
          ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) s‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f‖ := by
        gcongr
        exact vectorHeatSemigroupBUCExtended_c0_contracting
          (E := E) (F := F) |>.2.2.2 s
      _ = ‖f‖ := one_mul _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  change ‖integratedHeatOrbitBUC ε f‖ ≤ (ε : ℝ) * ‖f‖
  simpa [integratedHeatOrbitBUC, abs_of_nonneg ε.property, mul_comm] using hnorm

@[simp]
theorem integratedHeatOrbitBUCCLM_apply (ε : ℝ≥0) (f : BUC) :
    integratedHeatOrbitBUCCLM (E := E) (F := F) ε f =
      integratedHeatOrbitBUC ε f :=
  by simp [integratedHeatOrbitBUCCLM, LinearMap.mkContinuous_apply]

/-- The strong heat-generator domain is invariant under every nonnegative
heat-semigroup time, and the generator value evolves by the same semigroup. -/
theorem IsInBUCHeatGeneratorDomain.semigroup
    {u Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au)
    {t : ℝ} (ht : 0 ≤ t) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t u)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t Au) := by
  let Ht : BUC →L[ℝ] BUC :=
    vectorHeatSemigroupBUCExtended (E := E) (F := F) t
  have hcomp : HasDerivWithinAt
      (fun h : ℝ => Ht
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) h u))
      (Ht Au) (Set.Ici 0) 0 :=
    Ht.hasFDerivAt.comp_hasDerivWithinAt 0 hu
  apply hcomp.congr
  · intro h hh
    calc
      vectorHeatSemigroupBUCExtended (E := E) (F := F) h (Ht u) =
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (h + t) u :=
        vectorHeatSemigroupBUCExtended_add_apply
          (E := E) (F := F) hh ht u
      _ = vectorHeatSemigroupBUCExtended (E := E) (F := F) (t + h) u := by
        rw [add_comm]
      _ = Ht (vectorHeatSemigroupBUCExtended (E := E) (F := F) h u) :=
        (vectorHeatSemigroupBUCExtended_add_apply
          (E := E) (F := F) ht hh u).symm
  · change vectorHeatSemigroupBUCExtended (E := E) (F := F) 0 (Ht u) =
      Ht (vectorHeatSemigroupBUCExtended (E := E) (F := F) 0 u)
    simp [vectorHeatSemigroupBUCExtended]

/-- The heat semigroup lifted to the strong-generator domain. -/
noncomputable def bucHeatSemigroupOnGeneratorDomain
    (t : ℝ) (ht : 0 ≤ t) :
    bucHeatGeneratorDomain (E := E) (F := F) →ₗ[ℝ]
      bucHeatGeneratorDomain (E := E) (F := F) where
  toFun u :=
    ⟨vectorHeatSemigroupBUCExtended (E := E) (F := F) t u,
      ⟨vectorHeatSemigroupBUCExtended (E := E) (F := F) t
          (bucHeatGenerator (E := E) (F := F) u),
        (bucHeatGenerator_spec (E := E) (F := F) u).semigroup ht⟩⟩
  map_add' u v := by
    apply Subtype.ext
    simp
  map_smul' c u := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_bucHeatSemigroupOnGeneratorDomain
    (t : ℝ) (ht : 0 ≤ t)
    (u : bucHeatGeneratorDomain (E := E) (F := F)) :
    (bucHeatSemigroupOnGeneratorDomain (E := E) (F := F) t ht u : BUC) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t u :=
  rfl

/-- On its invariant domain, the strong generator commutes with the heat
semigroup. -/
theorem bucHeatGenerator_semigroup_commute
    (t : ℝ) (ht : 0 ≤ t)
    (u : bucHeatGeneratorDomain (E := E) (F := F)) :
    bucHeatGenerator (E := E) (F := F)
        (bucHeatSemigroupOnGeneratorDomain (E := E) (F := F) t ht u) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t
        (bucHeatGenerator (E := E) (F := F) u) := by
  apply bucHeatGenerator_eq_of_mem
  exact (bucHeatGenerator_spec (E := E) (F := F) u).semigroup ht

/-- A heat orbit starting in the strong generator domain has right derivative
`H_t Au` at every nonnegative time `t`. -/
theorem IsInBUCHeatGeneratorDomain.hasDerivWithinAt_semigroup_orbit
    {u Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s : ℝ => vectorHeatSemigroupBUCExtended (E := E) (F := F) s u)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t Au)
      (Set.Ici t) t := by
  let shift : ℝ → ℝ := fun s => s - t
  have hshift : HasDerivWithinAt shift 1 (Set.Ici t) t := by
    simpa [shift] using
      ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hmaps : MapsTo shift (Set.Ici t) (Set.Ici 0) := by
    intro s hs
    change t ≤ s at hs
    exact sub_nonneg.mpr hs
  have hu' : HasDerivWithinAt
      (fun h : ℝ => vectorHeatSemigroupBUCExtended (E := E) (F := F) h u)
      Au (Set.Ici 0) 0 := hu
  have htranslated : HasDerivWithinAt
      (fun s : ℝ =>
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (shift s) u)
      Au (Set.Ici t) t := by
    simpa [Function.comp_def] using
      hu'.scomp_of_eq t hshift hmaps (by simp [shift])
  let Ht : BUC →L[ℝ] BUC :=
    vectorHeatSemigroupBUCExtended (E := E) (F := F) t
  have hcomposed : HasDerivWithinAt
      (fun s : ℝ => Ht
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (shift s) u))
      (Ht Au) (Set.Ici t) t :=
    Ht.hasFDerivAt.comp_hasDerivWithinAt t htranslated
  apply hcomposed.congr
  · intro s hs
    have hst : 0 ≤ s - t := sub_nonneg.mpr hs
    rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) ht hst u]
    simp
  · rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) ht (sub_nonneg.mpr (le_refl t)) u]
    simp

/-- Integrated orbit equation for a strong-generator datum.  This is the
closed-graph identity underlying the abstract heat equation `u' = Au`. -/
theorem IsInBUCHeatGeneratorDomain.integral_semigroup_eq_sub
    {u Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s : ℝ in (0 : ℝ)..t,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) s Au) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t u - u := by
  let orbitU : ℝ → BUC := fun s =>
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s u
  let orbitAu : ℝ → BUC := fun s =>
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s Au
  have hcontU : Continuous orbitU :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) u
  have hcontAu : Continuous orbitAu :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) Au
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt orbitU (orbitAu s) (Set.Ioi s) s := by
    intro s hs
    exact (hu.hasDerivWithinAt_semigroup_orbit hs.1.le).mono
      Set.Ioi_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    hcontU.continuousOn hderiv (hcontAu.intervalIntegrable 0 t)
  simpa [orbitU, orbitAu, vectorHeatSemigroupBUCExtended] using h

/-- Conversely, the integrated orbit equation characterizes membership in the
strong generator graph. -/
theorem isInBUCHeatGeneratorDomain_of_integral_semigroup_eq_sub
    {u Au : BUC}
    (hidentity : ∀ {t : ℝ}, 0 ≤ t →
      (∫ s : ℝ in (0 : ℝ)..t,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) s Au) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t u - u) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au := by
  let orbitAu : ℝ → BUC := fun s =>
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s Au
  have hcontAu : Continuous orbitAu :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) Au
  have hint : HasDerivAt
      (fun t : ℝ => ∫ s : ℝ in (0 : ℝ)..t, orbitAu s) Au 0 := by
    simpa [orbitAu, vectorHeatSemigroupBUCExtended] using
      (hcontAu.integral_hasStrictDerivAt (0 : ℝ) 0).hasDerivAt
  have hsum : HasDerivWithinAt
      (fun t : ℝ => u + ∫ s : ℝ in (0 : ℝ)..t, orbitAu s)
      Au (Set.Ici 0) 0 := by
    exact hint.hasDerivWithinAt.const_add u
  apply hsum.congr
  · intro t ht
    change 0 ≤ t at ht
    rw [hidentity ht]
    simp
  · simp [orbitAu, vectorHeatSemigroupBUCExtended]

/-- The strong heat-generator graph is sequentially closed: simultaneous
strong limits of graph data remain in the graph. -/
theorem isInBUCHeatGeneratorDomain_of_tendsto
    (u Au : ℕ → BUC) {uLim AuLim : BUC}
    (hgraph : ∀ n, IsInBUCHeatGeneratorDomain (E := E) (F := F) (u n) (Au n))
    (hu : Tendsto u atTop (𝓝 uLim))
    (hAu : Tendsto Au atTop (𝓝 AuLim)) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F) uLim AuLim := by
  apply isInBUCHeatGeneratorDomain_of_integral_semigroup_eq_sub
  intro t ht
  let ε : ℝ≥0 := ⟨t, ht⟩
  let J : BUC →L[ℝ] BUC :=
    integratedHeatOrbitBUCCLM (E := E) (F := F) ε
  let Ht : BUC →L[ℝ] BUC :=
    vectorHeatSemigroupBUCExtended (E := E) (F := F) t
  have hleft : Tendsto (fun n => J (Au n)) atTop (𝓝 (J AuLim)) :=
    J.continuous.continuousAt.tendsto.comp hAu
  have hright : Tendsto (fun n => Ht (u n) - u n) atTop
      (𝓝 (Ht uLim - uLim)) :=
    (Ht.continuous.continuousAt.tendsto.comp hu).sub hu
  have heq : (fun n => J (Au n)) = (fun n => Ht (u n) - u n) := by
    funext n
    have hn := (hgraph n).integral_semigroup_eq_sub ht
    simpa [J, Ht, ε, integratedHeatOrbitBUC] using hn
  rw [heq] at hleft
  have hlimit : J AuLim = Ht uLim - uLim := tendsto_nhds_unique hleft hright
  simpa [J, Ht, ε, integratedHeatOrbitBUC] using hlimit

/-- The graph relation of the strong `BUC` heat generator. -/
def bucHeatGeneratorGraph : Set (BUC × BUC) :=
  {p | IsInBUCHeatGeneratorDomain (E := E) (F := F) p.1 p.2}

/-- The strong `BUC` heat generator is a closed densely-defined linear
operator, in the precise sense that its graph is a closed subset of
`BUC × BUC`. -/
theorem isClosed_bucHeatGeneratorGraph :
    IsClosed (bucHeatGeneratorGraph (E := E) (F := F)) := by
  apply IsSeqClosed.isClosed
  intro p pLim hp hlim
  have hfst : Tendsto (fun n => (p n).1) atTop (𝓝 pLim.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hsnd : Tendsto (fun n => (p n).2) atTop (𝓝 pLim.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  exact isInBUCHeatGeneratorDomain_of_tendsto
    (E := E) (F := F) (fun n => (p n).1) (fun n => (p n).2)
      (fun n => hp n) hfst hsnd

/-- For generator-domain data, the explicit generator of a normalized
integrated orbit is itself the normalized integrated orbit of the generator. -/
theorem normalizedIntegratedHeatOrbitBUC_generator_eq
    {u Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au)
    (ε : ℝ≥0) :
    ((ε : ℝ)⁻¹) •
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) u - u) =
      normalizedIntegratedHeatOrbitBUC ε Au := by
  calc
    ((ε : ℝ)⁻¹) •
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) u - u) =
        ((ε : ℝ)⁻¹) • integratedHeatOrbitBUC ε Au := by
      exact congrArg (fun z : BUC => ((ε : ℝ)⁻¹) • z)
        (hu.integral_semigroup_eq_sub ε.property).symm
    _ = normalizedIntegratedHeatOrbitBUC ε Au := rfl

/-- Normalized integrated orbits approximate every generator graph point in
the product (graph-norm) topology. -/
theorem tendsto_normalizedIntegratedHeatOrbitBUC_generator_graph
    {u Au : BUC}
    (hu : IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au) :
    Tendsto
      (fun ε : ℝ≥0 =>
        (normalizedIntegratedHeatOrbitBUC ε u,
          ((ε : ℝ)⁻¹) •
            (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) u - u)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (u, Au)) := by
  have hfirst := tendsto_normalizedIntegratedHeatOrbitBUC_zero
    (E := E) (F := F) u
  have hsecond := tendsto_normalizedIntegratedHeatOrbitBUC_zero
    (E := E) (F := F) Au
  rw [nhds_prod_eq]
  apply hfirst.prodMk
  apply hsecond.congr'
  exact Eventually.of_forall fun ε =>
    (normalizedIntegratedHeatOrbitBUC_generator_eq
      (E := E) (F := F) hu ε).symm

/-- The concrete normalized integrated-orbit graph core. -/
def normalizedIntegratedHeatGeneratorCoreGraph : Set (BUC × BUC) :=
  {p | ∃ (ε : ℝ≥0) (f : BUC), 0 < ε ∧
    p = (normalizedIntegratedHeatOrbitBUC ε f,
      ((ε : ℝ)⁻¹) •
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f))}

/-- Every concrete integrated-orbit core point belongs to the strong
generator graph. -/
theorem normalizedIntegratedHeatGeneratorCoreGraph_subset_generatorGraph :
    normalizedIntegratedHeatGeneratorCoreGraph (E := E) (F := F) ⊆
      bucHeatGeneratorGraph (E := E) (F := F) := by
  rintro p ⟨ε, f, hε, rfl⟩
  exact normalizedIntegratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε f

/-- The integrated-orbit graph core is dense in the full strong-generator
graph: every graph point lies in its ambient closure. -/
theorem bucHeatGeneratorGraph_subset_closure_integratedCore :
    bucHeatGeneratorGraph (E := E) (F := F) ⊆
      closure (normalizedIntegratedHeatGeneratorCoreGraph (E := E) (F := F)) := by
  intro p hp
  refine mem_closure_of_tendsto
    (tendsto_normalizedIntegratedHeatOrbitBUC_generator_graph
      (E := E) (F := F) hp) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ⟨ε, p.1, hε, rfl⟩

/-- Exact graph-core theorem: closing the normalized integrated-orbit graph
recovers the full strong heat-generator graph. -/
theorem closure_normalizedIntegratedHeatGeneratorCoreGraph_eq :
    closure (normalizedIntegratedHeatGeneratorCoreGraph (E := E) (F := F)) =
      bucHeatGeneratorGraph (E := E) (F := F) := by
  apply Set.Subset.antisymm
  · exact closure_minimal
      (normalizedIntegratedHeatGeneratorCoreGraph_subset_generatorGraph
        (E := E) (F := F))
      (isClosed_bucHeatGeneratorGraph (E := E) (F := F))
  · exact bucHeatGeneratorGraph_subset_closure_integratedCore
      (E := E) (F := F)

/-- Every integrated heat orbit is therefore a classical right solution along
its full nonnegative semigroup orbit, with the explicit generator value. -/
theorem integratedHeatOrbitBUC_hasDerivWithinAt_semigroup_orbit
    (ε : ℝ≥0) (f : BUC) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s : ℝ => vectorHeatSemigroupBUCExtended (E := E) (F := F) s
        (integratedHeatOrbitBUC ε f))
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f))
      (Set.Ici t) t :=
  (integratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε f).hasDerivWithinAt_semigroup_orbit ht

end Poincare
