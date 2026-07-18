import Poincare.Global.SemilinearHeatBUCFixedPointRegularity
import Poincare.Global.HeatSemigroupBUCC0

/-!
# A concrete strong-generator core for the `BUC` heat semigroup

For every `BUC` datum `f` and every positive `ε`, the integrated heat orbit

`v = ∫₀ᵋ H_s f ds`

belongs to the strong generator domain, with generator value `H_ε f - f`.
This is the standard integrated-semigroup core construction and gives a large
honest family of initial data for the mild-to-classical upgrade without
assuming spatial derivatives of an arbitrary `BUC` function.  Normalizing
these integrated orbits by `ε⁻¹` gives approximants converging to every `BUC`
datum, so the resulting strong generator domain is a dense linear subspace.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Integral of a heat orbit over a finite initial time interval. -/
def integratedHeatOrbitBUC (ε : ℝ≥0) (f : BUC) : BUC :=
  ∫ s : ℝ in (0 : ℝ)..(ε : ℝ),
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s f

/-- Semigroup action on an integrated orbit is a difference of two heat-orbit
primitives. -/
theorem vectorHeatSemigroupBUCExtended_integratedHeatOrbit_eq
    (ε : ℝ≥0) (f : BUC) {h : ℝ} (hh : 0 ≤ h) :
    vectorHeatSemigroupBUCExtended (E := E) (F := F) h
        (integratedHeatOrbitBUC ε f) =
      (∫ s : ℝ in (0 : ℝ)..((ε : ℝ) + h),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) s f) -
        ∫ s : ℝ in (0 : ℝ)..h,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) s f := by
  let orbit : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s f
  have horbit : Continuous orbit :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) f
  have hint : IntervalIntegrable orbit volume (0 : ℝ) (ε : ℝ) :=
    horbit.intervalIntegrable _ _
  calc
    vectorHeatSemigroupBUCExtended (E := E) (F := F) h
        (integratedHeatOrbitBUC ε f) =
        ∫ s : ℝ in (0 : ℝ)..(ε : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) h (orbit s) := by
      rw [integratedHeatOrbitBUC]
      exact (ContinuousLinearMap.intervalIntegral_comp_comm
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) h) hint).symm
    _ = ∫ s : ℝ in (0 : ℝ)..(ε : ℝ), orbit (h + s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by
        simpa [min_eq_left ε.property] using hs.1
      exact vectorHeatSemigroupBUCExtended_add_apply
        (E := E) (F := F) hh hs0 f
    _ = ∫ s : ℝ in h..(h + (ε : ℝ)), orbit s := by
      simpa using
        (intervalIntegral.integral_comp_add_left
          (a := (0 : ℝ)) (b := (ε : ℝ)) orbit h)
    _ = (∫ s : ℝ in (0 : ℝ)..((ε : ℝ) + h), orbit s) -
        ∫ s : ℝ in (0 : ℝ)..h, orbit s := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (horbit.intervalIntegrable (0 : ℝ) h)
        (horbit.intervalIntegrable h ((ε : ℝ) + h))
      rw [add_comm h (ε : ℝ)]
      have hadd' :
          (∫ s : ℝ in h..((ε : ℝ) + h), orbit s ∂volume) +
              ∫ s : ℝ in (0 : ℝ)..h, orbit s ∂volume =
            ∫ s : ℝ in (0 : ℝ)..((ε : ℝ) + h), orbit s ∂volume := by
        simpa only [add_comm] using hadd
      exact eq_sub_of_add_eq hadd'

/-- Every positive-length integrated heat orbit lies in the strong generator
domain with generator `H_ε f - f`. -/
theorem integratedHeatOrbitBUC_mem_heatGeneratorDomain
    (ε : ℝ≥0) (f : BUC) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (integratedHeatOrbitBUC ε f)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f) := by
  let orbit : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s f
  let P : ℝ → BUC := fun t ↦ ∫ s : ℝ in (0 : ℝ)..t, orbit s
  have horbit : Continuous orbit :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) f
  have hPε : HasDerivAt P (orbit (ε : ℝ)) (ε : ℝ) := by
    simpa [P] using (horbit.integral_hasStrictDerivAt (0 : ℝ) (ε : ℝ)).hasDerivAt
  have hshift : HasDerivAt (fun h : ℝ ↦ P ((ε : ℝ) + h))
      (orbit (ε : ℝ)) 0 := by
    have hinner : HasDerivAt (fun h : ℝ ↦ (ε : ℝ) + h) 1 0 := by
      simpa using
        ((hasDerivAt_const (0 : ℝ) (ε : ℝ)).add (hasDerivAt_id (0 : ℝ)))
    have hPε' : HasDerivAt P (orbit (ε : ℝ)) ((ε : ℝ) + 0) := by
      simpa using hPε
    simpa [Function.comp_def] using hPε'.scomp 0 hinner
  have hP0 : HasDerivAt P (orbit 0) 0 := by
    simpa [P] using (horbit.integral_hasStrictDerivAt (0 : ℝ) 0).hasDerivAt
  have hdiff : HasDerivAt (fun h : ℝ ↦ P ((ε : ℝ) + h) - P h)
      (orbit (ε : ℝ) - orbit 0) 0 := hshift.sub hP0
  have hwithin := hdiff.hasDerivWithinAt (s := Set.Ici (0 : ℝ))
  have hcongr : HasDerivWithinAt
      (fun h : ℝ ↦ vectorHeatSemigroupBUCExtended (E := E) (F := F) h
        (integratedHeatOrbitBUC ε f))
      (orbit (ε : ℝ) - orbit 0) (Set.Ici 0) 0 := by
    apply hwithin.congr
    · intro h hh
      simpa [P] using
        (vectorHeatSemigroupBUCExtended_integratedHeatOrbit_eq
          (E := E) (F := F) ε f hh)
    · simpa [P] using
        (vectorHeatSemigroupBUCExtended_integratedHeatOrbit_eq
          (E := E) (F := F) ε f (le_refl 0))
  simpa [IsInBUCHeatGeneratorDomain, orbit, vectorHeatSemigroupBUCExtended] using hcongr

/-- The normalized initial-orbit average.  Its value at `ε = 0` is set to zero
by the usual convention `0⁻¹ = 0`; only its positive-time limit is used. -/
def normalizedIntegratedHeatOrbitBUC (ε : ℝ≥0) (f : BUC) : BUC :=
  ((ε : ℝ)⁻¹) • integratedHeatOrbitBUC ε f

/-- The normalized integrated heat orbits converge strongly to their datum as
the averaging length tends to zero through positive values. -/
theorem tendsto_normalizedIntegratedHeatOrbitBUC_zero
    (f : BUC) :
    Tendsto
      (fun ε : ℝ≥0 ↦ normalizedIntegratedHeatOrbitBUC ε f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds f) := by
  let orbit : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) s f
  let P : ℝ → BUC := fun t ↦ ∫ s : ℝ in (0 : ℝ)..t, orbit s
  have horbit : Continuous orbit :=
    continuous_vectorHeatSemigroupBUCExtended_apply (E := E) (F := F) f
  have hP0 : HasDerivAt P f 0 := by
    have h := (horbit.integral_hasStrictDerivAt (0 : ℝ) 0).hasDerivAt
    simpa [P, orbit, vectorHeatSemigroupBUCExtended] using h
  have hreal :
      Tendsto (fun ε : ℝ ↦ ε⁻¹ • (P (0 + ε) - P 0))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds f) :=
    hP0.tendsto_slope_zero_right
  have hcoe :
      Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [Tendsto, NNReal.map_coe_nhdsGT]
    simp
  have h := hreal.comp hcoe
  simpa [normalizedIntegratedHeatOrbitBUC, integratedHeatOrbitBUC, P] using h

/-- The strong heat-generator domain, forgetting the generator value, is a
linear subspace of `BUC`. -/
def bucHeatGeneratorDomain : Submodule ℝ BUC where
  carrier := {u | ∃ Au, IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simpa [IsInBUCHeatGeneratorDomain] using
      (hasDerivWithinAt_const (x := (0 : ℝ)) (c := (0 : BUC))
        (s := Set.Ici (0 : ℝ)))
  add_mem' := by
    rintro u v ⟨Au, hu⟩ ⟨Av, hv⟩
    refine ⟨Au + Av, ?_⟩
    simpa only [IsInBUCHeatGeneratorDomain, map_add] using hu.add hv
  smul_mem' := by
    rintro c u ⟨Au, hu⟩
    refine ⟨c • Au, ?_⟩
    simpa only [IsInBUCHeatGeneratorDomain, map_smul] using hu.const_smul c

@[simp]
theorem mem_bucHeatGeneratorDomain_iff {u : BUC} :
    u ∈ bucHeatGeneratorDomain (E := E) (F := F) ↔
      ∃ Au, IsInBUCHeatGeneratorDomain (E := E) (F := F) u Au :=
  Iff.rfl

/-- Every normalized integrated orbit belongs to the strong generator domain,
with the correspondingly normalized generator value. -/
theorem normalizedIntegratedHeatOrbitBUC_mem_heatGeneratorDomain
    (ε : ℝ≥0) (f : BUC) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (normalizedIntegratedHeatOrbitBUC ε f)
      (((ε : ℝ)⁻¹) •
        (vectorHeatSemigroupBUCExtended (E := E) (F := F) (ε : ℝ) f - f)) := by
  have h := integratedHeatOrbitBUC_mem_heatGeneratorDomain
    (E := E) (F := F) ε f
  simpa only [normalizedIntegratedHeatOrbitBUC,
    IsInBUCHeatGeneratorDomain, map_smul] using h.const_smul ((ε : ℝ)⁻¹)

/-- The strong heat-generator domain is dense in `BUC`.  The approximants are
the normalized integrated heat orbits above. -/
theorem dense_bucHeatGeneratorDomain :
    Dense (bucHeatGeneratorDomain (E := E) (F := F) : Set BUC) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  refine mem_closure_of_tendsto
    (tendsto_normalizedIntegratedHeatOrbitBUC_zero
      (E := E) (F := F) f) ?_
  exact Eventually.of_forall fun ε ↦
    (mem_bucHeatGeneratorDomain_iff (E := E) (F := F)).2
      ⟨_, normalizedIntegratedHeatOrbitBUC_mem_heatGeneratorDomain
        (E := E) (F := F) ε f⟩

end Poincare
