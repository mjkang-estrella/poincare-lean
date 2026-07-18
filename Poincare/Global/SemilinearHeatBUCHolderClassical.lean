import Poincare.Global.HeatDuhamelBUCGeneratorHolderContinuity
import Poincare.Global.SemilinearHeatBUCTwoSidedInteriorRegularity

/-!
# Classical interior regularity from Hölder forcing

For a semilinear heat fixed point, write the forcing as the globally clamped
path

`G(t) = N(u(proj_[0,T] t))`.

At every positive time, the homogeneous heat orbit is in the strong heat
generator domain.  If `G` is uniformly Hölder on `[0,b]`, the Duhamel term is
also in that domain, and its selected generator value is continuous on every
`[a,b]` with `a > 0`.  Adding the two graph witnesses supplies exactly the
continuous generator family required by the right-to-two-sided regularity
theorem.  The conclusion remains restricted to strict interior times.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction BigOperators

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- The forcing path of a semilinear fixed point, extended to all real times
by projection onto its compact existence interval. -/
def semilinearHeatBUCProjectedForcing
    (T : ℝ≥0) (N : BUC → BUC) (u : DuhamelPath T BUC) (t : ℝ) : BUC :=
  N (u (Set.projIcc 0 (T : ℝ) T.property t))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
@[simp]
theorem semilinearHeatBUCProjectedForcing_apply
    (T : ℝ≥0) (N : BUC → BUC) (u : DuhamelPath T BUC) (t : ℝ) :
    semilinearHeatBUCProjectedForcing T N u t =
      N (u (Set.projIcc 0 (T : ℝ) T.property t)) :=
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- The projected forcing is continuous whenever the nonlinearity is. -/
theorem continuous_semilinearHeatBUCProjectedForcing
    (T : ℝ≥0) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) :
    Continuous (semilinearHeatBUCProjectedForcing T N u) := by
  exact hN.comp
    (u.continuous.comp (continuous_projIcc (h := T.property)))

/-- Canonical positive-time generator value for a semilinear mild path: the
generator of the homogeneous heat orbit plus the selected generator of its
Duhamel term. -/
def semilinearHeatBUCInteriorGeneratorValue
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC)
    (u : DuhamelPath T BUC) (t : ℝ) : BUC :=
  vectorHeatTimeDerivativeBUC (E := E) (F := F) t u₀ +
    heatDuhamelBUCGeneratorValue (E := E) (F := F)
      (semilinearHeatBUCProjectedForcing T N u) t

/-- A uniform endpoint Hölder estimate on the projected forcing constructs a
strong heat-generator graph witness for the current semilinear state.  No
pointwise generator-domain premise on that state is assumed. -/
theorem semilinearHeatBUCFixedPoint_mem_heatGeneratorDomain_of_forcing_holder
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    {t K α : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) (T : ℝ))
    (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖semilinearHeatBUCProjectedForcing T N u s -
          semilinearHeatBUCProjectedForcing T N u t‖ ≤
        K * |t - s| ^ α) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (u (Set.projIcc 0 (T : ℝ) T.property t))
      (semilinearHeatBUCInteriorGeneratorValue
        (E := E) (F := F) T u₀ N u t) := by
  let G : ℝ → BUC := semilinearHeatBUCProjectedForcing T N u
  let τ : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, ⟨ht.1.le, ht.2⟩⟩
  have hproj : Set.projIcc 0 (T : ℝ) T.property t = τ :=
    Set.projIcc_of_mem T.property ⟨ht.1.le, ht.2⟩
  have hG : Continuous G := by
    exact continuous_semilinearHeatBUCProjectedForcing T N hN u
  have hlinear :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) ht.1 u₀
  have hduhamel := heatDuhamelBUC_mem_heatGeneratorDomain_of_holder
    (E := E) (F := F) hG ht.1 hK hα (by
      simpa only [G] using hholder)
  have hmild := congrArg (fun w : DuhamelPath T BUC ↦ w τ) hu
  have hstate : u τ =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ +
        ∫ s : ℝ in (0 : ℝ)..t,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
            (G s) := by
    simpa only [semilinearHeatBUCPicard_apply, τ, G,
      semilinearHeatBUCProjectedForcing] using hmild.symm
  rw [hproj, hstate]
  simpa only [semilinearHeatBUCInteriorGeneratorValue, G,
    IsInBUCHeatGeneratorDomain, map_add] using
    hlinear.add hduhamel

/-- On a compact interval separated from zero, the constructed generator
values of a semilinear mild path are continuous under one uniform endpoint
Hölder hypothesis on its projected forcing. -/
theorem continuousOn_semilinearHeatBUCInteriorGeneratorValue_of_uniformHolder
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) {a b K α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ t ∈ Set.Icc a b,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖semilinearHeatBUCProjectedForcing T N u s -
            semilinearHeatBUCProjectedForcing T N u t‖ ≤
          K * |t - s| ^ α) :
    ContinuousOn
      (semilinearHeatBUCInteriorGeneratorValue
        (E := E) (F := F) T u₀ N u)
      (Set.Icc a b) := by
  have hlinear := continuousOn_vectorHeatTimeDerivativeBUC_Icc
    (E := E) (F := F) u₀ ha (b := b)
  have hduhamel :=
    continuousOn_heatDuhamelBUCGeneratorValue_of_uniformHolder
      (E := E) (F := F)
      (continuous_semilinearHeatBUCProjectedForcing T N hN u)
      ha hab hK hα hholder
  simpa only [semilinearHeatBUCInteriorGeneratorValue] using
    hlinear.add hduhamel

/-- A semilinear heat fixed point with uniformly endpoint-Hölder projected
forcing is classical at every strict time in `(a,b)`, for `0 < a ≤ b ≤ T`.
This theorem discharges both the pointwise generator-graph witnesses and
continuity of the chosen generator path required by the abstract two-sided
regularity layer. -/
theorem semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_uniformHolder_forcing
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    {a b K α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbT : b ≤ (T : ℝ)) (hK : 0 ≤ K) (hα : 0 < α)
    (hholder : ∀ t ∈ Set.Icc a b,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖semilinearHeatBUCProjectedForcing T N u s -
            semilinearHeatBUCProjectedForcing T N u t‖ ≤
          K * |t - s| ^ α) :
    ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (fun r : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property r))
        (semilinearHeatBUCInteriorGeneratorValue
            (E := E) (F := F) T u₀ N u t +
          semilinearHeatBUCProjectedForcing T N u t) t := by
  let path : ℝ → BUC := fun r ↦
    u (Set.projIcc 0 (T : ℝ) T.property r)
  let G : ℝ → BUC := semilinearHeatBUCProjectedForcing T N u
  let A : ℝ → BUC :=
    semilinearHeatBUCInteriorGeneratorValue
      (E := E) (F := F) T u₀ N u
  let velocity : ℝ → BUC := fun r ↦ A r + G r
  have hpath : Continuous path :=
    u.continuous.comp (continuous_projIcc (h := T.property))
  have hG : Continuous G := by
    exact continuous_semilinearHeatBUCProjectedForcing T N hN u
  have hA : ContinuousOn A (Set.Icc a b) := by
    exact continuousOn_semilinearHeatBUCInteriorGeneratorValue_of_uniformHolder
      (E := E) (F := F) T u₀ N hN u ha hab hK hα hholder
  have hvelocity : ContinuousOn velocity (Set.Icc a b) :=
    hA.add hG.continuousOn
  have hright : ∀ s ∈ Set.Ico a b,
      HasDerivWithinAt path (velocity s) (Set.Ici s) s := by
    intro s hs
    have hspos : 0 < s := ha.trans_le hs.1
    have hsT : s < (T : ℝ) := hs.2.trans_le hbT
    let σ : Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨s, ⟨hspos.le, hsT.le⟩⟩
    have hproj : Set.projIcc 0 (T : ℝ) T.property s = σ :=
      Set.projIcc_of_mem T.property ⟨hspos.le, hsT.le⟩
    have hgraph : IsInBUCHeatGeneratorDomain (E := E) (F := F)
        (u σ) (A s) := by
      have hendpoint : ∀ r ∈ Set.Icc (0 : ℝ) s,
          ‖semilinearHeatBUCProjectedForcing T N u r -
              semilinearHeatBUCProjectedForcing T N u s‖ ≤
            K * |s - r| ^ α := by
        intro r hr
        exact hholder s ⟨hs.1, hs.2.le⟩ r hr
      simpa only [A, hproj, σ] using
        semilinearHeatBUCFixedPoint_mem_heatGeneratorDomain_of_forcing_holder
          (E := E) (F := F) T u₀ N hN u hu
          (t := s) ⟨hspos, hsT.le⟩ hK hα hendpoint
    have hderiv :=
      semilinearHeatBUCFixedPoint_hasDerivWithinAt_interior_right
        (E := E) (F := F) T u₀ N hN u hu σ hsT (A s) hgraph
    simpa only [path, velocity, G, semilinearHeatBUCProjectedForcing,
      hproj, σ] using hderiv
  intro t ht
  simpa only [path, velocity, A, G] using
    hasDerivAt_of_continuousOn_rightDerivative
      hab path velocity hpath.continuousOn hvelocity hright ht

end Poincare
