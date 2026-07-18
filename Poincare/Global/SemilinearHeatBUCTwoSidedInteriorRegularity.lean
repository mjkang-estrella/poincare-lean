import Poincare.Global.SemilinearHeatBUCInteriorRegularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Two-sided interior regularity from continuous right derivatives

A continuous Banach-valued path on `[a,b]` whose right derivative is a
continuous field on `[a,b]` is differentiable relative to the whole closed
interval, and hence genuinely two-sided differentiable at every point of
`(a,b)`.

The proof clamps the derivative field to `[a,b]`, integrates that globally
continuous extension, and compares the resulting primitive with the original
path using `eq_of_has_deriv_right_eq`.  This also recovers the left derivative
at `b`; no left derivative is assumed.

For a semilinear heat fixed point, the preceding right-derivative theorem
supplies the hypotheses once the current state has a heat-generator graph
witness at each time in `[0,T)`.  Continuity of the chosen generator values
then upgrades the mild path to an ordinary differentiable path on `(0,T)`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction BigOperators

namespace Poincare

section ContinuousRightDerivative

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A continuous field of right derivatives on a compact interval determines
the derivative relative to the entire interval.  In particular, the value of
the continuous derivative field at the right endpoint is recovered as a left
derivative there.

The comparison path is
`f a + ∫ s in a..t, IccExtend hab f' s`.  Its derivative is the clamped
continuous extension of `f'`; `eq_of_has_deriv_right_eq` identifies it with
`f` on `[a,b]`. -/
theorem hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
    {a b : ℝ} (hab : a ≤ b) (f f' : ℝ → X)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContinuousOn f' (Set.Icc a b))
    (hright : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt f (f' t) (Set.Ici t) t) :
    ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt f (f' t) (Set.Icc a b) t := by
  let f'ext : ℝ → X :=
    Set.IccExtend hab (fun t : Set.Icc a b ↦ f' (t : ℝ))
  have hf'ext : Continuous f'ext := by
    exact (continuousOn_iff_continuous_restrict.mp hf').Icc_extend'
  have hf'ext_eq (t : ℝ) (ht : t ∈ Set.Icc a b) : f'ext t = f' t := by
    change f' (Set.projIcc a b hab t) = f' t
    rw [Set.projIcc_of_mem hab ht]
  let g : ℝ → X := fun t ↦
    f a + ∫ s : ℝ in a..t, f'ext s
  have hgderiv (t : ℝ) : HasDerivAt g (f'ext t) t := by
    have hint : HasDerivAt
        (fun r : ℝ ↦ ∫ s : ℝ in a..r, f'ext s) (f'ext t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hf'ext.intervalIntegrable a t)
        hf'ext.aestronglyMeasurable.stronglyMeasurableAtFilter
        hf'ext.continuousAt
    simpa only [g] using hint.const_add (f a)
  have hg : Continuous g :=
    continuous_iff_continuousAt.mpr fun t ↦ (hgderiv t).continuousAt
  have hgright : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt g (f' t) (Set.Ici t) t := by
    intro t ht
    rw [← hf'ext_eq t ⟨ht.1, ht.2.le⟩]
    exact (hgderiv t).hasDerivWithinAt
  have hfg : ∀ t ∈ Set.Icc a b, f t = g t :=
    eq_of_has_deriv_right_eq hright hgright hf hg.continuousOn (by simp [g])
  intro t ht
  have hgt : HasDerivWithinAt g (f' t) (Set.Icc a b) t := by
    rw [← hf'ext_eq t ht]
    exact (hgderiv t).hasDerivWithinAt
  exact hgt.congr (fun s hs ↦ hfg s hs) (hfg t ht)

/-- At a strict interior point, the interval derivative furnished by
`hasDerivWithinAt_Icc_of_continuousOn_rightDerivative` is an ordinary
two-sided derivative. -/
theorem hasDerivAt_of_continuousOn_rightDerivative
    {a b t : ℝ} (hab : a ≤ b) (f f' : ℝ → X)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContinuousOn f' (Set.Icc a b))
    (hright : ∀ s ∈ Set.Ico a b,
      HasDerivWithinAt f (f' s) (Set.Ici s) s)
    (ht : t ∈ Set.Ioo a b) :
    HasDerivAt f (f' t) t := by
  exact
    (hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
      hab f f' hf hf' hright t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)

end ContinuousRightDerivative

section SemilinearFixedPointTwoSidedRegularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- A continuous choice `A(t)` of heat-generator values upgrades all of the
pointwise right derivatives of a semilinear heat fixed point to derivatives
relative to the complete time interval.  Graph witnesses are required only
at times strictly before `T`, exactly where the right-derivative input is
used; the endpoint derivative follows by continuity. -/
theorem semilinearHeatBUCFixedPoint_hasDerivWithinAt_timeInterval_of_continuous_generator
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (A : ℝ → BUC)
    (hA : ContinuousOn A (Set.Icc 0 (T : ℝ)))
    (hgraph : ∀ a : Set.Icc (0 : ℝ) (T : ℝ),
      (a : ℝ) < (T : ℝ) →
        IsInBUCHeatGeneratorDomain (E := E) (F := F) (u a) (A (a : ℝ))) :
    ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      HasDerivWithinAt
        (fun s : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property s))
        (A t + N (u (Set.projIcc 0 (T : ℝ) T.property t)))
        (Set.Icc (0 : ℝ) (T : ℝ)) t := by
  let path : ℝ → BUC := fun s ↦
    u (Set.projIcc 0 (T : ℝ) T.property s)
  let velocity : ℝ → BUC := fun s ↦ A s + N (path s)
  have hpath : Continuous path :=
    u.continuous.comp (continuous_projIcc (h := T.property))
  have hvelocity : ContinuousOn velocity (Set.Icc (0 : ℝ) (T : ℝ)) := by
    exact hA.add (hN.comp hpath).continuousOn
  have hright : ∀ t ∈ Set.Ico (0 : ℝ) (T : ℝ),
      HasDerivWithinAt path (velocity t) (Set.Ici t) t := by
    intro t ht
    let a : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hproj : Set.projIcc 0 (T : ℝ) T.property t = a := by
      exact Set.projIcc_of_mem T.property ⟨ht.1, ht.2.le⟩
    have hderiv :=
      semilinearHeatBUCFixedPoint_hasDerivWithinAt_interior_right
        (E := E) (F := F) T u₀ N hN u hu a ht.2 (A t) (by
          simpa only [a] using hgraph a ht.2)
    simpa only [path, velocity, a, hproj] using hderiv
  simpa only [path, velocity] using
    hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
      T.property path velocity hpath.continuousOn hvelocity hright

/-- Under a continuous family of generator graph values, a semilinear mild
fixed point is genuinely two-sided differentiable at every strict interior
time, with the expected vector field `A(t) + N(u(t))`. -/
theorem semilinearHeatBUCFixedPoint_hasDerivAt_interior_of_continuous_generator
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (A : ℝ → BUC)
    (hA : ContinuousOn A (Set.Icc 0 (T : ℝ)))
    (hgraph : ∀ a : Set.Icc (0 : ℝ) (T : ℝ),
      (a : ℝ) < (T : ℝ) →
        IsInBUCHeatGeneratorDomain (E := E) (F := F) (u a) (A (a : ℝ)))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T : ℝ)) :
    HasDerivAt
      (fun s : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property s))
      (A t + N (u (Set.projIcc 0 (T : ℝ) T.property t))) t := by
  exact
    (semilinearHeatBUCFixedPoint_hasDerivWithinAt_timeInterval_of_continuous_generator
      (E := E) (F := F) T u₀ N hN u hu A hA hgraph t
        ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

end SemilinearFixedPointTwoSidedRegularity

end Poincare
