import Poincare.Global.MetricEntryThirdJetFormalInverse

/-!
# Raw coordinate jets from formal metric profiles

The scalar third-jet profile already records all metric derivatives needed by
the fixed-basis curvature formulas.  This module exposes those entries as
finite coordinate arrays and proves that the arrays vary continuously with a
formal profile and its model-space coordinate.

No multilinearity is asserted for an arbitrary formal profile: outside the
range of genuine metric profiles, the direction-tagged scalar entries need
not satisfy the identities of actual derivatives.  Keeping raw arrays makes
that boundary explicit while retaining exactly the data used by finite-basis
Christoffel, Ricci, and covariant-Ricci contractions.
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

/-- First metric-jet entries of a formal profile in the canonical finite
basis.  The indices select the derivative direction and two metric slots. -/
noncomputable def formalProfileMetricFirstJetCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun r i j => p (.first x (b r) (b i) (b j)) z

/-- Second metric-jet entries of a formal profile in the canonical finite
basis. -/
noncomputable def formalProfileMetricSecondJetCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun r s i j => p (.second x (b r) (b s) (b i) (b j)) z

/-- Third metric-jet entries of a formal profile in the canonical finite
basis. -/
noncomputable def formalProfileMetricThirdJetCoordinatesAt
    (p : P) (x : M) (z : E) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → ℝ :=
  let b := Module.finBasis ℝ E
  fun r s t i j => p (.third x (b r) (b s) (b t) (b i) (b j)) z

/-- On a genuine metric profile, the formal first-jet array is exactly the
first derivative of the cutoff-blended metric in the canonical basis. -/
@[simp] theorem formalProfileMetricFirstJetCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileMetricFirstJetCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun r i j =>
        fderiv ℝ (anchorBlendedMetricFamily (fun h : G ↦ h) x g) z
          ((Module.finBasis ℝ E) r) ((Module.finBasis ℝ E) i)
          ((Module.finBasis ℝ E) j) := by
  rfl

/-- On a genuine metric profile, the formal second-jet array is exactly the
iterated second derivative of the cutoff-blended metric in the canonical
basis. -/
@[simp] theorem formalProfileMetricSecondJetCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileMetricSecondJetCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun r s i j =>
        fderiv ℝ
          (fun y => fderiv ℝ
            (anchorBlendedMetricFamily (fun h : G ↦ h) x g) y
              ((Module.finBasis ℝ E) r)) z
          ((Module.finBasis ℝ E) s) ((Module.finBasis ℝ E) i)
          ((Module.finBasis ℝ E) j) := by
  rfl

/-- On a genuine metric profile, the formal third-jet array is exactly the
iterated third derivative of the cutoff-blended metric in the canonical
basis. -/
@[simp] theorem formalProfileMetricThirdJetCoordinatesAt_profile
    (g : G) (x : M) (z : E) :
    formalProfileMetricThirdJetCoordinatesAt
        (metricEntryThirdJetProfile g) x z =
      fun r s t i j =>
        fderiv ℝ
          (fun y => fderiv ℝ
            (fun w => fderiv ℝ
              (anchorBlendedMetricFamily (fun h : G ↦ h) x g) w
                ((Module.finBasis ℝ E) r)) y
              ((Module.finBasis ℝ E) s)) z
          ((Module.finBasis ℝ E) t) ((Module.finBasis ℝ E) i)
          ((Module.finBasis ℝ E) j) := by
  rfl

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The complete formal first-jet coordinate array is jointly continuous in
the profile and model-space coordinate. -/
theorem continuous_formalProfileMetricFirstJetCoordinatesAt (x : M) :
    Continuous (fun q : P × E =>
      formalProfileMetricFirstJetCoordinatesAt q.1 x q.2) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_apply
    (MetricEntryThirdJetSlot.first x
      ((Module.finBasis ℝ E) r) ((Module.finBasis ℝ E) i)
      ((Module.finBasis ℝ E) j))).comp continuous_fst).eval continuous_snd)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The complete formal second-jet coordinate array is jointly continuous in
the profile and model-space coordinate. -/
theorem continuous_formalProfileMetricSecondJetCoordinatesAt (x : M) :
    Continuous (fun q : P × E =>
      formalProfileMetricSecondJetCoordinatesAt q.1 x q.2) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_apply
    (MetricEntryThirdJetSlot.second x
      ((Module.finBasis ℝ E) r) ((Module.finBasis ℝ E) s)
      ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))).comp
        continuous_fst).eval continuous_snd)

omit [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- The complete formal third-jet coordinate array is jointly continuous in
the profile and model-space coordinate. -/
theorem continuous_formalProfileMetricThirdJetCoordinatesAt (x : M) :
    Continuous (fun q : P × E =>
      formalProfileMetricThirdJetCoordinatesAt q.1 x q.2) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  apply continuous_pi
  intro t
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_apply
    (MetricEntryThirdJetSlot.third x
      ((Module.finBasis ℝ E) r) ((Module.finBasis ℝ E) s)
      ((Module.finBasis ℝ E) t) ((Module.finBasis ℝ E) i)
      ((Module.finBasis ℝ E) j))).comp continuous_fst).eval continuous_snd)

end Poincare
