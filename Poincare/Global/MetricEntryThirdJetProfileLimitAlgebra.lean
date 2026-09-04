import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Poincare.Global.MetricEntryThirdJetProfileCompactness

/-!
# Fiberwise algebra at anchors of formal metric-profile limits

The value slots of a scalar third-jet profile can be evaluated at their own
chart anchors.  On the closure of an actual metric family, these anchor values
retain bilinearity, symmetry, and any uniform positive lower comparison with a
fixed reference metric.

This gives a continuous positive-definite bilinear form in each individual
model fiber.  It does not prove compatibility between different chart anchors,
and it does not realize a formal profile limit as a smooth Riemannian metric.
-/

noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "P" => MetricEntryThirdJetProfileTarget n M

/-- The order-zero value of a formal third-jet profile at the chart anchor
named by its slot. -/
noncomputable def profileAnchorMetricValue
    (p : P) (x : M) (i j : E) : ℝ :=
  p (.value x i j) (extChartAt (closedSmoothModelWithCorners n) x x)

omit [IsManifold (closedSmoothModelWithCorners n) ∞ M] in
/-- Anchor evaluation is continuous on the product compact-open profile
space. -/
theorem continuous_profileAnchorMetricValue (x : M) (i j : E) :
    Continuous (fun p : P ↦ profileAnchorMetricValue p x i j) :=
  (continuous_eval_const
      (extChartAt (closedSmoothModelWithCorners n) x x)).comp
    (continuous_apply (MetricEntryThirdJetSlot.value x i j))

/-- At an actual metric profile, anchor evaluation recovers the metric
pairing. -/
@[simp] theorem profileAnchorMetricValue_metricEntryThirdJetProfile
    (g : G) (x : M) (i j : E) :
    profileAnchorMetricValue (metricEntryThirdJetProfile g) x i j =
      g.inner x i j :=
  metricEntryThirdJetProfile_value_anchor g x i j

/-- A family has a uniform positive lower comparison with a fixed reference
metric if the same positive factor works at every parameter, point, and
vector. -/
def UniformClosedRiemannianMetricLowerComparison
    {J : Type v} (gref : G) (gt : J → G) (c : ℝ) : Prop :=
  0 < c ∧
    ∀ t x w, c * gref.inner x w w ≤ (gt t).inner x w w

private theorem profile_limit_eq_of_eq_on_range
    {J : Type v} {gt : J → G} {F H : P → ℝ}
    (hF : Continuous F) (hH : Continuous H)
    (hEq : ∀ t, F (metricEntryThirdJetProfile (gt t)) =
      H (metricEntryThirdJetProfile (gt t)))
    {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt))) :
    F p = H p := by
  apply (closure_minimal ?_ (isClosed_eq hF hH)) hp
  rintro q ⟨t, rfl⟩
  exact hEq t

/-- Addition in the first vector slot is preserved at every anchor of a
formal profile limit. -/
theorem metricEntryThirdJetProfile_anchor_add_left_of_mem_closure
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (i₁ i₂ j : E) :
    profileAnchorMetricValue p x (i₁ + i₂) j =
      profileAnchorMetricValue p x i₁ j +
        profileAnchorMetricValue p x i₂ j := by
  refine profile_limit_eq_of_eq_on_range (gt := gt)
    (continuous_profileAnchorMetricValue x (i₁ + i₂) j)
    ((continuous_profileAnchorMetricValue x i₁ j).add
      (continuous_profileAnchorMetricValue x i₂ j))
    ?_ hp
  intro t
  change profileAnchorMetricValue (metricEntryThirdJetProfile (gt t))
      x (i₁ + i₂) j =
    profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i₁ j +
      profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i₂ j
  rw [profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile]
  calc
    _ = (((gt t).inner x i₁) + ((gt t).inner x i₂)) j :=
      congrArg (fun L : E →L[ℝ] ℝ ↦ L j)
        (((gt t).inner x).map_add i₁ i₂)
    _ = _ := rfl

/-- Scalar multiplication in the first vector slot is preserved at every
anchor of a formal profile limit. -/
theorem metricEntryThirdJetProfile_anchor_smul_left_of_mem_closure
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (a : ℝ) (i j : E) :
    profileAnchorMetricValue p x (a • i) j =
      a • profileAnchorMetricValue p x i j := by
  refine profile_limit_eq_of_eq_on_range (gt := gt)
    (continuous_profileAnchorMetricValue x (a • i) j)
    ((continuous_profileAnchorMetricValue x i j).const_smul a)
    ?_ hp
  intro t
  change profileAnchorMetricValue (metricEntryThirdJetProfile (gt t))
      x (a • i) j =
    a • profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i j
  rw [profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile]
  calc
    _ = (a • (gt t).inner x i) j :=
      congrArg (fun L : E →L[ℝ] ℝ ↦ L j)
        (((gt t).inner x).map_smul a i)
    _ = _ := rfl

/-- Addition in the second vector slot is preserved at every anchor of a
formal profile limit. -/
theorem metricEntryThirdJetProfile_anchor_add_right_of_mem_closure
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (i j₁ j₂ : E) :
    profileAnchorMetricValue p x i (j₁ + j₂) =
      profileAnchorMetricValue p x i j₁ +
        profileAnchorMetricValue p x i j₂ := by
  refine profile_limit_eq_of_eq_on_range (gt := gt)
    (continuous_profileAnchorMetricValue x i (j₁ + j₂))
    ((continuous_profileAnchorMetricValue x i j₁).add
      (continuous_profileAnchorMetricValue x i j₂))
    ?_ hp
  intro t
  change profileAnchorMetricValue (metricEntryThirdJetProfile (gt t))
      x i (j₁ + j₂) =
    profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i j₁ +
      profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i j₂
  rw [profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile]
  exact ((gt t).inner x i).map_add j₁ j₂

/-- Scalar multiplication in the second vector slot is preserved at every
anchor of a formal profile limit. -/
theorem metricEntryThirdJetProfile_anchor_smul_right_of_mem_closure
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (a : ℝ) (i j : E) :
    profileAnchorMetricValue p x i (a • j) =
      a • profileAnchorMetricValue p x i j := by
  refine profile_limit_eq_of_eq_on_range (gt := gt)
    (continuous_profileAnchorMetricValue x i (a • j))
    ((continuous_profileAnchorMetricValue x i j).const_smul a)
    ?_ hp
  intro t
  change profileAnchorMetricValue (metricEntryThirdJetProfile (gt t))
      x i (a • j) =
    a • profileAnchorMetricValue (metricEntryThirdJetProfile (gt t)) x i j
  rw [profileAnchorMetricValue_metricEntryThirdJetProfile,
    profileAnchorMetricValue_metricEntryThirdJetProfile]
  exact ((gt t).inner x i).map_smul a j

/-- Symmetry is preserved at every anchor of a formal profile limit. -/
theorem metricEntryThirdJetProfile_anchor_symm_of_mem_closure
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (i j : E) :
    profileAnchorMetricValue p x i j =
      profileAnchorMetricValue p x j i := by
  refine profile_limit_eq_of_eq_on_range (gt := gt)
    (continuous_profileAnchorMetricValue x i j)
    (continuous_profileAnchorMetricValue x j i)
    ?_ hp
  intro t
  simpa using (gt t).inner_symm x i j

/-- A uniform lower metric comparison passes to every anchor value in the
formal profile closure. -/
theorem metricEntryThirdJetProfile_anchor_lower_of_mem_closure
    {J : Type v} (gref : G) (gt : J → G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c)
    {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (w : E) :
    c * gref.inner x w w ≤ profileAnchorMetricValue p x w w := by
  have hclosed : IsClosed
      {q : P | c * gref.inner x w w ≤ profileAnchorMetricValue q x w w} :=
    isClosed_Ici.preimage (continuous_profileAnchorMetricValue x w w)
  apply (closure_minimal ?_ hclosed) hp
  rintro q ⟨t, rfl⟩
  simpa using hLower.2 t x w

private theorem metricEntryThirdJetProfile_anchor_isBilinearMap
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) :
    IsBilinearMap ℝ (profileAnchorMetricValue p x) where
  add_left :=
    metricEntryThirdJetProfile_anchor_add_left_of_mem_closure hp x
  smul_left :=
    metricEntryThirdJetProfile_anchor_smul_left_of_mem_closure hp x
  add_right :=
    metricEntryThirdJetProfile_anchor_add_right_of_mem_closure hp x
  smul_right :=
    metricEntryThirdJetProfile_anchor_smul_right_of_mem_closure hp x

/-- The anchor values of a formal profile limit, bundled as a continuous
bilinear map on the finite-dimensional model fiber. -/
noncomputable def metricEntryThirdJetProfileAnchorBilin
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (metricEntryThirdJetProfile_anchor_isBilinearMap hp x).toContinuousBilinearMap

/-- The bundled anchor bilinear form evaluates to the original formal-profile
anchor value. -/
@[simp] theorem metricEntryThirdJetProfileAnchorBilin_apply
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (i j : E) :
    metricEntryThirdJetProfileAnchorBilin hp x i j =
      profileAnchorMetricValue p x i j :=
  rfl

/-- The bundled anchor bilinear form is symmetric. -/
theorem metricEntryThirdJetProfileAnchorBilin_symm
    {J : Type v} {gt : J → G} {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) (i j : E) :
    metricEntryThirdJetProfileAnchorBilin hp x i j =
      metricEntryThirdJetProfileAnchorBilin hp x j i := by
  simpa using metricEntryThirdJetProfile_anchor_symm_of_mem_closure hp x i j

/-- Under a uniform positive lower comparison, every nonzero vector has
strictly positive square under the formal-limit anchor bilinear form. -/
theorem metricEntryThirdJetProfileAnchorBilin_pos
    {J : Type v} (gref : G) (gt : J → G) (c : ℝ)
    (hLower : UniformClosedRiemannianMetricLowerComparison gref gt c)
    {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    (x : M) {w : E} (hw : w ≠ 0) :
    0 < metricEntryThirdJetProfileAnchorBilin hp x w w := by
  rw [metricEntryThirdJetProfileAnchorBilin_apply]
  exact lt_of_lt_of_le
    (mul_pos hLower.1 (gref.inner_pos x hw))
    (metricEntryThirdJetProfile_anchor_lower_of_mem_closure
      gref gt c hLower hp x w)

end Poincare
