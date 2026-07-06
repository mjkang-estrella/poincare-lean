import Poincare.Global.ShortTimeInterface

/-!
# Ricci-DeTurck statement layer

This module adds the closed global Ricci-DeTurck vocabulary on top of the
genuine `Global/` Ricci-flow API.  It deliberately avoids the quarantined
legacy interface packages.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

section General

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
The Lie derivative of the metric along a tangent field, evaluated at one
point.  Mathlib's covariant-derivative convention is
`(g.leviCivita W x) u = (∇_u W)(x)`, so this is the usual torsion-free
Levi-Civita formula `(L_W g)(u,w) = g(∇_u W,w) + g(u,∇_w W)`.
-/
def lieDerivMetricAt
    (g : ClosedSmoothRiemannianMetric n M) (W : ∀ y : M, TM y)
    (x : M) (u w : TM x) : ℝ :=
  g.inner x ((g.leviCivita W x) u) w +
    g.inner x u ((g.leviCivita W x) w)

/-- The metric Lie derivative is symmetric in its two tangent-vector slots. -/
theorem lieDerivMetricAt_symm
    (g : ClosedSmoothRiemannianMetric n M) (W : ∀ y : M, TM y)
    (x : M) (u w : TM x) :
    lieDerivMetricAt g W x u w = lieDerivMetricAt g W x w u := by
  unfold lieDerivMetricAt
  rw [g.inner_symm x ((g.leviCivita W x) u) w,
    g.inner_symm x ((g.leviCivita W x) w) u]
  ring

omit [T2Space M] in
/--
The globally zero tangent field is `C²`, hence admissible as DeTurck vector
field data.
-/
theorem closedC2TangentField_zero :
    ClosedC2TangentField (n := n) (M := M) (0 : ∀ y : M, TM y) := by
  have hzero :
      ContMDiff I ((I).prod 𝓘(ℝ, E)) (2 : ℕ∞ω)
        (Bundle.zeroSection E TM) :=
    Bundle.contMDiff_zeroSection ℝ TM
  simpa [ClosedC2TangentField, Bundle.zeroSection] using
    hzero

/--
The zero-field case of the Lie derivative.  This uses
`CovariantDerivative.zero`, the connection linearity lemma for the section
slot.
-/
@[simp] theorem lieDerivMetricAt_zero_field
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) :
    lieDerivMetricAt g (0 : ∀ y : M, TM y) x u w = 0 := by
  have hzero : g.leviCivita (0 : ∀ y : M, TM y) = 0 :=
    CovariantDerivative.zero g.leviCivita
  simp [lieDerivMetricAt, hzero]

/-- If the vector field is literally zero, the Lie derivative vanishes. -/
theorem lieDerivMetricAt_eq_zero_of_field_eq_zero
    (g : ClosedSmoothRiemannianMetric n M) {W : ∀ y : M, TM y}
    {x : M} {u w : TM x} (hW : W = 0) :
    lieDerivMetricAt g W x u w = 0 := by
  subst W
  simp

/--
Pointwise Ricci-DeTurck solution condition for closed smooth metrics.

It has the same test-field shape as `IsClosedRicciFlowSolutionAt`, but the
right-hand side contains the metric Lie derivative along the DeTurck field.
The DeTurck field is required to be a genuine `C²` tangent field at the active
time slice.
-/
structure IsClosedRicciDeTurckSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (Wt : ℝ → ∀ y : M, TM y) (t₀ : ℝ) (x : M) : Prop where
  leviCivita : ∀ t : ℝ,
    CovariantDerivative.IsLeviCivitaAt
      (fun y ↦ (gt t).inner y) (gt t).leviCivita x
  deTurckField : ClosedC2TangentField (n := n) (M := M) (Wt t₀)
  flow : ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField (n := n) (M := M) Z →
    ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
      (w : TM x),
      deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
        -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
          lieDerivMetricAt (gt t₀) (Wt t₀) x (Z x) w

/--
When the DeTurck field is zero at the time slice, the Ricci-DeTurck equation is
exactly the Ricci-flow equation.
-/
theorem isClosedRicciDeTurckSolutionAt_iff_isClosedRicciFlowSolutionAt_of_zero
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {Wt : ℝ → ∀ y : M, TM y} {t₀ : ℝ} {x : M}
    (hWzero : Wt t₀ = 0) :
    IsClosedRicciDeTurckSolutionAt gt Wt t₀ x ↔
      IsClosedRicciFlowSolutionAt gt t₀ x := by
  constructor
  · intro hdet
    refine ⟨hdet.leviCivita, ?_⟩
    intro Z hZ hreg w
    have hlie :
        lieDerivMetricAt (gt t₀) (Wt t₀) x (Z x) w = 0 := by
      exact lieDerivMetricAt_eq_zero_of_field_eq_zero
        (g := gt t₀) (W := Wt t₀) (x := x) (u := Z x) (w := w) hWzero
    simpa [hlie] using hdet.flow hZ hreg w
  · intro hflow
    refine ⟨hflow.leviCivita, ?_, ?_⟩
    · simpa [hWzero] using closedC2TangentField_zero (n := n) (M := M)
    · intro Z hZ hreg w
      have hlie :
          lieDerivMetricAt (gt t₀) (Wt t₀) x (Z x) w = 0 := by
        exact lieDerivMetricAt_eq_zero_of_field_eq_zero
          (g := gt t₀) (W := Wt t₀) (x := x) (u := Z x) (w := w) hWzero
      simpa [hlie] using hflow.flow hZ hreg w

end General

section DimensionThree

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/--
Hamilton-DeTurck short-time existence for the closed three-dimensional global
vocabulary: every initial metric admits a positive-time Ricci-DeTurck metric
family and DeTurck vector-field family.
-/
def RicciDeTurckShortTimeExistence3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M,
    ∃ T : ℝ, 0 < T ∧
      ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
        ∃ Wt : ℝ → ∀ y : M,
          TangentSpace (closedSmoothModelWithCorners 3) y,
          gt 0 = g₀ ∧
            ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
              IsClosedRicciDeTurckSolutionAt gt Wt t x

/--
The gauge-pullback wall: a short-time Ricci-DeTurck family produces a
short-time Ricci-flow family with the same initial metric and interval.
-/
def DeTurckPullbackToRicciFlow3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ (g₀ : ClosedSmoothRiemannianMetric 3 M) {T : ℝ}
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {Wt : ℝ → ∀ y : M,
      TangentSpace (closedSmoothModelWithCorners 3) y},
      0 < T →
        gt 0 = g₀ →
          (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
            IsClosedRicciDeTurckSolutionAt gt Wt t x) →
            ∃ ht : ℝ → ClosedSmoothRiemannianMetric 3 M,
              ht 0 = g₀ ∧
                ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
                  IsClosedRicciFlowSolutionAt ht t x

/--
Hamilton-DeTurck short-time existence plus the pullback identity gives the
closed Ricci-flow short-time existence interface.
-/
theorem ricciFlowShortTimeExistence3_of_deTurck_of_pullback
    (hDeTurck : RicciDeTurckShortTimeExistence3 M)
    (hPullback : DeTurckPullbackToRicciFlow3 M) :
    RicciFlowShortTimeExistence3 M := by
  intro g₀
  rcases hDeTurck g₀ with ⟨T, hT, gt, Wt, hinit, hdet⟩
  rcases hPullback g₀ hT hinit hdet with ⟨ht, hht0, hflow⟩
  exact ⟨T, hT, ht, hht0, hflow⟩

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] in
/--
Static Ricci-flat metrics satisfy the Ricci-DeTurck clause with zero DeTurck
field.
-/
theorem static_ricciFlat_deTurckClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM3 y},
      ClosedC2TangentField (n := 3) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM3 x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciDeTurckSolutionAt
        (fun _ : ℝ ↦ g) (fun _ : ℝ ↦ (0 : ∀ y : M, TM3 y)) t x := by
  have hflow := static_ricciFlat_flowClause (M := M) (g := g) hric T
  intro t ht x
  exact
    (isClosedRicciDeTurckSolutionAt_iff_isClosedRicciFlowSolutionAt_of_zero
      (gt := fun _ : ℝ ↦ g)
      (Wt := fun _ : ℝ ↦ (0 : ∀ y : M, TM3 y))
      (t₀ := t) (x := x) rfl).2 (hflow t ht x)

end DimensionThree

end Poincare
