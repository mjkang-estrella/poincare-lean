# M2-deturck-1 done: honest DeTurck vocabulary at the Global layer

## Scope

New file: `Poincare/Global/DeTurck.lean`.

No existing Lean module was edited, and `Poincare.lean` was not changed.  The
new file imports `Poincare.Global.ShortTimeInterface` and stays on the genuine
`Global/` vocabulary: `ClosedSmoothRiemannianMetric`, `g.leviCivita`,
`CovariantDerivative.ricciTraceAt`, `ClosedC2TangentField`,
`IsClosedRicciFlowSolutionAt`, and `RicciFlowShortTimeExistence3`.

## Final declarations

```lean
def lieDerivMetricAt
    (g : ClosedSmoothRiemannianMetric n M) (W : ∀ y : M, TM y)
    (x : M) (u w : TM x) : ℝ
```

Final connection spelling:

```lean
(g.leviCivita W x) u
```

This is Mathlib's convention for `(∇_u W)(x)`.  The definition is

```lean
g.inner x ((g.leviCivita W x) u) w +
  g.inner x u ((g.leviCivita W x) w)
```

Proved:

```lean
theorem lieDerivMetricAt_symm
theorem closedC2TangentField_zero
@[simp] theorem lieDerivMetricAt_zero_field
theorem lieDerivMetricAt_eq_zero_of_field_eq_zero
```

The zero-field theorem uses `CovariantDerivative.zero`, the existing
connection linearity lemma for the section slot.

```lean
structure IsClosedRicciDeTurckSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (Wt : ℝ → ∀ y : M, TM y) (t₀ : ℝ) (x : M) : Prop
```

Fields:

```lean
leviCivita : ∀ t : ℝ,
  CovariantDerivative.IsLeviCivitaAt
    (fun y ↦ (gt t).inner y) (gt t).leviCivita x

deTurckField : ClosedC2TangentField (Wt t₀)

flow : ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField Z →
  ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
    (w : TM x),
    deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
      -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
        lieDerivMetricAt (gt t₀) (Wt t₀) x (Z x) w
```

Reduction anchor:

```lean
theorem isClosedRicciDeTurckSolutionAt_iff_isClosedRicciFlowSolutionAt_of_zero
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {Wt : ℝ → ∀ y : M, TM y} {t₀ : ℝ} {x : M}
    (hWzero : Wt t₀ = 0) :
    IsClosedRicciDeTurckSolutionAt gt Wt t₀ x ↔
      IsClosedRicciFlowSolutionAt gt t₀ x
```

Interfaces:

```lean
def RicciDeTurckShortTimeExistence3 (M : Type u) ... : Prop
```

Payload: for every `g₀ : ClosedSmoothRiemannianMetric 3 M`, there are
`T > 0`, `gt : ℝ → ClosedSmoothRiemannianMetric 3 M`, and
`Wt : ℝ → ∀ y : M, TangentSpace (closedSmoothModelWithCorners 3) y` with
`gt 0 = g₀` and the Ricci-DeTurck clause on `Set.Ico 0 T`.

```lean
def DeTurckPullbackToRicciFlow3 (M : Type u) ... : Prop
```

Payload: every short-time Ricci-DeTurck family produces a Ricci-flow metric
family on the same interval with the same initial metric.

Composition:

```lean
theorem ricciFlowShortTimeExistence3_of_deTurck_of_pullback
    (hDeTurck : RicciDeTurckShortTimeExistence3 M)
    (hPullback : DeTurckPullbackToRicciFlow3 M) :
    RicciFlowShortTimeExistence3 M
```

Static sanity:

```lean
theorem static_ricciFlat_deTurckClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM3 y},
      ClosedC2TangentField Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM3 x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciDeTurckSolutionAt
        (fun _ : ℝ ↦ g) (fun _ : ℝ ↦ 0) t x
```

This proof routes through `static_ricciFlat_flowClause` and the zero-field
reduction theorem.

## Next isolated task: DeTurck vector field construction

Construct the actual DeTurck vector field from a moving metric and a fixed
background metric.  Precise statement sketch:

```lean
noncomputable def deTurckVectorFieldAt
    (g bg : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    TangentSpace (closedSmoothModelWithCorners 3) x :=
  metricTraceWithRespectTo g x
    (fun u v ↦
      ((g.leviCivita.difference bg.leviCivita) x v) u)
```

In finite-frame spelling, this should become the invariant version of

```lean
∑ i, ((g.leviCivita.difference bg.leviCivita) x (b i)) (sharp i)
```

where `b` and `sharp` are the existing Gram-frame / metric-dual frame data for
`g` at `x`.  This is the coordinate-free trace of
`Γ(g) - Γ(bg)`, i.e. `W^k = g^{ij}(Γ(g)^k_{ij} - Γ(bg)^k_{ij})`.

Target deliverables for that task:

```lean
noncomputable def deTurckVectorField
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (bg : ClosedSmoothRiemannianMetric 3 M) (t : ℝ) :
    ∀ x : M, TangentSpace (closedSmoothModelWithCorners 3) x

def DeTurckVectorFieldRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (bg : ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : Prop :=
  ClosedC2TangentField (deTurckVectorField gt bg t)
```

Then specialize `IsClosedRicciDeTurckSolutionAt gt (deTurckVectorField gt bg)`
and keep the analytic proof that this field makes the system strictly
parabolic as a later, separate obligation.

## Verification

Required command run:

```text
lake build Poincare.Global.DeTurck
```

Actual result: success, `Build completed successfully (3077 jobs)`.  The build
replayed existing upstream warnings and `#check` info, but `Poincare.Global.DeTurck`
itself built successfully.
