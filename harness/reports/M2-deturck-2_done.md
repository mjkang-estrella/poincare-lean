# M2-deturck-2 done: concrete DeTurck vector field at the Global layer

## Scope

New Lean file: `Poincare/Global/DeTurckField.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.  The
new file imports `Poincare.Global.DeTurck`, so it stays on the genuine
`Global/` vocabulary and reuses the already imported Gram-frame trace
machinery from `Global/ScalarVariation.lean`.

The construction is general in `n`; the fallback to dimension `3` was not
needed.

## Final declarations

```lean
noncomputable def deTurckConnectionDifferenceAt
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) : TM x
```

Final pointwise spelling:

```lean
(g.leviCivita (extend E w) x) u -
  (bg.leviCivita (extend E w) x) u
```

Here `u` is the first lower connection index and `w` seeds the canonical
`extend` section in the second lower index.

```lean
@[simp] theorem deTurckConnectionDifferenceAt_self
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) :
    deTurckConnectionDifferenceAt g g x u w = 0
```

```lean
noncomputable def deTurckVectorFieldAt
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) : TM x
```

Final trace formula:

```lean
letI : FiniteDimensional ℝ (TM x) :=
  inferInstanceAs (FiniteDimensional ℝ E)
∑ i, deTurckConnectionDifferenceAt g bg x
  ((Module.finBasis ℝ (TM x)) i)
  (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))
```

This is the `g`-Gram-inverse-weighted trace of `Γ(g) - Γ(bg)` in the canonical
extension frame.  Equivalently, in component notation it is
`W^k = g^{ij} (Γ(g)^k_{ij} - Γ(bg)^k_{ij})`.

```lean
@[simp] theorem deTurckVectorFieldAt_self
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    deTurckVectorFieldAt g g x = 0
```

```lean
noncomputable def deTurckVectorField
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) : ∀ x : M, TM x
```

with

```lean
@[simp] theorem deTurckVectorField_apply
```

unfolding it to `fun x => deTurckVectorFieldAt (gt t) bg x`.

```lean
def DeTurckVectorFieldRegularAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) : Prop :=
  ClosedC2TangentField (n := n) (M := M) (deTurckVectorField gt bg t)
```

This is an honest regularity proposition, not an instance or certificate.

```lean
def IsDeTurckGaugedFlowAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop :=
  IsClosedRicciDeTurckSolutionAt gt (fun t ↦ deTurckVectorField gt bg t) t₀ x
```

with the definitional unfolding lemma:

```lean
theorem isDeTurckGaugedFlowAt_iff
```

Static sanity:

```lean
theorem isDeTurckGaugedFlowAt_const_self_iff_isClosedRicciFlowSolutionAt
    (g : ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    IsDeTurckGaugedFlowAt (fun _ : ℝ ↦ g) g t₀ x ↔
      IsClosedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ x
```

The proof uses `funext` to produce the zero-field hypothesis from
`deTurckVectorFieldAt_self`, then applies
`isClosedRicciDeTurckSolutionAt_iff_isClosedRicciFlowSolutionAt_of_zero`.

```lean
theorem static_ricciFlat_deTurckGaugedFlowClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM3 y},
      ClosedC2TangentField (n := 3) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM3 x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsDeTurckGaugedFlowAt (fun _ : ℝ ↦ g) g t x
```

This composes the constant-self reduction with
`static_ricciFlat_flowClause`.

## Verification

Required command run:

```text
lake build Poincare.Global.DeTurckField
```

Actual result: success, `Build completed successfully (3078 jobs)`.  The build
replayed existing upstream warnings, but `Poincare.Global.DeTurckField` built
successfully.

Additional hygiene checks:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/DeTurckField.lean
git diff --check -- Poincare/Global/DeTurckField.lean
```

Actual result: no forbidden markers and no whitespace errors.

## Next decomposition

1. Chart formula for the constructed field: prove that the `extend`-frame
   trace above agrees in coordinates with the classical Christoffel formula
   `W^k = g^{ij}(Γ(g)^k_{ij} - Γ(bg)^k_{ij})`.
2. Regularity of `deTurckVectorField`: discharge
   `DeTurckVectorFieldRegularAt gt bg t` from the metric smoothness and
   connection-regularity APIs, producing the required `ClosedC2TangentField`.
3. Ricci-DeTurck equation with this exact field: specialize the
   `IsClosedRicciDeTurckSolutionAt` equation to `IsDeTurckGaugedFlowAt` and use
   the chart formula as the strict-parabolicity target.
