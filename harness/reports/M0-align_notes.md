# M0-align-mathlib Notes

Mathlib's `SimplyConnectedSpace.nonempty_homeomorph_sphere_three` is a
topological statement:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) (1 : ℝ))
```

The frozen local `Poincare.PoincareConjecture` in
`Poincare/Global/Statement.lean` is stronger on hypotheses: it additionally
requires `SecondCountableTopology M`, `IsManifold (𝓡 3) ∞ M`, and
`ConnectedSpace M`.

The missing `ConnectedSpace` requirement is not the substantive gap, since
Mathlib's `SimplyConnectedSpace` provides path-connectedness and hence
connectedness. The substantive mismatch is that Mathlib's topological
`ChartedSpace ℝ³ M` hypothesis does not by itself provide the smooth
compatibility hypothesis `IsManifold (𝓡 3) ∞ M` required by the frozen local
statement.

Therefore `Poincare/Global/Alignment.lean` does not force an iff. It proves the
honest direction:

```lean
Poincare.poincareConjecture_of_mathlibPoincareStatement :
  Poincare.MathlibPoincareStatement.{u} → Poincare.PoincareConjecture.{u}
```
