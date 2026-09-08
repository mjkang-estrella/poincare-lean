# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/connection-naturality`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/ConnectionInstanceNaturality.lean`; no vacuous definitions; report actual command output;
commit each verified lemma on the branch; report to `harness/reports/connection-naturality_{done|blocked}.md`.
Stop conditions as in `harness/tasks/M5-glob-69.md`.

# Task: discharge `ConnectionCurvatureNaturality`

Read first: `harness/reports/curvature-transport_blocked.md` (the previous worker's exact boundary and its
"exact next mathematical action"), then `Poincare/Global/CurvatureInstanceTransport.lean` fully
(`transportField`, `inverseTransportField`, `transportField_contMDiff_iff`, `modelMDifferentiableAt_iff`,
`inverseTransportField_mdiffAt`, `conjugatedDerivative`, `conjugatedDerivative_apply`,
`conjugatedDerivative_add`, `ConnectionCurvatureNaturality`, `conjugatedDerivative_isCovariantDerivativeOn`,
`conjugatedConnection_eq_leviCivita`, `hasConstantSectionalCurvature3_transport`,
`target_of_ConnectionCurvatureNaturality`, `exists_controlled_recognition_reduction`),
`Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean` (`J`, `J_apply`, `D`, `transport_inner`),
`Poincare/Global/LeviCivita.lean` (`levi_civita_unique`, `IsMetricCompatible`), Mathlib's
`CovariantDerivative` (`Mathlib/Geometry/Manifold/VectorField/CovariantDerivative/*`: the Leibniz law
`IsCovariantDerivativeOn`, `torsion`, `curvatureOp`) and `VectorField.mlieBracket`
(`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`), and `mfderiv` chain rules
(`mfderiv_comp`, `MDifferentiableAt.comp`, `mfderivWithin` on charts).

Target (frozen). In the context of `CurvatureInstanceTransport.lean`
(`[T2Space M] [inst : ChartedSpace E M] [IsManifold I ∞ M] (inst' : ChartedSpace E M)
(h : inst'.atlas ⊆ maximalAtlas inst)`):

```lean
theorem connectionCurvatureNaturality (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    CurvatureInstanceTransport.ConnectionCurvatureNaturality (inst := inst) inst' h g
```

and the two unconditional consumers it unlocks, restated without the `hN` hypothesis:
`unitConstantCurvatureSphereRecognition3_of_controlled` (recognition for `inst` from recognition for
`inst'`) and the `∃`-form `exists_controlled_recognition_reduction'` for an arbitrary compatible metric.

Order of work (commit each):
1. The scalar exterior-derivative identity across instances, exactly the previous worker's displayed shape:
   for `f : M → ℝ` pointwise `MDifferentiableAt` at `x` (for one instance, hence for both by
   `modelMDifferentiableAt_iff`), `mfderiv_new f x v = mfderiv_old f x (J x v)` (state it with the exact
   `mfderiv`/`extDerivFun` spelling used in the repository's `IsMetricCompatible` and Leibniz laws). Proof: both
   sides are derivatives of `f ∘ chart⁻¹` in the respective charts; `J_apply` is the derivative of the chart
   change; chain rule.
2. Naturality of the Lie bracket: `mlieBracket` of transported fields is the transport of the bracket, at points
   where both fields are differentiable (Mathlib's `mlieBracket` is chart-defined; use `J_apply` and the
   chain rule as in step 1; the `T2Space` and pointwise-differentiability hypotheses match the previous
   module's).
3. The Leibniz law for `conjugatedDerivative` from step 1 and `conjugatedDerivative_add`, then metric
   compatibility of the conjugated operator for `transport g` (from `transport_inner` and step 1) and zero
   torsion (from step 2); conclude the first naturality clause via `levi_civita_unique` exactly as
   `conjugatedConnection_eq_leviCivita` does, but unconditionally.
4. The second clause (curvature values conjugate by `J`): from the first clause applied twice, the definition of
   `curvatureOp` on the extended fields, and locality/tensoriality of the curvature operator (the repository has
   curvature tensoriality lemmas in `CurvatureTensoriality.lean` / `Global/Curvature.lean`; find and use them
   rather than comparing total functions of local extensions).
5. Assemble `connectionCurvatureNaturality` and the two unconditional consumers.
If step 2 or 4 resists, deliver the earlier steps and the exact resisting `def` with `target_of_<resisting>`.
