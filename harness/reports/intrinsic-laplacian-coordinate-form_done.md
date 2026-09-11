# Intrinsic Laplacian coordinate form: done

Date: 2026-09-11. Base: `84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5`.
Branch: `worker/intrinsic-laplacian-coordinate-form`.
Verified proof head: `4f0def7b4e1831ba8c7e03282eb3e4194167a233`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

Both parts are proved. The frozen part-A diagnostic type, the unconditional
static Stokes theorem, and the forward normalized-flow scalar corollary pass
exact assignment probes against the freshly compiled module. The restricted
domain constructor is also implemented. No mathematical obligation from this
task remains in the final statements. This worker result awaits independent
review; it is not merged or marked accepted.

The only Lean addition is `Poincare/Global/IntrinsicLaplacianCoordinateForm.lean`, with sixteen
theorems and one constructor definition, all in the requested namespace.
Each authored declaration was compiled and dependency-checked before its
separate proof commit. A final cleanup removes two unused section assumptions
from the support lemma. No existing Lean file, `Poincare.lean`, frozen contract,
or `HANDOFF.md` is changed. The task's explicit file scope keeps those files
read-only; this report supplies the dated handoff.

## Deliverables

| Declaration | Result | First proof commit |
| --- | --- | --- |
| `transported_gradient_eq_coordGradient` | Genuine inverse-chart pullback of the intrinsic gradient equals the coordinate metric gradient | `6bfbc4be` |
| `hessianAt_eq_blended_chart_hessian` | Applies the specified Levi-Civita transport bridge to the gradient and its derivative | `5cb6a954` |
| `hessianAt_eq_chart_derivatives` | Removes the auxiliary cutoff from the Hessian formula | `828633a3` |
| `hessianAt_eq_coordinate_hessian` | Full ordinary second derivative minus the standard Christoffel sum | `6a0b55aa` |
| `laplacianAt_eq_inverseGram_hessian` | Inverse-Gram contraction in any finite tangent basis | `6e4b8312` |
| `laplacianAt_eq_chart_hessian` | Specialization to the inverse-chart Euclidean tangent frame | `4edfb209` |
| `laplacianAt_eq_christoffelCoordinateLaplacian` | Exact part-A identity from the previous report's diagnostic | `eca8835d` |
| `geometry_of_shrunk_coordinate_coefficients` | Original Stokes record with coordinate domains equal to the images of the shrunk regions | `656f39f2` |
| `closedLaplacianStokes_of_contMDiff_two` | Integrability and zero integral of the intrinsic Laplacian for every C² scalar | `72214b33` |
| `closedLaplacianStokes_scalarAt_of_normalizedRicciFlow` | Requested forward-flow scalar conclusion from all-time joint C³ entries | `1763acf3` |

## Mathematical construction

The initial probe reproduces the exact metric-dual trace residual displayed in
`closed-laplacian-stokes-global-coefficients_blocked.md`. The genuine inverse
matrix is explicitly typed as a matrix wherever the coordinate array is
introduced. It is not the entrywise reciprocal operation.

The trace proof uses the landed `laplacianAt_eq_sum_hessianAt_basis`,
`metricDualVectorAt_basis_coord_eq_sum_inv`, and
`inverseChartEuclideanTangentBasisAt`. It identifies the actual Gram matrix of
that transported basis with `inverseChartPullbackGramMatrixField`.

The gradient proof first pairs the transported gradient with the chart metric.
The fixed-chart scalar differential and the chart-derivative round trip give
the ordinary differential of `coordinateScalar`. Nondegeneracy then identifies
the gradient with the genuine inverse-metric coordinate gradient.

The Hessian proof applies
`LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one`
to that intrinsic gradient. Neighborhood equality identifies both the
transported gradient and its ordinary derivative with the coordinate gradient
of a smooth blended metric. The landed model gradient-Hessian theorem supplies
the ordinary second derivative and the closed Christoffel correction.

The canonical anchor cutoff is not assumed to equal one throughout the shrunk
region. For each evaluation point, the compact-set cutoff theorem is applied
to its singleton, producing a smooth cutoff supported inside the chart target
and equal to one nearby. Neighborhood equality then removes this cutoff from
the final Hessian formula. The standard Christoffel array is proved directly
from the closed operator's Koszul covector, first derivatives of the metric,
and inverse-matrix coordinates. The anchor-cutoff-specific
`christoffel_eq_connection` is inspected but not needed in the final proof.

For part B, `restrictedChart_measure` transports the density measure through
the inclusion of the smaller coordinate domain. `restrictedChart_density_integrable`
uses that measure equality and finite Riemannian volume. The support lemma
bounds the coordinate support by the chart image of the manifold support.
Continuity of the localized Laplacian is proved using the coordinate divergence
on the smaller open region and local vanishing outside the scalar support.
Thus measurability is supplied by the constructor, not added as an analytic
premise.

The static theorem consumes the landed shrunk-cover global coefficient
extensions. Their neighborhood agreement on the images of the closures gives
the genuine density weight, the transferred divergence compatibility, and the
coefficient values required by part A. Second countability is derived from
compactness using `ChartedSpace.secondCountable_of_sigmaCompact`; it is not an
extra hypothesis of the static theorem. The final flow theorem uses exactly
the scalar C² regularity route specified in the earlier report.

## Verification

The final direct source gate exits 0 with no warnings. The forbidden-token
scan is empty, exit 1. `git diff 84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5 --check`
exits 0. The final exact assignments check the copied part-A diagnostic type
and the static and forward-flow conclusions. The module was first compiled
to a fresh object in this worktree's cloned Lake cache, then imported for these
checks. No full build or root integration audit was run.

The module-wide scan covers twenty noninternal declarations: the seventeen
authored declarations and three compiler-generated equations. All twenty
have exactly `[propext, Classical.choice, Quot.sound]`, and all twenty are
also checked with literal `#print axioms` commands. The generated equations
are `Poincare.coordinateDirectionalDerivative.eq_1`,
`Poincare.coordinateSecondDerivative.eq_1`, and
`Poincare.ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt.congr_simp`.

Successful final scan output:

```text
MODULE_SCAN declarations=20 all_exact=true
```

The transcript below preserves every Lean probe, including the initial
resisting target and unsuccessful intermediate attempts. Dependency prints
from unsuccessful attempts can contain compiler recovery constants; these
are diagnostic output, not proofs present in the final source. Source edits
are recorded as deltas so those probes can be reconstructed. The initial
clean branch, base commit, and worktree inventory were checked before editing.

## Independent review handoff

The exact first action is:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Review `git diff 84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5..4f0def7b4e1831ba8c7e03282eb3e4194167a233 -- Poincare/Global/IntrinsicLaplacianCoordinateForm.lean`,
then rerun the final diagnostic source reproduced below. Root import wiring
and integration acceptance remain the orchestrator's responsibility.

## Proof commits

```text
6e4b8312 Prove intrinsic Laplacian inverse Gram contraction in any tangent basis
4edfb209 Compute the intrinsic Laplacian in the inverse chart Euclidean frame
741e94f3 Identify the differential through the transported intrinsic gradient
6bfbc4be Prove the intrinsic gradient equals the genuine coordinate gradient
5cb6a954 Transport the intrinsic Hessian through a smooth local chart metric
828633a3 Remove the auxiliary cutoff from the intrinsic Hessian formula
3574af09 Compute raised covector coordinates from the inverse metric matrix
63b40d78 Identify the standard Christoffel array with the closed connection operator
6a0b55aa Prove the full intrinsic Hessian identity in coordinate entries
eca8835d Prove the frozen intrinsic Laplacian coordinate identity
bf3c0f71 Prove the Hausdorff chart measure formula on restricted domains
42902a8d Prove integrability of the density on restricted chart domains
7b1da239 Control zero-extended coordinate support in the shrunk chart image
e74d9de4 Derive localized Laplacian continuity from restricted coordinate divergence
656f39f2 Construct Stokes geometry over the shrunk coordinate domains
72214b33 Prove closed Laplacian Stokes for every C2 scalar in dimension three
1763acf3 Prove forward normalized-flow scalar Laplacian Stokes
4f0def7b Remove unused ambient assumptions from the coordinate support lemma
```

## Final proof diff

```diff
diff --git a/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean b/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
new file mode 100644
index 00000000..f438c134
--- /dev/null
+++ b/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -0,0 +1,722 @@
+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
+import Poincare.Global.DeTurckPrincipalIdentity
+
+noncomputable section
+open Bundle FiberBundle Filter MeasureTheory Set
+open scoped Manifold ContDiff Topology ENNReal NNReal
+set_option autoImplicit false
+universe u
+namespace Poincare.IntrinsicLaplacianCoordinateForm
+
+variable {n : ℕ} {M : Type u}
+variable [TopologicalSpace M] [T2Space M]
+variable [ChartedSpace (ClosedSmoothModel n) M]
+variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+local notation "I" => closedSmoothModelWithCorners n
+local notation "E" => ClosedSmoothModel n
+local notation "TM" => (TangentSpace I : M → Type _)
+
+/-- The intrinsic Hessian trace contracts with the inverse Gram matrix in any basis. -/
+theorem laplacianAt_eq_inverseGram_hessian
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
+    {d : ℕ} (b : Module.Basis (Fin d) ℝ (TM x)) :
+    g.laplacianAt f x = ∑ i, ∑ j,
+      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
+  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
+  rw [Poincare.laplacianAt_eq_sum_hessianAt_basis g f x b]
+  apply Finset.sum_congr rfl
+  intro i _
+  rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
+  change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
+  rw [map_sum]
+  simp only [map_smul, smul_eq_mul]
+  rfl
+
+/-- In the inverse-chart frame the Laplacian uses the genuine inverse Gram field. -/
+theorem laplacianAt_eq_chart_hessian
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (p : M)
+    (z : (extChartAt I p).target) :
+    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
+      ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
+        g.hessianAt f ((extChartAt I p).symm z)
+          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+            (EuclideanSpace.basisFun (Fin n) ℝ i))
+          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
+  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
+  have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
+      inverseChartPullbackGramMatrixField g p z := by
+    ext i j
+    simp only [ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_apply,
+      ClosedSmoothRiemannianMetric.metricBilinAt_apply, b,
+      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
+    rfl
+  change g.laplacianAt f ((extChartAt I p).symm z) = _
+  rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
+  simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
+
+/-- Pairing the transported intrinsic gradient with the chart metric gives the
+ordinary differential of the coordinate scalar. -/
+theorem chartMetric_transported_gradient
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) (w : E) :
+    CovariantDerivative.chartMetric g.inner p z
+      (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z) w =
+      fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z w := by
+  let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+  have hD : D.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
+  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f =ᶠ[𝓝 z]
+      f ∘ (extChartAt I p).symm := by
+    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
+    exact indicator_of_mem hy _
+  rw [heq.fderiv_eq, CovariantDerivative.chartMetric_apply,
+    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
+  change g.inner ((extChartAt I p).symm z)
+    (D (D.inverse (g.gradient f ((extChartAt I p).symm z)))) (D w) = _
+  rw [hD.self_apply_inverse]
+  change g.inner ((extChartAt I p).symm z)
+    (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
+  rw [g.inner_gradientAt, extDerivFun_apply_fixed_chart ((extChartAt I p).map_target hz) hf,
+    (extChartAt I p).right_inv hz]
+  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz
+  have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
+  change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
+  exact congrArg (fderiv ℝ (f ∘ (extChartAt I p).symm) z) hw
+
+/-- The inverse-chart pullback of the intrinsic gradient is the coordinate gradient. -/
+theorem transported_gradient_eq_coordGradient
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) :
+    CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z =
+      RicciFlow.RicciFlow.coordGradient (CovariantDerivative.chartMetric g.inner p)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z := by
+  let G := CovariantDerivative.chartMetric g.inner p
+  have hpos (v : E) (hv : v ≠ 0) : 0 < G z v v :=
+    CovariantDerivative.chartMetric_posDef g.inner
+      (fun y u hu ↦ g.inner_pos y hu) p
+      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
+  have hnondeg : (RicciFlow.RicciFlow.metricBilin (G z)).Nondegenerate := by
+    constructor
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+  have hinv : (G z).IsInvertible :=
+    CovariantDerivative.metric_isInvertible G
+      (RicciFlow.RicciFlow.metricBilin (G z)) hnondeg (fun _ _ ↦ rfl)
+  symm
+  apply hinv.inverse_apply_eq.mpr
+  ext w
+  exact (chartMetric_transported_gradient g p f hz hf w).symm
+
+/-- A smooth local metric extension transports the intrinsic Hessian to the
+ordinary second derivative with its Christoffel correction. -/
+theorem hessianAt_eq_blended_chart_hessian
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M)
+    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
+    (hχsupp : tsupport χ ⊆ (extChartAt I p).target)
+    (hχ0 : ∀ q, 0 ≤ χ q) (hχ1 : ∀ q, χ q ≤ 1)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hone : ∀ᶠ q in 𝓝 z, χ q = 1)
+    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f) (v w : E) :
+    let H := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
+    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
+      fderiv ℝ (fderiv ℝ u) z v w -
+        fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z v w) := by
+  intro H u D
+  have hpos (q : E) (hq : q ≠ 0) : 0 < innerSL ℝ q q := by
+    simpa only [innerSL_apply_apply] using (real_inner_self_pos.mpr hq)
+  have hsupp : ∀ q, χ q ≠ 0 →
+      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) q).IsInvertible := by
+    intro q hq
+    exact isInvertible_mfderivWithin_extChartAt_symm
+      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
+  have hH : ContDiff ℝ 1 H :=
+    CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
+      (m := 1) (by
+        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+        exact WithTop.coe_le_coe.mpr le_top) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
+  have hinv (q : E) : (H q).IsInvertible :=
+    CovariantDerivative.metric_isInvertible H
+      (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
+      (CovariantDerivative.chartBilin_nondegenerate χ (innerSL ℝ) hpos g.inner
+        (fun y v hv ↦ g.inner_pos y hv) p hχ0 hχ1 hsupp q) (fun _ _ ↦ rfl)
+  have hsym (q a b : E) : H q a b = H q b a :=
+    CovariantDerivative.blendedChartMetric_symm χ (innerSL ℝ)
+      (fun a b : E ↦ real_inner_comm b a)
+      g.inner (fun y a b ↦ g.inner_symm y a b) p q a b
+  have hu : ContDiff ℝ 2 u :=
+    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
+  let S := CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)
+  have heq : S =ᶠ[𝓝 z] RicciFlow.RicciFlow.coordGradient H u := by
+    filter_upwards [hone, (isOpen_extChartAt_target p).mem_nhds hz] with q hq hqt
+    have hg := transported_gradient_eq_coordGradient g p f hqt
+      (hf.contMDiffAt.mdifferentiableAt two_ne_zero)
+    have hHq : H q = CovariantDerivative.chartMetric g.inner p q :=
+      CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+        χ (innerSL ℝ) g.inner p hq
+    simpa only [RicciFlow.RicciFlow.coordGradient, hHq, S, u] using hg
+  have hbridge :=
+    LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
+      g χ (innerSL ℝ) hpos p hχ0 hχ1 hsupp (hH.differentiable one_ne_zero)
+      (fun a b : E ↦ real_inner_comm b a)
+      ((extChartAt I p).map_target hz)
+      (by simpa only [(extChartAt I p).right_inv hz] using hone)
+      (show MDiffAtTangentField (g.gradient f) ((extChartAt I p).symm z) from
+        g.mdifferentiableAt_gradient hf.contMDiffAt) (D v)
+  dsimp only [CovariantDerivative.chartTransportedLeviCivitaValueAt,
+    CovariantDerivative.chartTransportedLeviCivitaModelValue] at hbridge
+  rw [(extChartAt I p).right_inv hz] at hbridge
+  have hCD := congrArg (fun L : E →L[ℝ] E ↦ L v)
+    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz)
+  change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)) (D v) = v at hCD
+  have hbridge' : D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) =
+      (LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
+        ((extChartAt I p).symm z) (D v) :=
+    (congrArg (fun a ↦ D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos
+      g.inner (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) a)) hCD).symm.trans hbridge
+  have hmodel :
+      (CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+        (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v =
+      fderiv ℝ (RicciFlow.RicciFlow.coordGradient H u) z v +
+        RicciFlow.RicciFlow.christoffelClosedOp H z v
+          (RicciFlow.RicciFlow.coordGradient H u z) := by
+    rw [CovariantDerivative.chartLeviCivita, CovariantDerivative.modelLeviCivita_apply,
+      ← RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt H _ _ (fun _ _ ↦ rfl)]
+    rw [heq.fderiv_eq, heq.self_of_nhds]
+  have hresult := RicciFlow.RicciFlow.g_covariantDeriv_coordGradient_eq_covariantHessian'
+    H (hH.differentiable one_ne_zero z) hsym hinv hu v w
+  rw [← RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian H hsym hinv u z v w,
+    RicciFlow.RicciFlow.covariantHessianForm_apply] at hresult
+  rw [ClosedSmoothRiemannianMetric.hessianAt]
+  change g.inner ((extChartAt I p).symm z)
+    ((LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
+      ((extChartAt I p).symm z) (D v)) (D w) = _
+  rw [← hbridge']
+  change CovariantDerivative.chartMetric g.inner p z
+    ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) w = _
+  rw [hmodel, ← CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+    χ (innerSL ℝ) g.inner p hone.self_of_nhds]
+  exact hresult
+
+/-- The intrinsic Hessian in a genuine chart has the ordinary second derivative
+and the connection of the genuine chart metric. -/
+theorem hessianAt_eq_chart_derivatives
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M)
+    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    {z : E} (hz : z ∈ (extChartAt I p).target) (v w : E) :
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
+    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
+      fderiv ℝ (fderiv ℝ u) z v w - fderiv ℝ u z
+        (RicciFlow.RicciFlow.christoffelClosedOp
+          (CovariantDerivative.chartMetric g.inner p) z v w) := by
+  obtain ⟨χ, hχ, hχsupp, hone, hbounds⟩ :=
+    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
+      (isCompact_singleton (x := z)) (isOpen_extChartAt_target p)
+      (singleton_subset_iff.mpr hz)
+  have heq : CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p =ᶠ[𝓝 z]
+      CovariantDerivative.chartMetric g.inner p := by
+    filter_upwards [hone z (mem_singleton z)] with q hq
+    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+      χ (innerSL ℝ) g.inner p hq
+  have h := hessianAt_eq_blended_chart_hessian g p χ hχ hχsupp
+    (fun q ↦ (hbounds q).1) (fun q ↦ (hbounds q).2) hz
+    (hone z (mem_singleton z)) f hs hf v w
+  dsimp only at h ⊢
+  simpa only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
+    CovariantDerivative.christoffelFunctional, heq.self_of_nhds, heq.fderiv_eq] using h
+
+/-- Coordinates of a raised covector are its inverse-matrix contraction. -/
+theorem inverse_apply_coord
+    (G : ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
+    (hG : G.IsInvertible) (hs : ∀ v w, G v w = G w v)
+    (q : ClosedSmoothModel 3 →L[ℝ] ℝ) (k : Fin 3) :
+    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k (G.inverse q) =
+      ∑ m, DeTurckPrincipalSecondJet.inverseEntries G k m *
+        q (EuclideanSpace.basisFun (Fin 3) ℝ m) := by
+  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
+  let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord k))
+  have hp := DeTurckPrincipalIdentity.inverse_pairing_symm G hG hs
+    (LinearMap.toContinuousLinearMap (b.coord k)) q
+  change b.coord k (G.inverse q) = q r at hp
+  rw [hp]
+  have hr := congrArg q (b.sum_repr r)
+  calc
+    q r = ∑ m, b.repr r m * q (b m) := by
+      simpa only [map_sum, map_smul, smul_eq_mul] using hr.symm
+    _ = _ := by
+      rw [DeTurckPrincipalIdentity.inverseEntries_eq_coordinates G hG]
+      rfl
+
+/-- The closed Christoffel operator has the standard inverse-Gram coordinates. -/
+theorem christoffelClosedOp_coord
+    (G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
+    (z : ClosedSmoothModel 3) (hG : (G z).IsInvertible)
+    (hs : ∀ v w, G z v w = G z w v) (hd : DifferentiableAt ℝ G z)
+    (k i j : Fin 3) :
+    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k
+      (RicciFlow.RicciFlow.christoffelClosedOp G z
+        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
+      (1 / 2 : ℝ) * ∑ m, DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
+        (coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ m)) i z +
+         coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ m)) j z -
+         coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) m z) := by
+  have hderiv (a b v : ClosedSmoothModel 3) :
+      fderiv ℝ (fun q ↦ G q a b) z v = fderiv ℝ G z v a b := by
+    have h := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const a z)).clm_apply
+      (hasFDerivAt_const b z)
+    simpa using congrArg (fun L : ClosedSmoothModel 3 →L[ℝ] ℝ ↦ L v) h.fderiv
+  rw [RicciFlow.RicciFlow.christoffelClosedOp_apply, inverse_apply_coord (G z) hG hs]
+  simp only [LinearMap.coe_toContinuousLinearMap', CovariantDerivative.christoffelFunctional,
+    coordinateDirectionalDerivative, ← EuclideanSpace.basisFun_apply, hderiv, Finset.mul_sum]
+  apply Finset.sum_congr rfl
+  intro m _
+  dsimp
+  ring
+
+section Three
+variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
+  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
+  [ChartedSpace (ClosedSmoothModel 3) M₃]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
+local notation "I₃" => closedSmoothModelWithCorners 3
+local notation "E₃" => ClosedSmoothModel 3
+
+/-- The intrinsic Hessian entries in the inverse-chart frame have the standard
+coordinate second-derivative and Christoffel formula. -/
+theorem hessianAt_eq_coordinate_hessian
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
+    (f : M₃ → ℝ) (hs : tsupport f ⊆ (extChartAt I₃ p).source)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f)
+    {z : E₃} (hz : z ∈ (extChartAt I₃ p).target) (i j : Fin 3) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
+    let Γ := fun y k i j ↦ (1 / 2 : ℝ) * ∑ m, a y k m *
+      (coordinateDirectionalDerivative (fun q ↦ G q j m) i y +
+       coordinateDirectionalDerivative (fun q ↦ G q i m) j y -
+       coordinateDirectionalDerivative (fun q ↦ G q i j) m y)
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p f
+    let D := mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ p).symm (range I₃) z
+    g.hessianAt f ((extChartAt I₃ p).symm z)
+      (D (EuclideanSpace.basisFun (Fin 3) ℝ i))
+      (D (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
+      coordinateSecondDerivative u i j z - ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
+  intro G a Γ u D
+  let H := CovariantDerivative.chartMetric g.inner p
+  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
+  have hd : DifferentiableAt ℝ H z :=
+    (deTurckChartMetric_contDiffAt_two_of_mem_target g p hz).differentiableAt two_ne_zero
+  have hpos (v : E₃) (hv : v ≠ 0) : 0 < H z v v :=
+    CovariantDerivative.chartMetric_posDef g.inner (fun y v hv ↦ g.inner_pos y hv) p
+      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
+  have hnondeg : (RicciFlow.RicciFlow.metricBilin (H z)).Nondegenerate := by
+    constructor
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+  have hinv : (H z).IsInvertible := CovariantDerivative.metric_isInvertible H
+    (RicciFlow.RicciFlow.metricBilin (H z)) hnondeg (fun _ _ ↦ rfl)
+  have hcoord (k : Fin 3) : b.coord k
+      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = Γ z k i j :=
+    christoffelClosedOp_coord H z hinv
+      (CovariantDerivative.chartMetric_symm g.inner (fun y v w ↦ g.inner_symm y v w) p z) hd k i j
+  have hu : ContDiff ℝ 2 u := ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
+  have hsecond : coordinateSecondDerivative u i j z = fderiv ℝ (fderiv ℝ u) z (b i) (b j) := by
+    have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z
+    have h := hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (b j) z)
+    have hh := congrArg (fun L : E₃ →L[ℝ] ℝ ↦ L (b i)) h.fderiv
+    simpa [coordinateSecondDerivative, coordinateDirectionalDerivative, b,
+      EuclideanSpace.basisFun_apply] using hh
+  have hcorrect : fderiv ℝ u z
+      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
+      ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
+    have h := congrArg (fderiv ℝ u z)
+      (b.sum_repr (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)))
+    have hexp : fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
+        ∑ k, b.coord k (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) *
+          fderiv ℝ u z (b k) := by
+      simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] using h.symm
+    simp_rw [hcoord] at hexp
+    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
+      coordinateDirectionalDerivative] using hexp
+  rw [hessianAt_eq_chart_derivatives g p f hs hf hz]
+  change fderiv ℝ (fderiv ℝ u) z (b i) (b j) - fderiv ℝ u z
+    (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = _
+  rw [← hsecond, hcorrect]
+
+/-- The intrinsic scalar Laplacian equals the standard Christoffel-coordinate
+formula on each shrunk chart region. -/
+theorem laplacianAt_eq_christoffelCoordinateLaplacian
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
+    (V : Set M₃) (hV : closure V ⊆ (extChartAt I₃ p).source)
+    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 φ)
+    (z : (extChartAt I₃ p).target) (hz : (z : E₃) ∈ (extChartAt I₃ p) '' V) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
+    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
+      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
+       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
+       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
+    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
+      christoffelCoordinateLaplacian a Γ
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
+  intro G a Γ
+  have hs : tsupport φ ⊆ (extChartAt I₃ p).source :=
+    hφ.trans (subset_closure.trans hV)
+  have hzt : (z : E₃) ∈ (extChartAt I₃ p).target := by
+    obtain ⟨x, hx, hzx⟩ := hz
+    rw [← hzx]
+    exact (extChartAt I₃ p).map_source (hV (subset_closure hx))
+  rw [laplacianAt_eq_chart_hessian g φ p z]
+  unfold christoffelCoordinateLaplacian
+  apply Finset.sum_congr rfl
+  intro i _
+  apply Finset.sum_congr rfl
+  intro j _
+  exact congrArg (fun t : ℝ ↦ a z i j * t)
+    (hessianAt_eq_coordinate_hessian g p φ hs hf hzt i j)
+
+end Three
+
+/-- Restricting the genuine chart domain restricts the Riemannian chart measure. -/
+theorem restrictedChart_measure
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
+    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
+    HausdorffChartDensityEquality g U
+      (fun z ↦ inverseExtendedChartParametrization (n := n) p (Set.inclusion hsub z))
+      ((extChartAt I p).symm '' U)
+      (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)) := by
+  let ψ := inverseExtendedChartParametrization (n := n) p
+  let ι := Set.inclusion hsub
+  let μ := rawHausdorffCoordinateDensityMeasure (extChartAt I p).target
+    (inverseChartPullbackVolumeDensity g p)
+  have hψ : MeasurableEmbedding ψ :=
+    (inverseExtendedChartParametrization_isEmbedding (n := n) p).measurableEmbedding
+      (by rw [range_inverseExtendedChartParametrization]; exact (isOpen_extChartAt_source p).measurableSet)
+  have hmap := map_rawHausdorffCoordinateDensityMeasure_inclusion
+    (isOpen_extChartAt_target p).measurableSet hU hsub (inverseChartPullbackVolumeDensity g p)
+  have hres := hψ.restrict_map μ (ψ '' range ι)
+  rw [preimage_image_eq _ hψ.injective] at hres
+  have himage : ψ '' range ι = (extChartAt I p).symm '' U := by
+    ext x
+    constructor
+    · rintro ⟨q, ⟨z, rfl⟩, rfl⟩
+      exact ⟨z, z.2, rfl⟩
+    · rintro ⟨z, hz, rfl⟩
+      exact ⟨ι ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
+  have hsource : ψ '' range ι ⊆ (extChartAt I p).source := by
+    rintro x ⟨z, _, rfl⟩
+    exact (extChartAt I p).map_target z.2
+  change Measure.map (ψ ∘ ι) _ = _
+  rw [← Measure.map_map hψ.measurable (measurable_inclusion hsub), hmap, ← hres]
+  have hfull : Measure.map ψ μ = (volumeMeasure g).restrict (extChartAt I p).source :=
+    ClosedLaplacianStokesProducer.openChart_measure g p
+  rw [hfull, Measure.restrict_restrict_of_subset hsource, himage]
+
+/-- The genuine density remains integrable on a measurable subdomain of a chart. -/
+theorem restrictedChart_density_integrable
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
+    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
+    Integrable (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z))
+      (coordinateLebesgueMeasure U) := by
+  let δ := fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)
+  have hcont : Continuous δ := (continuous_inverseChartPullbackVolumeDensity g p).comp
+    (continuous_inclusion hsub)
+  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+  have hmeas : Measurable (fun z : U ↦ inverseExtendedChartParametrization (n := n) p
+      (Set.inclusion hsub z)) :=
+    (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable.comp
+    (measurable_inclusion hsub)
+  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (restrictedChart_measure g p hU hsub)
+  dsimp only at hmass
+  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
+    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
+  have hfinite : ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) * δ z)
+      ∂(coordinateLebesgueMeasure U) ≠ (⊤ : ℝ≥0∞) := by
+    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
+      Measure.restrict_univ] at hmass
+    rw [hmass]
+    letI := volumeMeasure_isFiniteMeasure g
+    exact measure_ne_top (volumeMeasure g) _
+  have hint := (lintegral_ofReal_ne_top_iff_integrable
+    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
+    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
+      (inverseChartPullbackVolumeDensity_pos g p (Set.inclusion hsub z)).le)).mp hfinite
+  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint
+
+omit [T2Space M] [IsManifold I ∞ M] in
+/-- Zero extension does not enlarge the coordinate support beyond the image
+of the manifold support. -/
+theorem coordinateScalar_tsupport_subset_image [CompactSpace M]
+    (p : M) (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source) :
+    tsupport (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) ⊆
+      (extChartAt I p) '' tsupport f := by
+  have hcompact : IsCompact ((extChartAt I p) '' tsupport f) :=
+    (isClosed_tsupport f).isCompact.image_of_continuousOn ((continuousOn_extChartAt p).mono hs)
+  apply closure_minimal _ hcompact.isClosed
+  intro z hz
+  by_cases hzt : z ∈ (extChartAt I p).target
+  · refine ⟨(extChartAt I p).symm z, ?_, (extChartAt I p).right_inv hzt⟩
+    apply subset_tsupport
+    simpa only [Function.mem_support, ClosedLaplacianStokesProducer.coordinateScalar,
+      indicator_of_mem hzt] using hz
+  · exact False.elim (hz (indicator_of_notMem hzt _))
+
+/-- A continuous coordinate divergence on a smaller open region suffices
+for continuity of the localized intrinsic Laplacian. -/
+theorem laplacian_continuous_of_restricted_coordinate_divergence
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (V : Set M)
+    (hV : IsOpen V) (hVs : V ⊆ (extChartAt I p).source)
+    (f : M → ℝ) (hs : tsupport f ⊆ V) (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    (w D : E → ℝ) (hw : Continuous w) (hD : Continuous D)
+    (hpos : ∀ z ∈ (extChartAt I p) '' V, 0 < w z)
+    (hcoord : ∀ z : (extChartAt I p).target, (z : E) ∈ (extChartAt I p) '' V →
+      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
+    Continuous (fun x ↦ g.laplacianAt f x) := by
+  have hformula (x : M) (hx : x ∈ V) :
+      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
+    let z : (extChartAt I p).target := ⟨extChartAt I p x, (extChartAt I p).map_source (hVs hx)⟩
+    have hinv : inverseExtendedChartParametrization (n := n) p z = x :=
+      (extChartAt I p).left_inv (hVs hx)
+    have hz : (z : E) ∈ (extChartAt I p) '' V := ⟨x, hx, rfl⟩
+    apply (eq_div_iff (hpos z hz).ne').mpr
+    simpa only [hinv, mul_comm] using hcoord z hz
+  apply continuous_iff_continuousAt.mpr
+  intro x
+  by_cases hx : x ∈ V
+  · have hc := (continuousOn_extChartAt p x (hVs hx)).continuousAt
+      ((isOpen_extChartAt_source p).mem_nhds (hVs hx))
+    have hquot := (hD.continuousAt.div hw.continuousAt
+      (hpos _ ⟨x, hx, rfl⟩).ne').comp hc
+    apply hquot.congr_of_eventuallyEq
+    filter_upwards [hV.mem_nhds hx] with y hy
+    exact hformula y hy
+  · have hxt : x ∉ tsupport f := fun h ↦ hx (hs h)
+    apply continuousAt_const.congr_of_eventuallyEq
+    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
+    calc
+      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
+        g.laplacianAt_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
+          (g.mdifferentiableAt_gradient hf.contMDiffAt)
+          (g.mdifferentiableAt_gradient contMDiffAt_const)
+      _ = 0 := g.laplacianAt_const 0 y
+
+/-- The Stokes geometry can use the coordinate images of a shrunk open cover. -/
+def geometry_of_shrunk_coordinate_coefficients
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    (C : FiniteExtendedChartCover (n := n) (M := M))
+    (V : Fin C.chartCount → Set M) (hV : ∀ i, IsOpen (V i))
+    (hVs : ∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source)
+    (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ) (hρ : ρ.IsSubordinate V)
+    (w : Fin C.chartCount → E → ℝ)
+    (a : Fin C.chartCount → E → Fin n → Fin n → ℝ)
+    (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
+    (hw : ∀ i, ContDiff ℝ 1 (w i))
+    (ha : ∀ i j k, ContDiff ℝ 1 (fun z ↦ a i z j k))
+    (hweight : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
+      w i z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g (C.anchor i) z)
+    (hcompat : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i → ∀ j,
+      (∑ k, fderiv ℝ (fun y ↦ w i y * a i y k j) z (EuclideanSpace.single k (1 : ℝ))) =
+        w i z * (-(∑ k, ∑ l, a i z k l * Γ i z j k l)))
+    (hcoord : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
+      g.laplacianAt (fun x ↦ ρ i x * f x)
+        (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
+      christoffelCoordinateLaplacian (a i) (Γ i)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z) :
+    FiniteSubordinateHausdorffLaplacianGeometry g f := by
+  let U := fun i ↦ (extChartAt I (C.anchor i)) '' V i
+  have hVs' (i) : V i ⊆ (extChartAt I (C.anchor i)).source := subset_closure.trans (hVs i)
+  have hsub (i) : U i ⊆ (extChartAt I (C.anchor i)).target :=
+    image_subset_iff.mpr fun _ hx ↦ (extChartAt I (C.anchor i)).map_source (hVs' i hx)
+  have hU (i) : MeasurableSet (U i) := by
+    have heq : U i = Subtype.val ''
+        (inverseExtendedChartParametrization (n := n) (C.anchor i) ⁻¹' V i) := by
+      ext z
+      constructor
+      · rintro ⟨x, hx, rfl⟩
+        refine ⟨⟨extChartAt I (C.anchor i) x, (extChartAt I (C.anchor i)).map_source (hVs' i hx)⟩, ?_, rfl⟩
+        change (extChartAt I (C.anchor i)).symm (extChartAt I (C.anchor i) x) ∈ V i
+        rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hx)]
+      · rintro ⟨z, hz, rfl⟩
+        exact ⟨(extChartAt I (C.anchor i)).symm z, hz, (extChartAt I (C.anchor i)).right_inv z.2⟩
+    rw [heq]
+    exact (MeasurableEmbedding.subtype_coe (isOpen_extChartAt_target (C.anchor i)).measurableSet).measurableSet_image.mpr
+      ((inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable
+        (hV i).measurableSet)
+  have himage (i) : (extChartAt I (C.anchor i)).symm '' U i = V i := by
+    ext x
+    constructor
+    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
+      rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hy)]
+    · intro hx
+      exact ⟨extChartAt I (C.anchor i) x, ⟨x, hx, rfl⟩,
+        (extChartAt I (C.anchor i)).left_inv (hVs' i hx)⟩
+  have hsV (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
+  have hs (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ (extChartAt I (C.anchor i)).source :=
+    (hsV i).trans (hVs' i)
+  have htwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  have hlocal (i) : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
+    ((ρ i).contMDiff.of_le htwo).mul hf
+  let u := fun i ↦ ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)
+  have hu (i) : ContDiff ℝ 2 (u i) :=
+    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two (C.anchor i) _ (hs i) (hlocal i)
+  have hcontinuous (i) : Continuous (fun x ↦ g.laplacianAt (fun y ↦ ρ i y * f y) x) := by
+    let F := coordinateMetricFluxComponent (w i) (a i) (u i)
+    have hF (k) : ContDiff ℝ 1 (F k) := coordinateMetricFluxComponent_contDiff_one (hw i) (ha i) (hu i) k
+    apply laplacian_continuous_of_restricted_coordinate_divergence g (C.anchor i) (V i)
+      (hV i) (hVs' i) _ (hsV i) (hlocal i) (w i) (euclideanCoordinateDivergence F) (hw i).continuous
+    · exact continuous_finsetSum _ fun k _ ↦ ((hF k).continuous_fderiv one_ne_zero).clm_apply continuous_const
+    · intro z hz
+      rw [hweight i ⟨z, hsub i hz⟩ hz]
+      have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+        exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+          (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+      exact mul_pos hscale (inverseChartPullbackVolumeDensity_pos g (C.anchor i) ⟨z, hsub i hz⟩)
+    · intro z hz
+      have hdiv := euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
+        (contractedChristoffel := fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l))
+        ((hw i).differentiable one_ne_zero z)
+        (fun j k ↦ (ha i j k).differentiable one_ne_zero z)
+        (fun j ↦ (coordinateDirectionalDerivative_contDiff_one (hu i) j).differentiable one_ne_zero z)
+        (hcompat i z hz)
+      rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
+        (a i) (Γ i) (fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l)) (u i) z (fun _ ↦ rfl)] at hdiv
+      rw [hcoord i z hz]
+      exact hdiv.symm
+  exact {
+    chartCount := C.chartCount
+    coordinateDomain := U
+    coordinateDomain_measurable := hU
+    inverseChart := fun i z ↦ inverseExtendedChartParametrization (n := n) (C.anchor i) (Set.inclusion (hsub i) z)
+    inverseChart_measurable := fun i ↦
+      (inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable.comp (measurable_inclusion (hsub i))
+    chartRegion := V
+    chartRegion_isOpen := hV
+    density := fun i z ↦ inverseChartPullbackVolumeDensity g (C.anchor i) (Set.inclusion (hsub i) z)
+    density_nonneg := fun i ↦ Eventually.of_forall fun z ↦ (inverseChartPullbackVolumeDensity_pos g (C.anchor i) (Set.inclusion (hsub i) z)).le
+    density_integrable := fun i ↦ restrictedChart_density_integrable g (C.anchor i) (hU i) (hsub i)
+    chartMeasure := fun i ↦ by
+      have h := restrictedChart_measure g (C.anchor i) (hU i) (hsub i)
+      rwa [himage i] at h
+    partition := ρ
+    partition_subordinate := hρ
+    f_contMDiff_two := hf
+    coordinateRepresentative := u
+    coordinateRepresentative_eq := fun i z ↦ indicator_of_mem (hsub i z.2) _
+    coordinateRepresentative_contDiff_two := hu
+    coordinateRepresentative_hasCompactSupport := fun i ↦
+      (ClosedLaplacianStokesProducer.coordinateScalar_support (C.anchor i) _ (hs i)).1
+    coordinateRepresentative_tsupport_subset_coordinateDomain := fun i ↦
+      (coordinateScalar_tsupport_subset_image (C.anchor i) _ (hs i)).trans (image_mono (hsV i))
+    weight := w
+    weight_contDiff_one := hw
+    weight_eq_density := fun i z ↦ hweight i (Set.inclusion (hsub i) z) z.2
+    inverseMetric := a
+    inverseMetric_contDiff_one := ha
+    christoffel := Γ
+    contractedChristoffel := fun i z j ↦ -(∑ k, ∑ l, a i z k l * Γ i z j k l)
+    contractedChristoffel_eq := fun _ _ _ ↦ rfl
+    density_inverseMetric_compatibility := fun i z ↦ hcompat i (Set.inclusion (hsub i) z) z.2
+    intrinsicCoordinateLaplacian_eq := fun i z ↦ hcoord i (Set.inclusion (hsub i) z) z.2
+    localizedLaplacian_aestronglyMeasurable := fun i ↦ (hcontinuous i).aestronglyMeasurable }
+
+section StokesThree
+variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
+  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
+  [ChartedSpace (ClosedSmoothModel 3) M₃]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
+local notation "I₃" => closedSmoothModelWithCorners 3
+local notation "E₃" => ClosedSmoothModel 3
+
+/-- On a closed smooth three-manifold the Laplacian of a C² scalar is
+integrable and its integral is zero. -/
+theorem closedLaplacianStokes_of_contMDiff_two
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ)
+    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
+    ClosedLaplacianStokes g f := by
+  letI : SecondCountableTopology M₃ := ChartedSpace.secondCountable_of_sigmaCompact E₃ M₃
+  let C := compactFiniteExtendedChartCover (n := 3) (M := M₃)
+  obtain ⟨V, ρ, w, a, _hcover, hV, hVs, _hcompact, hρ, hw, ha, hwe, hae⟩ :=
+    ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients g C
+  let G := fun i ↦ inverseChartPullbackGramMatrixField g (C.anchor i)
+  let A : Fin C.chartCount → E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun i z ↦ (G i z)⁻¹
+  let Γ := fun i z j k l ↦ (1 / 2 : ℝ) * ∑ m, A i z j m *
+    (coordinateDirectionalDerivative (fun y ↦ G i y l m) k z +
+     coordinateDirectionalDerivative (fun y ↦ G i y k m) l z -
+     coordinateDirectionalDerivative (fun y ↦ G i y k l) m z)
+  have hle1 : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  have hle2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  apply (geometry_of_shrunk_coordinate_coefficients g f hf C V hV hVs ρ hρ w a Γ
+    (fun i ↦ (hw i).of_le hle1) (fun i j k ↦ (ha i j k).of_le hle1) ?_ ?_ ?_).closedLaplacianStokes
+  · intro i z hz
+    rw [(hwe i z (image_mono subset_closure hz)).self_of_nhds]
+    exact (ClosedLaplacianStokesProducer.chartWeight_regular g (C.anchor i)).2 z
+  · intro i z hz j
+    exact ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
+      g (C.anchor i) (w i) (a i) z z.2
+      (hwe i z (image_mono subset_closure hz)) (hae i z (image_mono subset_closure hz)) j
+  · intro i z hz
+    have hlocal : ContMDiff I₃ 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
+      ((ρ i).contMDiff.of_le hle2).mul hf
+    have h := laplacianAt_eq_christoffelCoordinateLaplacian g (C.anchor i) (V i) (hVs i)
+      (fun x ↦ ρ i x * f x) (tsupport_mul_subset_left.trans (hρ i)) hlocal z hz
+    change g.laplacianAt (fun x ↦ ρ i x * f x)
+      (inverseExtendedChartParametrization (n := 3) (C.anchor i) z) =
+      christoffelCoordinateLaplacian (A i) (Γ i)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) (C.anchor i) (fun x ↦ ρ i x * f x)) z at h
+    rw [h]
+    unfold christoffelCoordinateLaplacian
+    have hval : a i z = A i z := (hae i z (image_mono subset_closure hz)).self_of_nhds
+    rw [hval]
+
+/-- Joint C³ metric entries supply the scalar C² input along a forward
+normalized Ricci flow. -/
+theorem closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
+    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) := by
+  intro t ht
+  apply closedLaplacianStokes_of_contMDiff_two
+  intro x
+  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow (hFlow t ht)
+    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hJoint t y)) x
+
+end StokesThree
+
+end Poincare.IntrinsicLaplacianCoordinateForm
```

## Actual command transcript

Each entry records the command, its real process exit code, and its combined
standard output and standard error. Empty output blocks mean no output.
Trailing whitespace is removed from reproduced output and diff context lines
to satisfy the repository whitespace check; the diagnostic text is unchanged.
Source deltas refer to the single new Lean module. When the probe includes
that entire module verbatim, only its additional diagnostic tail is repeated;
otherwise the complete diagnostic source is included.

### probe-001

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `1`.

Diagnostic source:

```lean
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.DeTurckPrincipalIdentity
noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm
open ClosedLaplacianStokesGlobalCoefficients
variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
 [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
 [ChartedSpace (ClosedSmoothModel 3) M₃]
 [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
example
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (V : Set M₃) (hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source)
    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 φ)
    (z : (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (hz : (z : ClosedSmoothModel 3) ∈ (extChartAt (closedSmoothModelWithCorners 3) p) '' V) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
      christoffelCoordinateLaplacian a Γ
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
  intro G a Γ
  have hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source :=
    hφ.trans (subset_closure.trans hV)
  have hu := ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p φ hsource hf
  have hcompat := density_inverseMetric_compatibility g p z z.2
  rw [g.laplacianAt_eq_trace_hessianContinuousAt]
  trace_state

#check DeTurckPrincipalIdentity.christoffel_eq_connection
#check DeTurckPrincipalIdentity.koszul_apply
#check LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:28:75: error: unsolved goals
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace (ClosedSmoothModel 3) M₃
inst✝ : IsManifold (closedSmoothModelWithCorners 3) ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
V : Set M₃
hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
φ : M₃ → ℝ
hφ : tsupport φ ⊆ V
hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ, ℝ) 2 φ
z : ↑(extChartAt (closedSmoothModelWithCorners 3) p).target
hz : ↑z ∈ ↑(extChartAt (closedSmoothModelWithCorners 3) p) '' V
G : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : ClosedSmoothModel 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y j k l =>
    1 / 2 *
      ∑ m,
        a y j m *
          (coordinateDirectionalDerivative (fun q => G q l m) k y +
              coordinateDirectionalDerivative (fun q => G q k m) l y -
            coordinateDirectionalDerivative (fun q => G q k l) m y)
hsource : tsupport φ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source
hu : ContDiff ℝ 2 (ClosedLaplacianStokesProducer.coordinateScalar p φ)
hcompat :
  ∀ (j : Fin 3),
    ∑ k,
        (fderiv ℝ
            (fun y =>
              (fun z =>
                    ↑(rawHausdorffLebesgueScale 3) *
                      VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
                  y *
                (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) y k j)
            ↑z)
          (EuclideanSpace.single k 1) =
      (fun z =>
            ↑(rawHausdorffLebesgueScale 3) *
              VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
          ↑z *
        -∑ k,
            ∑ l,
              (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) (↑z) k l *
                (fun z j k l =>
                    1 / 2 *
                      ∑ m,
                        (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹) z j m *
                          (coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y l m) k
                                z +
                              coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k m) l
                                z -
                            coordinateDirectionalDerivative (fun y => inverseChartPullbackGramMatrixField g p y k l) m
                              z))
                  (↑z) j k l
⊢ (LinearMap.trace ℝ (TangentSpace (closedSmoothModelWithCorners 3) (inverseExtendedChartParametrization p z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization p z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ ↑(g.hessianContinuousAt φ (inverseExtendedChartParametrization p z))) =
    christoffelCoordinateLaplacian a Γ (ClosedLaplacianStokesProducer.coordinateScalar p φ) ↑z
Poincare.DeTurckPrincipalIdentity.christoffel_eq_connection.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace DeTurckPrincipalSecondJet.E M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (g : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (z : DeTurckPrincipalSecondJet.E)
  (hcut : ∀ᶠ (y : ClosedSmoothModel 3) in 𝓝 z, GeodesicTransport.cutoff anchor y = 1)
  (u v : DeTurckPrincipalSecondJet.E) :
  ((GeodesicTransport.chartChristoffelField g anchor z) u) v =
    DeTurckPrincipalIdentity.connection (CovariantDerivative.chartMetric g.inner anchor z)
      (fderiv ℝ (CovariantDerivative.chartMetric g.inner anchor) z) u v
Poincare.DeTurckPrincipalIdentity.koszul_apply (J : DeTurckPrincipalSecondJet.Jet1)
  (u v q : DeTurckPrincipalSecondJet.E) :
  (DeTurckPrincipalIdentity.koszul J u v) q = 1 / 2 * (((J u) v) q + ((J v) u) q - ((J q) u) v)
Poincare.LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M] (g : ClosedSmoothRiemannianMetric n M) (χ : ClosedSmoothModel n → ℝ)
  (G₀ : ClosedSmoothModel n →L[ℝ] ClosedSmoothModel n →L[ℝ] ℝ)
  (hG₀pos : ∀ (v : ClosedSmoothModel n), v ≠ 0 → 0 < (G₀ v) v) (x₀ : M) (hχ0 : ∀ (z : ClosedSmoothModel n), 0 ≤ χ z)
  (hχ1 : ∀ (z : ClosedSmoothModel n), χ z ≤ 1)
  (hsupp :
    ∀ (z : ClosedSmoothModel n),
      χ z ≠ 0 →
        (mfderivWithin 𝓘(ℝ, ClosedSmoothModel n) (closedSmoothModelWithCorners n)
            (↑(extChartAt (closedSmoothModelWithCorners n) x₀).symm) (range ↑(closedSmoothModelWithCorners n))
            z).IsInvertible)
  (hbl : Differentiable ℝ (CovariantDerivative.blendedChartMetric χ G₀ g.inner x₀))
  (hG₀symm : ∀ (v w : ClosedSmoothModel n), (G₀ v) w = (G₀ w) v)
  {σ : (y : M) → TangentSpace (closedSmoothModelWithCorners n) y} {y : M}
  (hy : y ∈ (extChartAt (closedSmoothModelWithCorners n) x₀).source)
  (hχone : ∀ᶠ (z' : ClosedSmoothModel n) in 𝓝 (↑(extChartAt (closedSmoothModelWithCorners n) x₀) y), χ z' = 1)
  (hσ : MDiffAtTangentField σ y) (v : TangentSpace (closedSmoothModelWithCorners n) y) :
  CovariantDerivative.chartTransportedLeviCivitaValueAt χ G₀ hG₀pos g.inner ⋯ x₀ hχ0 hχ1 hsupp σ hy v =
    (↑(LeviCivitaExistence.closedLeviCivitaConnection g) σ y) v
```

### probe-002

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -0,0 +1,33 @@
+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
+import Poincare.Global.DeTurckPrincipalIdentity
+
+noncomputable section
+open Bundle FiberBundle Filter MeasureTheory Set
+open scoped Manifold ContDiff Topology ENNReal NNReal
+set_option autoImplicit false
+universe u
+namespace Poincare.IntrinsicLaplacianCoordinateForm
+
+variable {n : ℕ} {M : Type u}
+variable [TopologicalSpace M] [T2Space M]
+variable [ChartedSpace (ClosedSmoothModel n) M]
+variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+local notation "I" => closedSmoothModelWithCorners n
+local notation "E" => ClosedSmoothModel n
+local notation "TM" => (TangentSpace I : M → Type _)
+
+/-- The intrinsic Hessian trace contracts with the inverse Gram matrix in any basis. -/
+theorem laplacianAt_eq_inverseGram_hessian
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (x : M)
+    {d : ℕ} (b : Module.Basis (Fin d) ℝ (TM x)) :
+    g.laplacianAt f x = ∑ i, ∑ j,
+      (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
+  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
+  rw [g.laplacianAt_eq_sum_hessianAt_basis f x b]
+  apply Finset.sum_congr rfl
+  intro i _
+  rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
+  change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
+  simp only [map_sum, map_smul, smul_eq_mul, g.hessianDualAt_apply]
+
+end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:26:8: error(lean.invalidField): Invalid field `laplacianAt_eq_sum_hessianAt_basis`: The environment does not contain `Bundle.ContMDiffRiemannianMetric.laplacianAt_eq_sum_hessianAt_basis`, so it is not possible to project the field `laplacianAt_eq_sum_hessianAt_basis` from an expression
  g
of type
  ContMDiffRiemannianMetric I ∞ E fun x => TangentSpace I x
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:24:75: error: unsolved goals
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
x : M
d : ℕ
b : Module.Basis (Fin d) ℝ (TangentSpace I x)
this : FiniteDimensional ℝ (TangentSpace I x) := laplacianAt_eq_inverseGram_hessian._proof_1_1 x
⊢ g.laplacianAt f x = ∑ i, ∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j)
```

### probe-003

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -23,7 +23,7 @@
     g.laplacianAt f x = ∑ i, ∑ j,
       (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
   letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
-  rw [g.laplacianAt_eq_sum_hessianAt_basis f x b]
+  rw [ClosedSmoothRiemannianMetric.laplacianAt_eq_sum_hessianAt_basis g f x b]
   apply Finset.sum_congr rfl
   intro i _
   rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:26:6: error(lean.unknownIdentifier): Unknown constant `Poincare.ClosedSmoothRiemannianMetric.laplacianAt_eq_sum_hessianAt_basis`
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:24:75: error: unsolved goals
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
x : M
d : ℕ
b : Module.Basis (Fin d) ℝ (TangentSpace I x)
this : FiniteDimensional ℝ (TangentSpace I x) := laplacianAt_eq_inverseGram_hessian._proof_1_1 x
⊢ g.laplacianAt f x = ∑ i, ∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j)
```

### probe-004

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -23,7 +23,7 @@
     g.laplacianAt f x = ∑ i, ∑ j,
       (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j) := by
   letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
-  rw [ClosedSmoothRiemannianMetric.laplacianAt_eq_sum_hessianAt_basis g f x b]
+  rw [Poincare.laplacianAt_eq_sum_hessianAt_basis g f x b]
   apply Finset.sum_congr rfl
   intro i _
   rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:24:75: error: unsolved goals
n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
x : M
d : ℕ
b : Module.Basis (Fin d) ℝ (TangentSpace I x)
this : FiniteDimensional ℝ (TangentSpace I x) := laplacianAt_eq_inverseGram_hessian._proof_1_1 x
i : Fin d
a✝ : i ∈ Finset.univ
⊢ g.hessianAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) =
    ∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j * g.hessianAt f x (b i) (b j)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:31:13: warning: This simp argument is unused:
  map_sum

Hint: Omit it from the simp argument list.
  simp only [map_su̵m,̵ ̵m̵a̵p̵_̵s̵m̵ul, smul_eq_mul, g.hessianDualAt_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:31:22: warning: This simp argument is unused:
  map_smul

Hint: Omit it from the simp argument list.
  simp only [map_sum, m̵a̵p̵_̵smul,̵ ̵s̵m̵u̵l̵_eq_mul, g.hessianDualAt_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:31:32: warning: This simp argument is unused:
  smul_eq_mul

Hint: Omit it from the simp argument list.
  simp only [map_sum, map_smul, s̵m̵u̵l̵_̵e̵q̵_̵m̵u̵l̵,̵ ̵g.hessianDualAt_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### probe-005

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -28,6 +28,8 @@
   intro i _
   rw [g.metricDualVectorAt_basis_coord_eq_sum_inv x b i]
   change g.hessianDualAt f x (b i) (∑ j, (g.metricMatrixInBasisAt x b)⁻¹ i j • b j) = _
-  simp only [map_sum, map_smul, smul_eq_mul, g.hessianDualAt_apply]
+  rw [map_sum]
+  simp only [map_smul, smul_eq_mul]
+  rfl

 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-006

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-007

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-008

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-009

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -32,4 +32,22 @@
   simp only [map_smul, smul_eq_mul]
   rfl

+/-- In the inverse-chart frame the Laplacian uses the genuine inverse Gram field. -/
+theorem laplacianAt_eq_chart_hessian
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (p : M)
+    (z : (extChartAt I p).target) :
+    g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
+      ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
+        g.hessianAt f ((extChartAt I p).symm z)
+          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+            (EuclideanSpace.basisFun (Fin n) ℝ i))
+          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+            (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
+  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
+  have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
+      inverseChartPullbackGramMatrixField g p z := by
+    exact inverseChartPullbackGramMatrix_eq_field g p z
+  rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
+  simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:49:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:50:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  g.laplacianAt f (↑(extChartAt I p).symm ↑z)
in the target expression
  g.laplacianAt f (inverseExtendedChartParametrization p z) =
    ∑ i,
      ∑ j,
        (inverseChartPullbackGramMatrixField g p ↑z)⁻¹ i j *
          g.hessianAt f (↑(extChartAt I p).symm ↑z)
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) i))
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) j))

n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
p : M
z : ↑(extChartAt I p).target
b : Module.Basis (Fin n) ℝ (TangentSpace I (↑(extChartAt I p).symm ↑z)) :=
  ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p ⋯
hG : g.metricMatrixInBasisAt (↑(extChartAt I p).symm ↑z) b = inverseChartPullbackGramMatrixField g p ↑z
⊢ g.laplacianAt f (inverseExtendedChartParametrization p z) =
    ∑ i,
      ∑ j,
        (inverseChartPullbackGramMatrixField g p ↑z)⁻¹ i j *
          g.hessianAt f (↑(extChartAt I p).symm ↑z)
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) i))
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) j))
```

### probe-010

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `1`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:49:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:50:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  g.laplacianAt f (↑(extChartAt I p).symm ↑z)
in the target expression
  g.laplacianAt f (inverseExtendedChartParametrization p z) =
    ∑ i,
      ∑ j,
        (inverseChartPullbackGramMatrixField g p ↑z)⁻¹ i j *
          g.hessianAt f (↑(extChartAt I p).symm ↑z)
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) i))
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) j))

n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
p : M
z : ↑(extChartAt I p).target
b : Module.Basis (Fin n) ℝ (TangentSpace I (↑(extChartAt I p).symm ↑z)) :=
  ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p ⋯
hG : g.metricMatrixInBasisAt (↑(extChartAt I p).symm ↑z) b = inverseChartPullbackGramMatrixField g p ↑z
⊢ g.laplacianAt f (inverseExtendedChartParametrization p z) =
    ∑ i,
      ∑ j,
        (inverseChartPullbackGramMatrixField g p ↑z)⁻¹ i j *
          g.hessianAt f (↑(extChartAt I p).symm ↑z)
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) i))
            ((mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) ↑z) ((EuclideanSpace.basisFun (Fin n) ℝ) j))
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

### probe-011

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -46,7 +46,12 @@
   let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p z.2
   have hG : g.metricMatrixInBasisAt ((extChartAt I p).symm z) b =
       inverseChartPullbackGramMatrixField g p z := by
-    exact inverseChartPullbackGramMatrix_eq_field g p z
+    ext i j
+    simp only [ClosedSmoothRiemannianMetric.metricMatrixInBasisAt_apply,
+      ClosedSmoothRiemannianMetric.metricBilinAt_apply, b,
+      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
+    rfl
+  change g.laplacianAt f ((extChartAt I p).symm z) = _
   rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
   simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]

```

Actual output:

```text
```

### probe-012

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-013

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-014

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-015

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -55,4 +55,33 @@
   rw [laplacianAt_eq_inverseGram_hessian g f _ b, hG]
   simp only [b, ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]

+/-- Pairing the transported intrinsic gradient with the chart metric gives the
+ordinary differential of the coordinate scalar. -/
+theorem chartMetric_transported_gradient
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) (w : E) :
+    CovariantDerivative.chartMetric g.inner p z
+      (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z) w =
+      fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z w := by
+  let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+  have hD : D.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
+  have heq : ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f =ᶠ[𝓝 z]
+      f ∘ (extChartAt I p).symm := by
+    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
+    exact indicator_of_mem hy _
+  rw [heq.fderiv_eq, CovariantDerivative.chartMetric_apply,
+    CovariantDerivative.chartTransportedLeviCivitaSection_apply]
+  change g.inner ((extChartAt I p).symm z)
+    (D (D.inverse (g.gradient f ((extChartAt I p).symm z)))) (D w) = _
+  rw [hD.self_apply_inverse]
+  change g.inner ((extChartAt I p).symm z)
+    (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
+  rw [g.inner_gradientAt, extDerivFun_apply_fixed_chart ((extChartAt I p).map_target hz) hf,
+    (extChartAt I p).right_inv hz]
+  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := p) hz
+  have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
+  change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
+  rw [hw]
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:82:69: error: unexpected token ':='; expected ')', ',' or ':'
```

### probe-016

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -79,7 +79,7 @@
     (g.gradientAt f ((extChartAt I p).symm z)) (D w) = _
   rw [g.inner_gradientAt, extDerivFun_apply_fixed_chart ((extChartAt I p).map_target hz) hf,
     (extChartAt I p).right_inv hz]
-  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := p) hz
+  have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz
   have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
   change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
   rw [hw]
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:85:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D w)
in the target expression
  (fderiv ℝ (f ∘ ↑(extChartAt I p).symm) z) ((mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D w)) =
    (fderiv ℝ (f ∘ ↑(extChartAt I p).symm) z) w

n : ℕ
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : T2Space M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
p : M
f : M → ℝ
z : E
hz : z ∈ (extChartAt I p).target
hf : MDiffAt f (↑(extChartAt I p).symm z)
w : E
D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I (↑(extChartAt I p).symm z) :=
  mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z
hD : D.IsInvertible
heq : ClosedLaplacianStokesProducer.coordinateScalar p f =ᶠ[𝓝 z] f ∘ ↑(extChartAt I p).symm
hc :
  (mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)).comp
      (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z) =
    ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) z)
hw : (mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D w) = w
⊢ (fderiv ℝ (f ∘ ↑(extChartAt I p).symm) z) ((mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D w)) =
    (fderiv ℝ (f ∘ ↑(extChartAt I p).symm) z) w
```

### probe-017

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -82,6 +82,6 @@
   have hc := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz
   have hw := congrArg (fun L : E →L[ℝ] E ↦ L w) hc
   change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
-  rw [hw]
+  exact congrArg (fderiv ℝ (f ∘ (extChartAt I p).symm) z) hw

 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-018

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-019

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-020

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-021

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -84,4 +84,33 @@
   change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z) (D w) = w at hw
   exact congrArg (fderiv ℝ (f ∘ (extChartAt I p).symm) z) hw

+/-- The inverse-chart pullback of the intrinsic gradient is the coordinate gradient. -/
+theorem transported_gradient_eq_coordGradient
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I p).symm z)) :
+    CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f) z =
+      RicciFlow.RicciFlow.coordGradient (CovariantDerivative.chartMetric g.inner p)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) z := by
+  let G := CovariantDerivative.chartMetric g.inner p
+  have hpos (v : E) (hv : v ≠ 0) : 0 < G z v v :=
+    CovariantDerivative.chartMetric_posDef g.inner
+      (fun y u hu ↦ g.inner_pos y hu) p
+      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
+  have hnondeg : (RicciFlow.RicciFlow.metricBilin (G z)).Nondegenerate := by
+    constructor
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+  have hinv : (G z).IsInvertible :=
+    CovariantDerivative.metric_isInvertible G
+      (RicciFlow.RicciFlow.metricBilin (G z)) hnondeg (fun _ _ ↦ rfl)
+  symm
+  apply hinv.inverse_apply_eq.mpr
+  ext w
+  exact (chartMetric_transported_gradient g p f hz hf w).symm
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-022

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-023

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-024

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-025

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -113,4 +113,93 @@
   ext w
   exact (chartMetric_transported_gradient g p f hz hf w).symm

+/-- A smooth local metric extension transports the intrinsic Hessian to the
+ordinary second derivative with its Christoffel correction. -/
+theorem hessianAt_eq_blended_chart_hessian
+    [CompactSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M)
+    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
+    (hχsupp : tsupport χ ⊆ (extChartAt I p).target)
+    (hχ0 : ∀ q, 0 ≤ χ q) (hχ1 : ∀ q, χ q ≤ 1)
+    {z : E} (hz : z ∈ (extChartAt I p).target)
+    (hone : ∀ᶠ q in 𝓝 z, χ q = 1)
+    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f) (v w : E) :
+    let H := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
+    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
+      fderiv ℝ (fderiv ℝ u) z v w -
+        fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z v w) := by
+  intro H u D
+  have hpos (q : E) (hq : q ≠ 0) : 0 < innerSL ℝ q q := by
+    simpa only [innerSL_apply_apply] using (real_inner_self_pos.mpr hq)
+  have hsupp : ∀ q, χ q ≠ 0 →
+      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) q).IsInvertible := by
+    intro q hq
+    exact isInvertible_mfderivWithin_extChartAt_symm
+      (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
+  have hH : ContDiff ℝ 1 H :=
+    CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
+      (by simp) hχ hχsupp (g.contMDiff_inner.of_le (by simp))
+  have hinv (q : E) : (H q).IsInvertible :=
+    CovariantDerivative.metric_isInvertible H
+      (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
+      (CovariantDerivative.chartBilin_nondegenerate χ (innerSL ℝ) hpos g.inner
+        (fun y v hv ↦ g.inner_pos y hv) p hχ0 hχ1 hsupp q) (fun _ _ ↦ rfl)
+  have hsym (q a b : E) : H q a b = H q b a :=
+    CovariantDerivative.blendedChartMetric_symm χ (innerSL ℝ)
+      (fun a b ↦ by simp only [innerSL_apply_apply, real_inner_comm])
+      g.inner (fun y a b ↦ g.inner_symm y a b) p q a b
+  have hu : ContDiff ℝ 2 u :=
+    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
+  let S := CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)
+  have heq : S =ᶠ[𝓝 z] RicciFlow.RicciFlow.coordGradient H u := by
+    filter_upwards [hone, (isOpen_extChartAt_target p).mem_nhds hz] with q hq hqt
+    have hg := transported_gradient_eq_coordGradient g p f hqt
+      (hf.contMDiffAt.mdifferentiableAt two_ne_zero)
+    have hHq : H q = CovariantDerivative.chartMetric g.inner p q :=
+      CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+        χ (innerSL ℝ) g.inner p hq
+    simpa only [RicciFlow.RicciFlow.coordGradient, hHq, S, u] using hg
+  have hbridge :=
+    LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
+      g χ (innerSL ℝ) hpos p hχ0 hχ1 hsupp (hH.differentiable one_ne_zero)
+      (fun a b ↦ by simp only [innerSL_apply_apply, real_inner_comm])
+      ((extChartAt I p).map_target hz)
+      (by simpa only [(extChartAt I p).right_inv hz] using hone)
+      (show MDiffAtTangentField (g.gradient f) ((extChartAt I p).symm z) from
+        g.mdifferentiableAt_gradient hf.contMDiffAt) (D v)
+  dsimp only [CovariantDerivative.chartTransportedLeviCivitaValueAt,
+    CovariantDerivative.chartTransportedLeviCivitaModelValue] at hbridge
+  rw [(extChartAt I p).right_inv hz] at hbridge
+  have hCD := congrArg (fun L : E →L[ℝ] E ↦ L v)
+    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz)
+  change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)) (D v) = v at hCD
+  rw [hCD] at hbridge
+  have hmodel :
+      (CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+        (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v =
+      fderiv ℝ (RicciFlow.RicciFlow.coordGradient H u) z v +
+        RicciFlow.RicciFlow.christoffelClosedOp H z v
+          (RicciFlow.RicciFlow.coordGradient H u z) := by
+    rw [CovariantDerivative.chartLeviCivita, CovariantDerivative.modelLeviCivita_apply,
+      ← RicciFlow.RicciFlow.christoffelClosedOp_eq_christoffelAt H _ _ (fun _ _ ↦ rfl)]
+    rw [heq.fderiv_eq, heq.self_of_nhds]
+  have hresult := RicciFlow.RicciFlow.g_covariantDeriv_coordGradient_eq_covariantHessian'
+    H (hH.differentiable one_ne_zero z) hsym hinv hu v w
+  rw [← RicciFlow.RicciFlow.covariantHessianForm_eq_covariantHessian H hsym hinv u z v w,
+    RicciFlow.RicciFlow.covariantHessianForm_apply] at hresult
+  rw [ClosedSmoothRiemannianMetric.hessianAt]
+  change g.inner ((extChartAt I p).symm z)
+    ((LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
+      ((extChartAt I p).symm z) (D v)) (D w) = _
+  rw [← hbridge]
+  change CovariantDerivative.chartMetric g.inner p z
+    ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) w = _
+  rw [hmodel, ← CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+    χ (innerSL ℝ) g.inner p hone.self_of_nhds]
+  exact hresult
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:144:10: error: `simp` made no progress
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:152:20: error: `simp` made no progress
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:155:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  ConnectedSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:168:20: error: `simp` made no progress
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:179:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D v)
in the target expression
  (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z)
      ((↑(CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner ⋯ p hχ0 hχ1 hsupp)
          (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)) z)
        ((mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D v))) =
    (↑(LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f) (↑(extChartAt I p).symm z)) (D v)

n : ℕ
M : Type u
inst✝⁴ : TopologicalSpace M
inst✝³ : T2Space M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : CompactSpace M
g : ClosedSmoothRiemannianMetric n M
p : M
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχsupp : tsupport χ ⊆ (extChartAt I p).target
hχ0 : ∀ (q : E), 0 ≤ χ q
hχ1 : ∀ (q : E), χ q ≤ 1
z : E
hz : z ∈ (extChartAt I p).target
hone : ∀ᶠ (q : E) in 𝓝 z, χ q = 1
f : M → ℝ
hs : tsupport f ⊆ (extChartAt I p).source
hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f
v w : E
H : E → E →L[ℝ] E →L[ℝ] ℝ := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
u : E → ℝ := ClosedLaplacianStokesProducer.coordinateScalar p f
D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I (↑(extChartAt I p).symm z) :=
  mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z
hpos : ∀ (q : E), q ≠ 0 → 0 < ((innerSL ℝ) q) q
hsupp : ∀ (q : E), χ q ≠ 0 → (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) q).IsInvertible
hH : ContDiff ℝ 1 H
hinv : ∀ (q : E), (H q).IsInvertible
hsym : ∀ (q a b : E), ((H q) a) b = ((H q) b) a
hu : ContDiff ℝ 2 u
S : (z : E) → TangentSpace 𝓘(ℝ, E) z := CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)
heq : S =ᶠ[𝓝 z] RicciFlow.RicciFlow.coordGradient H u
hbridge :
  (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z)
      ((↑(CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner ⋯ p hχ0 hχ1 hsupp)
          (CovariantDerivative.chartTransportedLeviCivitaSection p (g.gradient f)) z)
        ((mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D v))) =
    (↑(LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f) (↑(extChartAt I p).symm z)) (D v)
hCD : (mfderiv% ↑(extChartAt I p) (↑(extChartAt I p).symm z)) (D v) = v
⊢ g.hessianAt f (↑(extChartAt I p).symm z) (D v) (D w) =
    ((fderiv ℝ (fderiv ℝ u) z) v) w - (fderiv ℝ u z) ((RicciFlow.RicciFlow.christoffelClosedOp H z v) w)
```

### probe-026

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -116,7 +116,7 @@
 /-- A smooth local metric extension transports the intrinsic Hessian to the
 ordinary second derivative with its Christoffel correction. -/
 theorem hessianAt_eq_blended_chart_hessian
-    [CompactSpace M]
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
     (g : ClosedSmoothRiemannianMetric n M) (p : M)
     (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
     (hχsupp : tsupport χ ⊆ (extChartAt I p).target)
@@ -141,7 +141,7 @@
       (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
   have hH : ContDiff ℝ 1 H :=
     CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
-      (by simp) hχ hχsupp (g.contMDiff_inner.of_le (by simp))
+      (m := 1) (by norm_num) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
   have hinv (q : E) : (H q).IsInvertible :=
     CovariantDerivative.metric_isInvertible H
       (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
@@ -149,7 +149,7 @@
         (fun y v hv ↦ g.inner_pos y hv) p hχ0 hχ1 hsupp q) (fun _ _ ↦ rfl)
   have hsym (q a b : E) : H q a b = H q b a :=
     CovariantDerivative.blendedChartMetric_symm χ (innerSL ℝ)
-      (fun a b ↦ by simp only [innerSL_apply_apply, real_inner_comm])
+      (fun a b : E ↦ real_inner_comm b a)
       g.inner (fun y a b ↦ g.inner_symm y a b) p q a b
   have hu : ContDiff ℝ 2 u :=
     ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
@@ -165,7 +165,7 @@
   have hbridge :=
     LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
       g χ (innerSL ℝ) hpos p hχ0 hχ1 hsupp (hH.differentiable one_ne_zero)
-      (fun a b ↦ by simp only [innerSL_apply_apply, real_inner_comm])
+      (fun a b : E ↦ real_inner_comm b a)
       ((extChartAt I p).map_target hz)
       (by simpa only [(extChartAt I p).right_inv hz] using hone)
       (show MDiffAtTangentField (g.gradient f) ((extChartAt I p).symm z) from
@@ -176,7 +176,12 @@
   have hCD := congrArg (fun L : E →L[ℝ] E ↦ L v)
     (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (x := p) hz)
   change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)) (D v) = v at hCD
-  rw [hCD] at hbridge
+  have hbridge' : D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
+      (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) =
+      (LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
+        ((extChartAt I p).symm z) (D v) :=
+    (congrArg (fun a ↦ D ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos
+      g.inner (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) a)) hCD).symm.trans hbridge
   have hmodel :
       (CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
         (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v =
@@ -194,7 +199,7 @@
   change g.inner ((extChartAt I p).symm z)
     ((LeviCivitaExistence.closedLeviCivitaConnection g) (g.gradient f)
       ((extChartAt I p).symm z) (D v)) (D w) = _
-  rw [← hbridge]
+  rw [← hbridge']
   change CovariantDerivative.chartMetric g.inner p z
     ((CovariantDerivative.chartLeviCivita χ (innerSL ℝ) hpos g.inner
       (fun y a ha ↦ g.inner_pos y ha) p hχ0 hχ1 hsupp S z) v) w = _
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:144:16: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : ChartedSpace E M
inst✝⁴ : IsManifold I ∞ M
inst✝³ : CompactSpace M
inst✝² : ConnectedSpace M
inst✝¹ : MeasurableSpace M
inst✝ : BorelSpace M
g : ClosedSmoothRiemannianMetric n M
p : M
χ : E → ℝ
hχ : ContDiff ℝ ∞ χ
hχsupp : tsupport χ ⊆ (extChartAt I p).target
hχ0 : ∀ (q : E), 0 ≤ χ q
hχ1 : ∀ (q : E), χ q ≤ 1
z : E
hz : z ∈ (extChartAt I p).target
hone : ∀ᶠ (q : E) in 𝓝 z, χ q = 1
f : M → ℝ
hs : tsupport f ⊆ (extChartAt I p).source
hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f
v w : E
H : E → E →L[ℝ] E →L[ℝ] ℝ := CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p
u : E → ℝ := ClosedLaplacianStokesProducer.coordinateScalar p f
D : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I (↑(extChartAt I p).symm z) :=
  mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) z
hpos : ∀ (q : E), q ≠ 0 → 0 < ((innerSL ℝ) q) q
hsupp : ∀ (q : E), χ q ≠ 0 → (mfderivWithin 𝓘(ℝ, E) I (↑(extChartAt I p).symm) (range ↑I) q).IsInvertible
⊢ 2 ≤ ∞
```

### probe-027

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -141,7 +141,9 @@
       (hχsupp (subset_tsupport χ (Function.mem_support.mpr hq)))
   have hH : ContDiff ℝ 1 H :=
     CovariantDerivative.contDiff_blendedChartMetric χ (innerSL ℝ) g.inner p
-      (m := 1) (by norm_num) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
+      (m := 1) (by
+        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+        exact WithTop.coe_le_coe.mpr le_top) hχ hχsupp (g.contMDiff_inner.of_le (by norm_num))
   have hinv (q : E) : (H q).IsInvertible :=
     CovariantDerivative.metric_isInvertible H
       (CovariantDerivative.chartBilin χ (innerSL ℝ) g.inner p q)
```

Actual output:

```text
```

### probe-028

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-029

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-030

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-031

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -209,4 +209,34 @@
     χ (innerSL ℝ) g.inner p hone.self_of_nhds]
   exact hresult

+/-- The intrinsic Hessian in a genuine chart has the ordinary second derivative
+and the connection of the genuine chart metric. -/
+theorem hessianAt_eq_chart_derivatives
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M)
+    (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    {z : E} (hz : z ∈ (extChartAt I p).target) (v w : E) :
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f
+    let D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) z
+    g.hessianAt f ((extChartAt I p).symm z) (D v) (D w) =
+      fderiv ℝ (fderiv ℝ u) z v w - fderiv ℝ u z
+        (RicciFlow.RicciFlow.christoffelClosedOp
+          (CovariantDerivative.chartMetric g.inner p) z v w) := by
+  obtain ⟨χ, hχ, hχsupp, hone, hbounds⟩ :=
+    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact
+      (isCompact_singleton (x := z)) (isOpen_extChartAt_target p)
+      (singleton_subset_iff.mpr hz)
+  have heq : CovariantDerivative.blendedChartMetric χ (innerSL ℝ) g.inner p =ᶠ[𝓝 z]
+      CovariantDerivative.chartMetric g.inner p := by
+    filter_upwards [hone z (mem_singleton z)] with q hq
+    exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
+      χ (innerSL ℝ) g.inner p hq
+  have h := hessianAt_eq_blended_chart_hessian g p χ hχ hχsupp
+    (fun q ↦ (hbounds q).1) (fun q ↦ (hbounds q).2) hz
+    (hone z (mem_singleton z)) f hs hf v w
+  dsimp only at h ⊢
+  simpa only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
+    CovariantDerivative.christoffelFunctional, heq.self_of_nhds, heq.fderiv_eq] using h
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-032

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-033

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-034

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-035

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -239,4 +239,26 @@
   simpa only [RicciFlow.RicciFlow.christoffelClosedOp_apply,
     CovariantDerivative.christoffelFunctional, heq.self_of_nhds, heq.fderiv_eq] using h

+/-- Coordinates of a raised covector are its inverse-matrix contraction. -/
+theorem inverse_apply_coord
+    (G : ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
+    (hG : G.IsInvertible) (hs : ∀ v w, G v w = G w v)
+    (q : ClosedSmoothModel 3 →L[ℝ] ℝ) (k : Fin 3) :
+    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k (G.inverse q) =
+      ∑ m, DeTurckPrincipalSecondJet.inverseEntries G k m *
+        q (EuclideanSpace.basisFun (Fin 3) ℝ m) := by
+  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
+  let r := G.inverse (LinearMap.toContinuousLinearMap (b.coord k))
+  have hp := DeTurckPrincipalIdentity.inverse_pairing_symm G hG hs
+    (LinearMap.toContinuousLinearMap (b.coord k)) q
+  change b.coord k (G.inverse q) = q r at hp
+  rw [hp]
+  have hr := congrArg q (b.sum_repr r)
+  calc
+    q r = ∑ m, b.repr r m * q (b m) := by
+      simpa only [map_sum, map_smul, smul_eq_mul] using hr.symm
+    _ = _ := by
+      rw [DeTurckPrincipalIdentity.inverseEntries_eq_coordinates G hG]
+      rfl
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-036

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-037

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-038

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-039

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -261,4 +261,32 @@
       rw [DeTurckPrincipalIdentity.inverseEntries_eq_coordinates G hG]
       rfl

+/-- The closed Christoffel operator has the standard inverse-Gram coordinates. -/
+theorem christoffelClosedOp_coord
+    (G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)
+    (z : ClosedSmoothModel 3) (hG : (G z).IsInvertible)
+    (hs : ∀ v w, G z v w = G z w v) (hd : DifferentiableAt ℝ G z)
+    (k i j : Fin 3) :
+    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord k
+      (RicciFlow.RicciFlow.christoffelClosedOp G z
+        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
+      (1 / 2 : ℝ) * ∑ m, DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
+        (coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ m)) i z +
+         coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ m)) j z -
+         coordinateDirectionalDerivative (fun q ↦ G q
+            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) m z) := by
+  have hderiv (a b v : ClosedSmoothModel 3) :
+      fderiv ℝ (fun q ↦ G q a b) z v = fderiv ℝ G z v a b := by
+    have h := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const a z)).clm_apply
+      (hasFDerivAt_const b z)
+    simpa using congrArg (fun L : ClosedSmoothModel 3 →L[ℝ] ℝ ↦ L v) h.fderiv
+  rw [RicciFlow.RicciFlow.christoffelClosedOp_apply, inverse_apply_coord (G z) hG hs]
+  simp only [LinearMap.coe_toContinuousLinearMap', CovariantDerivative.christoffelFunctional,
+    coordinateDirectionalDerivative, ← EuclideanSpace.basisFun_apply, hderiv, Finset.mul_sum]
+  apply Finset.sum_congr rfl
+  intro m _
+  ring
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:279:97: error: unsolved goals
G : ClosedSmoothModel 3 → ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ
z : ClosedSmoothModel 3
hG : (G z).IsInvertible
hs : ∀ (v w : ClosedSmoothModel 3), ((G z) v) w = ((G z) w) v
hd : DifferentiableAt ℝ G z
k i j : Fin 3
hderiv : ∀ (a b v : ClosedSmoothModel 3), (fderiv ℝ (fun q => ((G q) a) b) z) v = (((fderiv ℝ G z) v) a) b
m : Fin 3
a✝ : m ∈ Finset.univ
⊢ DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
      {
          toFun := fun w =>
            (((fderiv ℝ G z) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) w *
                  (1 / 2) +
                (((fderiv ℝ G z) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) w *
                  (1 / 2) +
              (((fderiv ℝ G z) w) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
                (-1 / 2),
          map_add' := ⋯, map_smul' := ⋯ }
        ((EuclideanSpace.basisFun (Fin 3) ℝ) m) =
    DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
            (((fderiv ℝ G z) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
              ((EuclideanSpace.basisFun (Fin 3) ℝ) m) *
          (1 / 2) +
        DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
            (((fderiv ℝ G z) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
              ((EuclideanSpace.basisFun (Fin 3) ℝ) m) *
          (1 / 2) +
      DeTurckPrincipalSecondJet.inverseEntries (G z) k m *
          (((fderiv ℝ G z) ((EuclideanSpace.basisFun (Fin 3) ℝ) m)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
            ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
        (-1 / 2)
```

### probe-040

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -287,6 +287,7 @@
     coordinateDirectionalDerivative, ← EuclideanSpace.basisFun_apply, hderiv, Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro m _
+  dsimp
   ring

 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-041

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-042

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-043

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-044

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -290,4 +290,71 @@
   dsimp
   ring

+section Three
+variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
+  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
+  [ChartedSpace (ClosedSmoothModel 3) M₃]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
+local notation "I₃" => closedSmoothModelWithCorners 3
+local notation "E₃" => ClosedSmoothModel 3
+
+/-- The intrinsic Hessian entries in the inverse-chart frame have the standard
+coordinate second-derivative and Christoffel formula. -/
+theorem hessianAt_eq_coordinate_hessian
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
+    (f : M₃ → ℝ) (hs : tsupport f ⊆ (extChartAt I₃ p).source)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 f)
+    {z : E₃} (hz : z ∈ (extChartAt I₃ p).target) (i j : Fin 3) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
+    let Γ := fun y k i j ↦ (1 / 2 : ℝ) * ∑ m, a y k m *
+      (coordinateDirectionalDerivative (fun q ↦ G q j m) i y +
+       coordinateDirectionalDerivative (fun q ↦ G q i m) j y -
+       coordinateDirectionalDerivative (fun q ↦ G q i j) m y)
+    let u := ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p f
+    let D := mfderivWithin 𝓘(ℝ, E₃) I₃ (extChartAt I₃ p).symm (range I₃) z
+    g.hessianAt f ((extChartAt I₃ p).symm z)
+      (D (EuclideanSpace.basisFun (Fin 3) ℝ i))
+      (D (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
+      coordinateSecondDerivative u i j z - ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
+  intro G a Γ u D
+  let H := CovariantDerivative.chartMetric g.inner p
+  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
+  have hd : DifferentiableAt ℝ H z :=
+    (deTurckChartMetric_contDiffAt_two_of_mem_target g p hz).differentiableAt two_ne_zero
+  have hpos (v : E₃) (hv : v ≠ 0) : 0 < H z v v :=
+    CovariantDerivative.chartMetric_posDef g.inner (fun y v hv ↦ g.inner_pos y hv) p
+      (isInvertible_mfderivWithin_extChartAt_symm hz) hv
+  have hnondeg : (RicciFlow.RicciFlow.metricBilin (H z)).Nondegenerate := by
+    constructor
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+    · intro v hv
+      by_contra h
+      exact (ne_of_gt (hpos v h)) (hv v)
+  have hinv : (H z).IsInvertible := CovariantDerivative.metric_isInvertible H
+    (RicciFlow.RicciFlow.metricBilin (H z)) hnondeg (fun _ _ ↦ rfl)
+  have hcoord (k : Fin 3) : b.coord k
+      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = Γ z k i j :=
+    christoffelClosedOp_coord H z hinv
+      (CovariantDerivative.chartMetric_symm g.inner (fun y v w ↦ g.inner_symm y v w) p z) hd k i j
+  have hu : ContDiff ℝ 2 u := ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two p f hs hf
+  have hsecond : coordinateSecondDerivative u i j z = fderiv ℝ (fderiv ℝ u) z (b i) (b j) := by
+    have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z
+    have h := hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (b j) z)
+    have hh := congrArg (fun L : E₃ →L[ℝ] ℝ ↦ L (b i)) h.fderiv
+    simpa [coordinateSecondDerivative, coordinateDirectionalDerivative, b,
+      EuclideanSpace.basisFun_apply] using hh
+  have hcorrect : fderiv ℝ u z
+      (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
+      ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
+    have h := congrArg (fderiv ℝ u z)
+      (b.sum_repr (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)))
+    simpa only [map_sum, map_smul, smul_eq_mul, ← Module.Basis.coord_apply, hcoord,
+      b, EuclideanSpace.basisFun_apply, coordinateDirectionalDerivative] using h.symm
+  rw [hessianAt_eq_chart_derivatives g p f hs hf hz, ← hsecond, hcorrect]
+
+end Three
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:354:4: error: Type mismatch: After simplification, term
  Eq.symm h
 has type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j)) =
    ∑ x, Γ z x i j * (fderiv ℝ u z) ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis x)
but is expected to have type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j)) =
    ∑ x, Γ z x i j * (fderiv ℝ u z) (EuclideanSpace.single x 1)
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:356:53: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ((fderiv ℝ (fderiv ℝ u) z) (b i)) (b j)
in the target expression
  ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar p f)) z) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        ((EuclideanSpace.basisFun (Fin 3) ℝ) j) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar p f) z)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner p) z
            ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) =
    coordinateSecondDerivative u i j z - ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z

M₃ : Type u
inst✝⁷ : TopologicalSpace M₃
inst✝⁶ : T2Space M₃
inst✝⁵ : CompactSpace M₃
inst✝⁴ : ConnectedSpace M₃
inst✝³ : MeasurableSpace M₃
inst✝² : BorelSpace M₃
inst✝¹ : ChartedSpace E₃ M₃
inst✝ : IsManifold I₃ ∞ M₃
g : ClosedSmoothRiemannianMetric 3 M₃
p : M₃
f : M₃ → ℝ
hs : tsupport f ⊆ (extChartAt I₃ p).source
hf : ContMDiff I₃ 𝓘(ℝ, ℝ) 2 f
z : E₃
hz : z ∈ (extChartAt I₃ p).target
i j : Fin 3
G : E₃ → Matrix (Fin 3) (Fin 3) ℝ := inverseChartPullbackGramMatrixField g p
a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y => (G y)⁻¹
Γ : E₃ → Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun y k i j =>
    1 / 2 *
      ∑ m,
        a y k m *
          (coordinateDirectionalDerivative (fun q => G q j m) i y +
              coordinateDirectionalDerivative (fun q => G q i m) j y -
            coordinateDirectionalDerivative (fun q => G q i j) m y)
u : E₃ → ℝ := ClosedLaplacianStokesProducer.coordinateScalar p f
D : TangentSpace 𝓘(ℝ, E₃) z →L[ℝ] TangentSpace I₃ (↑(extChartAt I₃ p).symm z) :=
  mfderivWithin 𝓘(ℝ, E₃) I₃ (↑(extChartAt I₃ p).symm) (range ↑I₃) z
H : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := CovariantDerivative.chartMetric g.inner p
b : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
hd : DifferentiableAt ℝ H z
hpos : ∀ (v : E₃), v ≠ 0 → 0 < ((H z) v) v
hnondeg : (RicciFlow.RicciFlow.metricBilin (H z)).Nondegenerate
hinv : (H z).IsInvertible
hcoord : ∀ (k : Fin 3), (b.coord k) ((RicciFlow.RicciFlow.christoffelClosedOp H z (b i)) (b j)) = Γ z k i j
hu : ContDiff ℝ 2 u
hsecond : coordinateSecondDerivative u i j z = ((fderiv ℝ (fderiv ℝ u) z) (b i)) (b j)
hcorrect :
  (fderiv ℝ u z) ((RicciFlow.RicciFlow.christoffelClosedOp H z (b i)) (b j)) =
    ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z
⊢ ((fderiv ℝ (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar p f)) z) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        ((EuclideanSpace.basisFun (Fin 3) ℝ) j) -
      (fderiv ℝ (ClosedLaplacianStokesProducer.coordinateScalar p f) z)
        ((RicciFlow.RicciFlow.christoffelClosedOp (CovariantDerivative.chartMetric g.inner p) z
            ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) =
    coordinateSecondDerivative u i j z - ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z
```

### probe-045

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -352,8 +352,11 @@
     have h := congrArg (fderiv ℝ u z)
       (b.sum_repr (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)))
     simpa only [map_sum, map_smul, smul_eq_mul, ← Module.Basis.coord_apply, hcoord,
-      b, EuclideanSpace.basisFun_apply, coordinateDirectionalDerivative] using h.symm
-  rw [hessianAt_eq_chart_derivatives g p f hs hf hz, ← hsecond, hcorrect]
+      b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, coordinateDirectionalDerivative] using h.symm
+  rw [hessianAt_eq_chart_derivatives g p f hs hf hz]
+  change fderiv ℝ (fderiv ℝ u) z (b i) (b j) - fderiv ℝ u z
+    (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = _
+  rw [← hsecond, hcorrect]

 end Three

```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:354:4: error: Type mismatch: After simplification, term
  Eq.symm h
 has type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) =
    ∑ x,
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord x)
          ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) *
        (fderiv ℝ u z) (EuclideanSpace.single x 1)
but is expected to have type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) =
    ∑ x, Γ z x i j * (fderiv ℝ u z) (EuclideanSpace.single x 1)
```

### probe-046

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `1`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:354:4: error: Type mismatch: After simplification, term
  Eq.symm h
 has type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) =
    ∑ x,
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord x)
          ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) *
        (fderiv ℝ u z) (EuclideanSpace.single x 1)
but is expected to have type
  (fderiv ℝ u z)
      ((RicciFlow.RicciFlow.christoffelClosedOp H z (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) =
    ∑ x, Γ z x i j * (fderiv ℝ u z) (EuclideanSpace.single x 1)
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

### probe-047

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -351,8 +351,13 @@
       ∑ k, Γ z k i j * coordinateDirectionalDerivative u k z := by
     have h := congrArg (fderiv ℝ u z)
       (b.sum_repr (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)))
-    simpa only [map_sum, map_smul, smul_eq_mul, ← Module.Basis.coord_apply, hcoord,
-      b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, coordinateDirectionalDerivative] using h.symm
+    have hexp : fderiv ℝ u z (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) =
+        ∑ k, b.coord k (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) *
+          fderiv ℝ u z (b k) := by
+      simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply] using h.symm
+    simp_rw [hcoord] at hexp
+    simpa only [b, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
+      coordinateDirectionalDerivative] using hexp
   rw [hessianAt_eq_chart_derivatives g p f hs hf hz]
   change fderiv ℝ (fderiv ℝ u) z (b i) (b j) - fderiv ℝ u z
     (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = _
```

Actual output:

```text
```

### probe-048

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-049

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-050

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-051

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -363,6 +363,39 @@
     (RicciFlow.RicciFlow.christoffelClosedOp H z (b i) (b j)) = _
   rw [← hsecond, hcorrect]

+/-- The intrinsic scalar Laplacian equals the standard Christoffel-coordinate
+formula on each shrunk chart region. -/
+theorem laplacianAt_eq_christoffelCoordinateLaplacian
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
+    (V : Set M₃) (hV : closure V ⊆ (extChartAt I₃ p).source)
+    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
+    (hf : ContMDiff I₃ 𝓘(ℝ) 2 φ)
+    (z : (extChartAt I₃ p).target) (hz : (z : E₃) ∈ (extChartAt I₃ p) '' V) :
+    let G := inverseChartPullbackGramMatrixField g p
+    let a : E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
+    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
+      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
+       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
+       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
+    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
+      christoffelCoordinateLaplacian a Γ
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
+  intro G a Γ
+  have hs : tsupport φ ⊆ (extChartAt I₃ p).source :=
+    hφ.trans (subset_closure.trans hV)
+  have hzt : (z : E₃) ∈ (extChartAt I₃ p).target := by
+    obtain ⟨x, hx, hzx⟩ := hz
+    rw [← hzx]
+    exact (extChartAt I₃ p).map_source (hV (subset_closure hx))
+  rw [laplacianAt_eq_chart_hessian g φ p z]
+  unfold christoffelCoordinateLaplacian
+  apply Finset.sum_congr rfl
+  intro i _
+  apply Finset.sum_congr rfl
+  intro j _
+  exact congrArg (fun t : ℝ ↦ a z i j * t)
+    (hessianAt_eq_coordinate_hessian g p φ hs hf hzt i j)
+
 end Three

 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-052

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-053

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-054

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-055

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -398,4 +398,40 @@

 end Three

+/-- Restricting the genuine chart domain restricts the Riemannian chart measure. -/
+theorem restrictedChart_measure
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
+    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
+    HausdorffChartDensityEquality g U
+      (fun z ↦ inverseExtendedChartParametrization (n := n) p (Set.inclusion hsub z))
+      ((extChartAt I p).symm '' U)
+      (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)) := by
+  let ψ := inverseExtendedChartParametrization (n := n) p
+  let ι := Set.inclusion hsub
+  let μ := rawHausdorffCoordinateDensityMeasure (extChartAt I p).target
+    (inverseChartPullbackVolumeDensity g p)
+  have hψ : MeasurableEmbedding ψ :=
+    (inverseExtendedChartParametrization_isEmbedding (n := n) p).measurableEmbedding
+      (by rw [range_inverseExtendedChartParametrization]; exact (isOpen_extChartAt_source p).measurableSet)
+  have hmap := map_rawHausdorffCoordinateDensityMeasure_inclusion
+    (isOpen_extChartAt_target p).measurableSet hU hsub (inverseChartPullbackVolumeDensity g p)
+  have hres := hψ.restrict_map μ (ψ '' range ι)
+  rw [preimage_image_eq _ hψ.injective] at hres
+  have himage : ψ '' range ι = (extChartAt I p).symm '' U := by
+    ext x
+    constructor
+    · rintro ⟨q, ⟨z, rfl⟩, rfl⟩
+      exact ⟨z, z.2, rfl⟩
+    · rintro ⟨z, hz, rfl⟩
+      exact ⟨ι ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
+  have hsource : ψ '' range ι ⊆ (extChartAt I p).source := by
+    rintro x ⟨z, _, rfl⟩
+    exact (extChartAt I p).map_target z.2
+  change Measure.map (ψ ∘ ι) _ = _
+  rw [← Measure.map_map hψ.measurable (measurable_inclusion hsub), hmap, ← hres]
+  have hfull : Measure.map ψ μ = (volumeMeasure g).restrict (extChartAt I p).source :=
+    ClosedLaplacianStokesProducer.openChart_measure g p
+  rw [hfull, Measure.restrict_restrict_of_subset hsource, himage]
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
```

### probe-056

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-057

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-058

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-059

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -434,4 +434,36 @@
     ClosedLaplacianStokesProducer.openChart_measure g p
   rw [hfull, Measure.restrict_restrict_of_subset hsource, himage]

+/-- The genuine density remains integrable on a measurable subdomain of a chart. -/
+theorem restrictedChart_density_integrable
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) {U : Set E}
+    (hU : MeasurableSet U) (hsub : U ⊆ (extChartAt I p).target) :
+    Integrable (fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z))
+      (coordinateLebesgueMeasure U) := by
+  let δ := fun z ↦ inverseChartPullbackVolumeDensity g p (Set.inclusion hsub z)
+  have hcont : Continuous δ := (continuous_inverseChartPullbackVolumeDensity g p).comp
+    (continuous_inclusion hsub)
+  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+  have hmeas := (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable.comp
+    (measurable_inclusion hsub)
+  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (restrictedChart_measure g p hU hsub)
+  dsimp only at hmass
+  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
+    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
+  have hfinite : ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) * δ z)
+      ∂(coordinateLebesgueMeasure U) ≠ (⊤ : ℝ≥0∞) := by
+    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
+      Measure.restrict_univ] at hmass
+    rw [hmass]
+    letI := volumeMeasure_isFiniteMeasure g
+    exact measure_ne_top (volumeMeasure g) _
+  have hint := (lintegral_ofReal_ne_top_iff_integrable
+    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
+    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
+      (inverseChartPullbackVolumeDensity_pos g p (Set.inclusion hsub z)).le)).mp hfinite
+  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:454:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (Measure.map (inverseExtendedChartParametrization p ∘ inclusion hsub) ?m.178) univ
in the target expression
  (Measure.map (fun z => inverseExtendedChartParametrization p (inclusion hsub z))
        (rawHausdorffCoordinateDensityMeasure U fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)))
      univ =
    ((volumeMeasure g).restrict (↑(extChartAt I p).symm '' U)) univ

n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : ChartedSpace E M
inst✝⁴ : IsManifold I ∞ M
inst✝³ : CompactSpace M
inst✝² : ConnectedSpace M
inst✝¹ : MeasurableSpace M
inst✝ : BorelSpace M
g : ClosedSmoothRiemannianMetric n M
p : M
U : Set E
hU : MeasurableSet U
hsub : U ⊆ (extChartAt I p).target
δ : ↑U → ℝ := fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)
hcont : Continuous δ
hscale : 0 < ↑(rawHausdorffLebesgueScale n)
hmeas : Measurable (inverseExtendedChartParametrization p ∘ inclusion hsub)
hmass :
  (Measure.map (fun z => inverseExtendedChartParametrization p (inclusion hsub z))
        (rawHausdorffCoordinateDensityMeasure U fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)))
      univ =
    ((volumeMeasure g).restrict (↑(extChartAt I p).symm '' U)) univ
⊢ Integrable (fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)) (coordinateLebesgueMeasure U)
```

### probe-060

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `1`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:454:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (Measure.map (inverseExtendedChartParametrization p ∘ inclusion hsub) ?m.178) univ
in the target expression
  (Measure.map (fun z => inverseExtendedChartParametrization p (inclusion hsub z))
        (rawHausdorffCoordinateDensityMeasure U fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)))
      univ =
    ((volumeMeasure g).restrict (↑(extChartAt I p).symm '' U)) univ

n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : ChartedSpace E M
inst✝⁴ : IsManifold I ∞ M
inst✝³ : CompactSpace M
inst✝² : ConnectedSpace M
inst✝¹ : MeasurableSpace M
inst✝ : BorelSpace M
g : ClosedSmoothRiemannianMetric n M
p : M
U : Set E
hU : MeasurableSet U
hsub : U ⊆ (extChartAt I p).target
δ : ↑U → ℝ := fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)
hcont : Continuous δ
hscale : 0 < ↑(rawHausdorffLebesgueScale n)
hmeas : Measurable (inverseExtendedChartParametrization p ∘ inclusion hsub)
hmass :
  (Measure.map (fun z => inverseExtendedChartParametrization p (inclusion hsub z))
        (rawHausdorffCoordinateDensityMeasure U fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)))
      univ =
    ((volumeMeasure g).restrict (↑(extChartAt I p).symm '' U)) univ
⊢ Integrable (fun z => inverseChartPullbackVolumeDensity g p (inclusion hsub z)) (coordinateLebesgueMeasure U)
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

### probe-061

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -447,7 +447,9 @@
   have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
     exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
       (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
-  have hmeas := (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable.comp
+  have hmeas : Measurable (fun z : U ↦ inverseExtendedChartParametrization (n := n) p
+      (Set.inclusion hsub z)) :=
+    (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable.comp
     (measurable_inclusion hsub)
   have hmass := congrArg (fun μ : Measure M ↦ μ univ) (restrictedChart_measure g p hU hsub)
   dsimp only at hmass
```

Actual output:

```text
```

### probe-062

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-063

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-064

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-065

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -468,4 +468,21 @@
       (inverseChartPullbackVolumeDensity_pos g p (Set.inclusion hsub z)).le)).mp hfinite
   exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

+/-- Zero extension does not enlarge the coordinate support beyond the image
+of the manifold support. -/
+theorem coordinateScalar_tsupport_subset_image [CompactSpace M]
+    (p : M) (f : M → ℝ) (hs : tsupport f ⊆ (extChartAt I p).source) :
+    tsupport (ClosedLaplacianStokesProducer.coordinateScalar (n := n) p f) ⊆
+      (extChartAt I p) '' tsupport f := by
+  have hcompact : IsCompact ((extChartAt I p) '' tsupport f) :=
+    (isClosed_tsupport f).isCompact.image_of_continuousOn ((continuousOn_extChartAt p).mono hs)
+  apply closure_minimal _ hcompact.isClosed
+  intro z hz
+  by_cases hzt : z ∈ (extChartAt I p).target
+  · refine ⟨(extChartAt I p).symm z, ?_, (extChartAt I p).right_inv hzt⟩
+    apply subset_tsupport
+    simpa only [Function.mem_support, ClosedLaplacianStokesProducer.coordinateScalar,
+      indicator_of_mem hzt] using hz
+  · exact False.elim (hz (indicator_of_notMem hzt _))
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### probe-066

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-067

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-068

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-069

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -485,4 +485,43 @@
       indicator_of_mem hzt] using hz
   · exact False.elim (hz (indicator_of_notMem hzt _))

+/-- A continuous coordinate divergence on a smaller open region suffices
+for continuity of the localized intrinsic Laplacian. -/
+theorem laplacian_continuous_of_restricted_coordinate_divergence
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (V : Set M)
+    (hV : IsOpen V) (hVs : V ⊆ (extChartAt I p).source)
+    (f : M → ℝ) (hs : tsupport f ⊆ V) (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    (w D : E → ℝ) (hw : Continuous w) (hD : Continuous D)
+    (hpos : ∀ z ∈ (extChartAt I p) '' V, 0 < w z)
+    (hcoord : ∀ z : (extChartAt I p).target, (z : E) ∈ (extChartAt I p) '' V →
+      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
+    Continuous (fun x ↦ g.laplacianAt f x) := by
+  have hformula (x : M) (hx : x ∈ V) :
+      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
+    let z : (extChartAt I p).target := ⟨extChartAt I p x, (extChartAt I p).map_source (hVs hx)⟩
+    have hinv : inverseExtendedChartParametrization (n := n) p z = x :=
+      (extChartAt I p).left_inv (hVs hx)
+    have hz : (z : E) ∈ (extChartAt I p) '' V := ⟨x, hx, rfl⟩
+    apply (eq_div_iff (hpos z hz).ne').mpr
+    simpa only [hinv, mul_comm] using hcoord z hz
+  apply continuous_iff_continuousAt.mpr
+  intro x
+  by_cases hx : x ∈ V
+  · have hc := (continuousOn_extChartAt p x (hVs hx)).continuousAt
+      ((isOpen_extChartAt_source p).mem_nhds (hVs hx))
+    have hquot := (hD.continuousAt.div hw.continuousAt
+      (hpos _ ⟨x, hx, rfl⟩).ne').comp hc
+    apply hquot.congr_of_eventuallyEq
+    filter_upwards [hV.mem_nhds hx] with y hy
+    exact hformula y hy
+  · have hxt : x ∉ tsupport f := fun h ↦ hx (hs h)
+    apply continuousAt_const.congr_of_eventuallyEq
+    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
+    calc
+      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
+        g.laplacianAt_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
+          (g.mdifferentiableAt_gradient hf.contMDiffAt)
+          (g.mdifferentiableAt_gradient contMDiffAt_const)
+      _ = 0 := g.laplacianAt_const 0 y
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### probe-070

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-071

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-072

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-073

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -524,4 +524,130 @@
           (g.mdifferentiableAt_gradient contMDiffAt_const)
       _ = 0 := g.laplacianAt_const 0 y

+/-- The Stokes geometry can use the coordinate images of a shrunk open cover. -/
+def geometry_of_shrunk_coordinate_coefficients
+    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
+    (hf : ContMDiff I 𝓘(ℝ) 2 f)
+    (C : FiniteExtendedChartCover (n := n) (M := M))
+    (V : Fin C.chartCount → Set M) (hV : ∀ i, IsOpen (V i))
+    (hVs : ∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source)
+    (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ) (hρ : ρ.IsSubordinate V)
+    (w : Fin C.chartCount → E → ℝ)
+    (a : Fin C.chartCount → E → Fin n → Fin n → ℝ)
+    (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
+    (hw : ∀ i, ContDiff ℝ 1 (w i))
+    (ha : ∀ i j k, ContDiff ℝ 1 (fun z ↦ a i z j k))
+    (hweight : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
+      w i z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g (C.anchor i) z)
+    (hcompat : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i → ∀ j,
+      (∑ k, fderiv ℝ (fun y ↦ w i y * a i y k j) z (EuclideanSpace.single k (1 : ℝ))) =
+        w i z * (-(∑ k, ∑ l, a i z k l * Γ i z j k l)))
+    (hcoord : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      (z : E) ∈ (extChartAt I (C.anchor i)) '' V i →
+      g.laplacianAt (fun x ↦ ρ i x * f x)
+        (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
+      christoffelCoordinateLaplacian (a i) (Γ i)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z) :
+    FiniteSubordinateHausdorffLaplacianGeometry g f := by
+  let U := fun i ↦ (extChartAt I (C.anchor i)) '' V i
+  have hVs' (i) : V i ⊆ (extChartAt I (C.anchor i)).source := subset_closure.trans (hVs i)
+  have hsub (i) : U i ⊆ (extChartAt I (C.anchor i)).target :=
+    image_subset_iff.mpr fun _ hx ↦ (extChartAt I (C.anchor i)).map_source (hVs' i hx)
+  have hU (i) : MeasurableSet (U i) := by
+    have heq : U i = Subtype.val ''
+        (inverseExtendedChartParametrization (n := n) (C.anchor i) ⁻¹' V i) := by
+      ext z
+      constructor
+      · rintro ⟨x, hx, rfl⟩
+        refine ⟨⟨extChartAt I (C.anchor i) x, (extChartAt I (C.anchor i)).map_source (hVs' i hx)⟩, ?_, rfl⟩
+        change (extChartAt I (C.anchor i)).symm (extChartAt I (C.anchor i) x) ∈ V i
+        rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hx)]
+      · rintro ⟨z, hz, rfl⟩
+        exact ⟨(extChartAt I (C.anchor i)).symm z, hz, (extChartAt I (C.anchor i)).right_inv z.2⟩
+    rw [heq]
+    exact (MeasurableEmbedding.subtype_coe (isOpen_extChartAt_target (C.anchor i)).measurableSet).measurableSet_image.mpr
+      ((inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable
+        (hV i).measurableSet)
+  have himage (i) : (extChartAt I (C.anchor i)).symm '' U i = V i := by
+    ext x
+    constructor
+    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
+      rwa [(extChartAt I (C.anchor i)).left_inv (hVs' i hy)]
+    · intro hx
+      exact ⟨extChartAt I (C.anchor i) x, ⟨x, hx, rfl⟩,
+        (extChartAt I (C.anchor i)).left_inv (hVs' i hx)⟩
+  have hsV (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ V i := tsupport_mul_subset_left.trans (hρ i)
+  have hs (i) : tsupport (fun x ↦ ρ i x * f x) ⊆ (extChartAt I (C.anchor i)).source :=
+    (hsV i).trans (hVs' i)
+  have htwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  have hlocal (i) : ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
+    ((ρ i).contMDiff.of_le htwo).mul hf
+  let u := fun i ↦ ClosedLaplacianStokesProducer.coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)
+  have hu (i) : ContDiff ℝ 2 (u i) :=
+    ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two (C.anchor i) _ (hs i) (hlocal i)
+  have hcontinuous (i) : Continuous (fun x ↦ g.laplacianAt (fun y ↦ ρ i y * f y) x) := by
+    let F := coordinateMetricFluxComponent (w i) (a i) (u i)
+    have hF (k) : ContDiff ℝ 1 (F k) := coordinateMetricFluxComponent_contDiff_one (hw i) (ha i) (hu i) k
+    apply laplacian_continuous_of_restricted_coordinate_divergence g (C.anchor i) (V i)
+      (hV i) (hVs' i) _ (hsV i) (hlocal i) (w i) (euclideanCoordinateDivergence F) (hw i).continuous
+    · exact continuous_finsetSum _ fun k _ ↦ ((hF k).continuous_fderiv one_ne_zero).clm_apply continuous_const
+    · intro z hz
+      rw [hweight i ⟨z, hsub i hz⟩ hz]
+      have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+        exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+          (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+      exact mul_pos hscale (inverseChartPullbackVolumeDensity_pos g (C.anchor i) ⟨z, hsub i hz⟩)
+    · intro z hz
+      have hdiv := euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
+        (contractedChristoffel := fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l))
+        ((hw i).differentiable one_ne_zero z)
+        (fun j k ↦ (ha i j k).differentiable one_ne_zero z)
+        (fun j ↦ (coordinateDirectionalDerivative_contDiff_one (hu i) j).differentiable one_ne_zero z)
+        (hcompat i z hz)
+      rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
+        (a i) (Γ i) (fun y j ↦ -(∑ k, ∑ l, a i y k l * Γ i y j k l)) (u i) z (fun _ ↦ rfl)] at hdiv
+      rw [hcoord i z hz]
+      exact hdiv.symm
+  exact {
+    chartCount := C.chartCount
+    coordinateDomain := U
+    coordinateDomain_measurable := hU
+    inverseChart := fun i z ↦ inverseExtendedChartParametrization (n := n) (C.anchor i) (Set.inclusion (hsub i) z)
+    inverseChart_measurable := fun i ↦
+      (inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable.comp (measurable_inclusion (hsub i))
+    chartRegion := V
+    chartRegion_isOpen := hV
+    density := fun i z ↦ inverseChartPullbackVolumeDensity g (C.anchor i) (Set.inclusion (hsub i) z)
+    density_nonneg := fun i ↦ Eventually.of_forall fun z ↦ (inverseChartPullbackVolumeDensity_pos g (C.anchor i) (Set.inclusion (hsub i) z)).le
+    density_integrable := fun i ↦ restrictedChart_density_integrable g (C.anchor i) (hU i) (hsub i)
+    chartMeasure := fun i ↦ by
+      have h := restrictedChart_measure g (C.anchor i) (hU i) (hsub i)
+      rwa [himage i] at h
+    partition := ρ
+    partition_subordinate := hρ
+    f_contMDiff_two := hf
+    coordinateRepresentative := u
+    coordinateRepresentative_eq := fun i z ↦ indicator_of_mem (hsub i z.2) _
+    coordinateRepresentative_contDiff_two := hu
+    coordinateRepresentative_hasCompactSupport := fun i ↦
+      (ClosedLaplacianStokesProducer.coordinateScalar_support (C.anchor i) _ (hs i)).1
+    coordinateRepresentative_tsupport_subset_coordinateDomain := fun i ↦
+      (coordinateScalar_tsupport_subset_image (C.anchor i) _ (hs i)).trans (image_mono (hsV i))
+    weight := w
+    weight_contDiff_one := hw
+    weight_eq_density := fun i z ↦ hweight i (Set.inclusion (hsub i) z) z.2
+    inverseMetric := a
+    inverseMetric_contDiff_one := ha
+    christoffel := Γ
+    contractedChristoffel := fun i z j ↦ -(∑ k, ∑ l, a i z k l * Γ i z j k l)
+    contractedChristoffel_eq := fun _ _ _ ↦ rfl
+    density_inverseMetric_compatibility := fun i z ↦ hcompat i (Set.inclusion (hsub i) z) z.2
+    intrinsicCoordinateLaplacian_eq := fun i z ↦ hcoord i (Set.inclusion (hsub i) z) z.2
+    localizedLaplacian_aestronglyMeasurable := fun i ↦ (hcontinuous i).aestronglyMeasurable }
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### probe-074

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-075

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-076

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-077

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -650,4 +650,59 @@
     intrinsicCoordinateLaplacian_eq := fun i z ↦ hcoord i (Set.inclusion (hsub i) z) z.2
     localizedLaplacian_aestronglyMeasurable := fun i ↦ (hcontinuous i).aestronglyMeasurable }

+section StokesThree
+variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
+  [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
+  [ChartedSpace (ClosedSmoothModel 3) M₃]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
+local notation "I₃" => closedSmoothModelWithCorners 3
+local notation "E₃" => ClosedSmoothModel 3
+
+/-- On a closed smooth three-manifold the Laplacian of a C² scalar is
+integrable and its integral is zero. -/
+theorem closedLaplacianStokes_of_contMDiff_two
+    (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ)
+    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
+    ClosedLaplacianStokes g f := by
+  letI : SecondCountableTopology M₃ := ChartedSpace.secondCountable_of_sigmaCompact E₃ M₃
+  let C := compactFiniteExtendedChartCover (n := 3) (M := M₃)
+  obtain ⟨V, ρ, w, a, _hcover, hV, hVs, _hcompact, hρ, hw, ha, hwe, hae⟩ :=
+    ClosedLaplacianStokesGlobalCoefficients.exists_shrunk_cover_global_coefficients g C
+  let G := fun i ↦ inverseChartPullbackGramMatrixField g (C.anchor i)
+  let A : Fin C.chartCount → E₃ → Matrix (Fin 3) (Fin 3) ℝ := fun i z ↦ (G i z)⁻¹
+  let Γ := fun i z j k l ↦ (1 / 2 : ℝ) * ∑ m, A i z j m *
+    (coordinateDirectionalDerivative (fun y ↦ G i y l m) k z +
+     coordinateDirectionalDerivative (fun y ↦ G i y k m) l z -
+     coordinateDirectionalDerivative (fun y ↦ G i y k l) m z)
+  have hle1 : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  have hle2 : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
+    exact WithTop.coe_le_coe.mpr le_top
+  apply (geometry_of_shrunk_coordinate_coefficients g f hf C V hV hVs ρ hρ w a Γ
+    (fun i ↦ (hw i).of_le hle1) (fun i j k ↦ (ha i j k).of_le hle1) ?_ ?_ ?_).closedLaplacianStokes
+  · intro i z hz
+    rw [(hwe i z (image_mono subset_closure hz)).self_of_nhds]
+    exact (ClosedLaplacianStokesProducer.chartWeight_regular g (C.anchor i)).2 z
+  · intro i z hz j
+    exact ClosedLaplacianStokesGlobalCoefficients.density_inverseMetric_compatibility_of_eventuallyEq
+      g (C.anchor i) (w i) (a i) z z.2
+      (hwe i z (image_mono subset_closure hz)) (hae i z (image_mono subset_closure hz)) j
+  · intro i z hz
+    have hlocal : ContMDiff I₃ 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
+      ((ρ i).contMDiff.of_le hle2).mul hf
+    have h := laplacianAt_eq_christoffelCoordinateLaplacian g (C.anchor i) (V i) (hVs i)
+      (fun x ↦ ρ i x * f x) (tsupport_mul_subset_left.trans (hρ i)) hlocal z hz
+    change g.laplacianAt (fun x ↦ ρ i x * f x)
+      (inverseExtendedChartParametrization (n := 3) (C.anchor i) z) =
+      christoffelCoordinateLaplacian (A i) (Γ i)
+        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) (C.anchor i) (fun x ↦ ρ i x * f x)) z at h
+    rw [h]
+    unfold christoffelCoordinateLaplacian
+    have hval : a i z = A i z := (hae i z (image_mono subset_closure hz)).self_of_nhds
+    rw [hval]
+
+end StokesThree
+
 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### probe-078

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-079

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-080

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-081

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -703,6 +703,19 @@
     have hval : a i z = A i z := (hae i z (image_mono subset_closure hz)).self_of_nhds
     rw [hval]

+/-- Joint C³ metric entries supply the scalar C² input along a forward
+normalized Ricci flow. -/
+theorem closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
+    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) := by
+  intro t ht
+  apply closedLaplacianStokes_of_contMDiff_two
+  intro x
+  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow (hFlow t ht)
+    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hJoint t y)) x
+
 end StokesThree

 end Poincare.IntrinsicLaplacianCoordinateForm
```

Actual output:

```text
Poincare/Global/IntrinsicLaplacianCoordinateForm.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### probe-082

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
```

Actual output:

```text
/private/tmp/intrinsic-laplacian-evidence/Probe.lean:473:0: warning: automatically included section variable(s) unused in theorem `Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image`:
  [T2Space M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-083

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-084

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-085

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Module source change before this command:

```diff
--- previous/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
+++ current/Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
@@ -468,6 +468,7 @@
       (inverseChartPullbackVolumeDensity_pos g p (Set.inclusion hsub z)).le)).mp hfinite
   exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint

+omit [T2Space M] [IsManifold I ∞ M] in
 /-- Zero extension does not enlarge the coordinate support beyond the image
 of the manifold support. -/
 theorem coordinateScalar_tsupport_subset_image [CompactSpace M]
```

Actual output:

```text
```

### probe-086

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic tail after the current module:

```lean

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
```

Actual output:

```text
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-087

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-088

```sh
git diff --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-089

```sh
LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/IntrinsicLaplacianCoordinateForm.olean Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Actual output:

```text
```

### probe-090

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic source:

```lean
import Poincare.Global.IntrinsicLaplacianCoordinateForm
noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm
variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
 [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
 [ChartedSpace (ClosedSmoothModel 3) M₃]
 [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
example
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (V : Set M₃) (hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source)
    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 φ)
    (z : (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (hz : (z : ClosedSmoothModel 3) ∈ (extChartAt (closedSmoothModelWithCorners 3) p) '' V) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
      christoffelCoordinateLaplacian a Γ
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
  exact laplacianAt_eq_christoffelCoordinateLaplacian g p V hV φ hφ hf z hz

example (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    ClosedLaplacianStokes g f :=
  closedLaplacianStokes_of_contMDiff_two g f hf

example (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) :=
  closedLaplacianStokes_scalarAt_of_normalizedRicciFlow gt hFlow hJoint

end Poincare.IntrinsicLaplacianCoordinateForm

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.IntrinsicLaplacianCoordinateForm
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected dependencies for {n}: {axs}"
      count := count + 1
      logInfo m!"EXACT_DEPENDENCIES {n}: {axs}"
  logInfo m!"MODULE_SCAN declarations={count} all_exact=true"
```

Actual output:

```text
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.coordinateDirectionalDerivative.eq_1: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.coordinateSecondDerivative.eq_1: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt.congr_simp: [propext,
 Classical.choice,
 Quot.sound]
MODULE_SCAN declarations=20 all_exact=true
```

### probe-091

```sh
git diff 84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5 --check
```

Exit code: `0`.

Actual output:

```text
```

### probe-092

```sh
git status --short --branch
```

Exit code: `0`.

Actual output:

```text
## worker/intrinsic-laplacian-coordinate-form
```

### probe-093

```sh
git log --reverse --format="%h %s" 84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5..HEAD
```

Exit code: `0`.

Actual output:

```text
6e4b8312 Prove intrinsic Laplacian inverse Gram contraction in any tangent basis
4edfb209 Compute the intrinsic Laplacian in the inverse chart Euclidean frame
741e94f3 Identify the differential through the transported intrinsic gradient
6bfbc4be Prove the intrinsic gradient equals the genuine coordinate gradient
5cb6a954 Transport the intrinsic Hessian through a smooth local chart metric
828633a3 Remove the auxiliary cutoff from the intrinsic Hessian formula
3574af09 Compute raised covector coordinates from the inverse metric matrix
63b40d78 Identify the standard Christoffel array with the closed connection operator
6a0b55aa Prove the full intrinsic Hessian identity in coordinate entries
eca8835d Prove the frozen intrinsic Laplacian coordinate identity
bf3c0f71 Prove the Hausdorff chart measure formula on restricted domains
42902a8d Prove integrability of the density on restricted chart domains
7b1da239 Control zero-extended coordinate support in the shrunk chart image
e74d9de4 Derive localized Laplacian continuity from restricted coordinate divergence
656f39f2 Construct Stokes geometry over the shrunk coordinate domains
72214b33 Prove closed Laplacian Stokes for every C2 scalar in dimension three
1763acf3 Prove forward normalized-flow scalar Laplacian Stokes
4f0def7b Remove unused ambient assumptions from the coordinate support lemma
```

### probe-094

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `1`.

Actual output:

```text
```

### probe-095

```sh
rg -n '^(theorem|def) ' Poincare/Global/IntrinsicLaplacianCoordinateForm.lean
```

Exit code: `0`.

Actual output:

```text
20:theorem laplacianAt_eq_inverseGram_hessian
36:theorem laplacianAt_eq_chart_hessian
60:theorem chartMetric_transported_gradient
88:theorem transported_gradient_eq_coordGradient
118:theorem hessianAt_eq_blended_chart_hessian
214:theorem hessianAt_eq_chart_derivatives
243:theorem inverse_apply_coord
265:theorem christoffelClosedOp_coord
303:theorem hessianAt_eq_coordinate_hessian
368:theorem laplacianAt_eq_christoffelCoordinateLaplacian
402:theorem restrictedChart_measure
438:theorem restrictedChart_density_integrable
474:theorem coordinateScalar_tsupport_subset_image [CompactSpace M]
491:theorem laplacian_continuous_of_restricted_coordinate_divergence
529:def geometry_of_shrunk_coordinate_coefficients
664:theorem closedLaplacianStokes_of_contMDiff_two
709:theorem closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
```

### probe-096

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/intrinsic-laplacian-evidence/Probe.lean
```

Exit code: `0`.

Diagnostic source:

```lean
import Poincare.Global.IntrinsicLaplacianCoordinateForm
noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
universe u
namespace Poincare.IntrinsicLaplacianCoordinateForm
variable {M₃ : Type u} [TopologicalSpace M₃] [T2Space M₃] [CompactSpace M₃]
 [ConnectedSpace M₃] [MeasurableSpace M₃] [BorelSpace M₃]
 [ChartedSpace (ClosedSmoothModel 3) M₃]
 [IsManifold (closedSmoothModelWithCorners 3) ∞ M₃]
example
    (g : ClosedSmoothRiemannianMetric 3 M₃) (p : M₃)
    (V : Set M₃) (hV : closure V ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).source)
    (φ : M₃ → ℝ) (hφ : tsupport φ ⊆ V)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 φ)
    (z : (extChartAt (closedSmoothModelWithCorners 3) p).target)
    (hz : (z : ClosedSmoothModel 3) ∈ (extChartAt (closedSmoothModelWithCorners 3) p) '' V) :
    let G := inverseChartPullbackGramMatrixField g p
    let a : ClosedSmoothModel 3 → Matrix (Fin 3) (Fin 3) ℝ := fun y ↦ (G y)⁻¹
    let Γ := fun y j k l ↦ (1 / 2 : ℝ) * ∑ m, a y j m *
      (coordinateDirectionalDerivative (fun q ↦ G q l m) k y +
       coordinateDirectionalDerivative (fun q ↦ G q k m) l y -
       coordinateDirectionalDerivative (fun q ↦ G q k l) m y)
    g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
      christoffelCoordinateLaplacian a Γ
        (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z := by
  exact laplacianAt_eq_christoffelCoordinateLaplacian g p V hV φ hφ hf z hz

example (g : ClosedSmoothRiemannianMetric 3 M₃) (f : M₃ → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    ClosedLaplacianStokes g f :=
  closedLaplacianStokes_of_contMDiff_two g f hf

example (gt : ℝ → ClosedSmoothRiemannianMetric 3 M₃)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M₃, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) :=
  closedLaplacianStokes_scalarAt_of_normalizedRicciFlow gt hFlow hJoint

end Poincare.IntrinsicLaplacianCoordinateForm

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.IntrinsicLaplacianCoordinateForm
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected dependencies for {n}: {axs}"
      count := count + 1
      logInfo m!"EXACT_DEPENDENCIES {n}: {axs}"
  logInfo m!"MODULE_SCAN declarations={count} all_exact=true"

#print axioms Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian
#print axioms Poincare.coordinateDirectionalDerivative.eq_1
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence
#print axioms Poincare.coordinateSecondDerivative.eq_1
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian
#print axioms Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives
#print axioms Poincare.ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt.congr_simp
```

Actual output:

```text
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.coordinateDirectionalDerivative.eq_1: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.coordinateSecondDerivative.eq_1: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCIES Poincare.ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt.congr_simp: [propext,
 Classical.choice,
 Quot.sound]
MODULE_SCAN declarations=20 all_exact=true
'Poincare.IntrinsicLaplacianCoordinateForm.transported_gradient_eq_coordGradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.chartMetric_transported_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_blended_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_coordinate_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.coordinateDirectionalDerivative.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.christoffelClosedOp_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.geometry_of_shrunk_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_christoffelCoordinateLaplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_of_contMDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.coordinateScalar_tsupport_subset_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.restrictedChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.inverse_apply_coord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacian_continuous_of_restricted_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.coordinateSecondDerivative.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_inverseGram_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.laplacianAt_eq_chart_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.IntrinsicLaplacianCoordinateForm.hessianAt_eq_chart_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt.congr_simp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### probe-097

```sh
rg -n '^(noncomputable )?(def|theorem) (coordinateScalar|coordinateScalar_support|coordinateScalar_contDiff_two|exists_shrunk_chart_cover|exists_shrunk_cover_global_coefficients|density_inverseMetric_compatibility_of_eventuallyEq|chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one|chartTransportedLeviCivitaSection|chartMetric_posDef|chartMetric_symm|metric_isInvertible|contDiff_blendedChartMetric|blendedChartMetric_symm|christoffel_eq_connection|koszul_apply|inverseEntries_eq_coordinates|inverse_pairing_symm|laplacianAt_eq_trace_hessianContinuousAt|laplacianAt_eq_sum_hessianAt_basis|metricDualVectorAt_basis_coord_eq_sum_inv|inverseChartEuclideanTangentBasisAt|inverseChartEuclideanTangentBasisAt_apply|map_rawHausdorffCoordinateDensityMeasure_inclusion|extDerivFun_apply_fixed_chart|deTurckChartMetric_contDiffAt_two_of_mem_target|g_covariantDeriv_coordGradient_eq_covariantHessian|covariantHessianForm_eq_covariantHessian|christoffelClosedOp_apply|modelLeviCivita_apply|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three)' Poincare/Global/ClosedLaplacianStokesProducer.lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean Poincare/Global/Laplacian.lean Poincare/Global/ScalarVariation.lean Poincare/Global/LeviCivitaTransport.lean Poincare/Global/DeTurckPrincipalIdentity.lean Poincare/Global/CoordinateChartFrameDensityVariation.lean Poincare/Global/HausdorffInverseChartMeasureTransport.lean Poincare/Global/DeTurckBUCCoefficientIdentification.lean Poincare/ChartIdentification.lean Poincare/ChartTransport.lean Poincare/ModelChristoffel.lean Poincare/ModelLaplacian.lean
```

Exit code: `0`.

Actual output:

```text
Poincare/ChartTransport.lean:91:theorem chartMetric_symm [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:135:theorem chartMetric_posDef [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:295:theorem blendedChartMetric_symm (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ChartTransport.lean:597:theorem contDiff_blendedChartMetric_scalar
Poincare/ChartTransport.lean:638:theorem contDiff_blendedChartMetric
Poincare/ChartTransport.lean:767:theorem contDiff_blendedChartMetric_scalar_eq :
Poincare/ChartTransport.lean:772:theorem contDiff_blendedChartMetric_eq :
Poincare/ChartTransport.lean:795:theorem chartMetric_symm_eq :
Poincare/ChartTransport.lean:805:theorem chartMetric_posDef_eq :
Poincare/ChartTransport.lean:846:theorem blendedChartMetric_symm_eq :
Poincare/Global/DeTurckPrincipalIdentity.lean:24:theorem koszul_apply (J : Jet1) (u v q : E) :
Poincare/Global/DeTurckPrincipalIdentity.lean:76:theorem inverseEntries_eq_coordinates (G : Bilin) (hG : G.IsInvertible) :
Poincare/Global/DeTurckPrincipalIdentity.lean:100:theorem inverse_pairing_symm (G : Bilin) (hG : G.IsInvertible)
Poincare/Global/DeTurckPrincipalIdentity.lean:384:theorem christoffel_eq_connection
Poincare/Global/HausdorffInverseChartMeasureTransport.lean:49:theorem map_rawHausdorffCoordinateDensityMeasure_inclusion
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:90:theorem exists_shrunk_chart_cover
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:259:theorem density_inverseMetric_compatibility_of_eventuallyEq
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:284:theorem exists_shrunk_cover_global_coefficients
Poincare/Global/Laplacian.lean:495:theorem laplacianAt_eq_trace_hessianContinuousAt
Poincare/Global/ClosedLaplacianStokesProducer.lean:83:def coordinateScalar (p : M) (f : M → ℝ) : E → ℝ :=
Poincare/Global/ClosedLaplacianStokesProducer.lean:89:theorem coordinateScalar_support (p : M) (f : M → ℝ)
Poincare/Global/ClosedLaplacianStokesProducer.lean:108:theorem coordinateScalar_contDiff_two (p : M) (f : M → ℝ)
Poincare/Global/CoordinateChartFrameDensityVariation.lean:105:theorem metricDualVectorAt_basis_coord_eq_sum_inv
Poincare/Global/CoordinateChartFrameDensityVariation.lean:204:def inverseChartEuclideanTangentBasisAt
Poincare/Global/CoordinateChartFrameDensityVariation.lean:214:theorem inverseChartEuclideanTangentBasisAt_apply
Poincare/ChartIdentification.lean:107:theorem extDerivFun_apply_fixed_chart {f : M → 𝕜} {x₀ y : M}
Poincare/ChartIdentification.lean:577:theorem extDerivFun_apply_fixed_chart_eq :
Poincare/Global/LeviCivitaTransport.lean:28:noncomputable def chartTransportedLeviCivitaSection
Poincare/Global/LeviCivitaTransport.lean:35:theorem chartTransportedLeviCivitaSection_apply
Poincare/Global/LeviCivitaTransport.lean:46:theorem chartTransportedLeviCivitaSection_apply_chart
Poincare/Global/LeviCivitaTransport.lean:111:theorem chartTransportedLeviCivitaSection_mlieBracket_apply_chart
Poincare/Global/LeviCivitaTransport.lean:157:theorem chartTransportedLeviCivitaSection_mdiffAt_apply_chart
Poincare/Global/LeviCivitaTransport.lean:625:theorem chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one
Poincare/Global/DeTurckBUCCoefficientIdentification.lean:435:theorem deTurckChartMetric_contDiffAt_two_of_mem_target
Poincare/ModelChristoffel.lean:167:theorem modelLeviCivita_apply (b : Π x : F, LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:310:theorem metric_isInvertible {x : F} (b : LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:999:theorem metric_isInvertible_eq :
Poincare/ModelChristoffel.lean:1087:theorem modelLeviCivita_apply_eq :
Poincare/Global/ScalarVariation.lean:764:theorem chartTransportedLeviCivitaSection_extend_apply_chart
Poincare/Global/ScalarVariation.lean:2125:theorem laplacianAt_eq_sum_hessianAt_basis
Poincare/ModelLaplacian.lean:4121:theorem christoffelClosedOp_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ModelLaplacian.lean:27677:theorem g_covariantDeriv_coordGradient_eq_covariantHessian
Poincare/ModelLaplacian.lean:27740:theorem g_covariantDeriv_coordGradient_eq_covariantHessian'
Poincare/ModelLaplacian.lean:28482:theorem g_covariantDeriv_coordGradient_eq_covariantHessian_field
Poincare/ModelLaplacian.lean:28854:theorem covariantHessianForm_eq_covariantHessian (G : E → E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ModelLaplacian.lean:35568:theorem g_covariantDeriv_coordGradient_eq_covariantHessian_eq :
Poincare/ModelLaplacian.lean:35578:theorem g_covariantDeriv_coordGradient_eq_covariantHessian'_eq :
Poincare/ModelLaplacian.lean:35683:theorem g_covariantDeriv_coordGradient_eq_covariantHessian_field_eq :
Poincare/ModelLaplacian.lean:35733:theorem covariantHessianForm_eq_covariantHessian_eq :
Poincare/ModelLaplacian.lean:36143:theorem christoffelClosedOp_apply_eq :
```

### probe-098

```sh
rg -n '^theorem (scalarAt_contMDiffAt_two_of_normalizedRicciFlow|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three)' Poincare/Global
```

Exit code: `0`.

Actual output:

```text
Poincare/Global/MetricFlowJointRegularity.lean:320:theorem timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowScalarRegularity.lean:91:theorem scalarAt_contMDiffAt_two_of_normalizedRicciFlow
```

### probe-099

```sh
git diff --stat 84a8c86c522b3ea9c7d9d94cbcc17e0573f4f3f5..HEAD
```

Exit code: `0`.

Actual output:

```text
 .../Global/IntrinsicLaplacianCoordinateForm.lean   | 722 +++++++++++++++++++++
 1 file changed, 722 insertions(+)
```

### probe-100

```sh
git rev-parse HEAD
```

Exit code: `0`.

Actual output:

```text
4f0def7b4e1831ba8c7e03282eb3e4194167a233
```
