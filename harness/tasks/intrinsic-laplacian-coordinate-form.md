# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/intrinsic-laplacian-coordinate-form`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/intrinsic-laplacian-coordinate-form_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo; record every probe with actual output. A blocked report displaying the exact resisting goal with committed partial lemmas is acceptable; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and, in full, `harness/reports/closed-laplacian-stokes-global-coefficients_blocked.md` (especially "Item 3: exact resisting identity", which displays the exact residual goal after rewriting with `laplacianAt_eq_trace_hessianContinuousAt`, and "Constructor and flow boundaries", which explains why the landed full-target constructor cannot consume a shrunk domain) and `harness/reports/closed-laplacian-stokes-producer_blocked.md`. Landed and directly relevant, all under `Poincare/Global/`: `ClosedLaplacianStokesProducer.lean` (`coordinateScalar` and its support/C² lemmas, `localizedLaplacian_continuous_of_coefficients`, `geometry_of_coordinate_coefficients`, `openChart_measure`, `openChart_density_integrable`, `chartWeight_regular`, `chartInverseMetric_contDiffOn`), `ClosedLaplacianStokesGlobalCoefficients.lean` (`exists_shrunk_chart_cover`, `exists_global_coefficients_on_compact`, `exists_shrunk_cover_global_coefficients`, `density_inverseMetric_compatibility` and its `_of_eventuallyEq` transfer, `fderiv_chartWeight`, `fderiv_chartInverseMetric`), `Laplacian.lean` (`laplacianAt`, `laplacianAt_eq_trace_hessianContinuousAt`), `LeviCivitaTransport.lean` (`chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` at line 625 — the bridge the previous worker identified as the right tool but did not apply), `DeTurckPrincipalIdentity.lean` (`christoffel_eq_connection`, `koszul_apply`), `NormalizedFlowHausdorffPartitionStokes.lean` (the record `FiniteSubordinateHausdorffLaplacianGeometry`, `christoffelCoordinateLaplacian`, and the record's `closedLaplacianStokes` theorem).

# Task intrinsic-laplacian-coordinate-form

Module: `Poincare/Global/IntrinsicLaplacianCoordinateForm.lean`. Namespace: `Poincare.IntrinsicLaplacianCoordinateForm`. Imports: `Poincare.Global.ClosedLaplacianStokesGlobalCoefficients` (add what you need).

This task has two parts. Part A is the mathematical core; part B is the plumbing that consumes it. Land whatever compiles; part A alone is a success.

**Part A (the resisting identity).** For a smooth metric `g` on a closed 3-manifold, a chart anchor `p`, an open `V` with `closure V` inside the chart source, a `C²` scalar `φ` with `tsupport φ ⊆ V`, and `z` in the coordinate image of `V`, prove

```lean
g.laplacianAt φ (inverseExtendedChartParametrization (n := 3) p z) =
  christoffelCoordinateLaplacian a Γ
    (ClosedLaplacianStokesProducer.coordinateScalar (n := 3) p φ) z
```

with `a` the genuine inverse Gram field and `Γ` the standard Christoffel array of the chart Gram field (use the exact spellings from the blocked report's diagnostic source, reproduced there in full; probe the statement before proving it).

Route: rewrite the left side with `laplacianAt_eq_trace_hessianContinuousAt`, which leaves the metric trace of the intrinsic scalar Hessian (the exact resulting goal is printed in the blocked report). Then:
1. Identify the intrinsic covariant Hessian of `φ` at that point with the coordinate expression `∂ᵢ∂ⱼ φ̂ − Γᵏᵢⱼ ∂ₖ φ̂` by applying `LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` to the intrinsic gradient and identifying its coordinate derivative; the canonical cutoff is eventually one near `z` because `tsupport φ ⊆ V` and `closure V` is inside the source. `DeTurckPrincipalIdentity.christoffel_eq_connection` and `koszul_apply` give the Christoffel identification in terms of `a` and the first derivatives of the Gram field.
2. Transform the metric trace into the coordinate basis: the trace of the endomorphism obtained from the bilinear Hessian by the metric dual is `aⁱʲ Hessᵢⱼ` in the chart frame. Prove this by evaluating the trace in the chart-induced basis of the tangent space (the repository's `TangentSpace` at that point is modelled on `E`; find the landed lemma that computes `LinearMap.trace` of such a composition in coordinates, or prove it from `LinearMap.trace_eq_sum_of_basis`-type lemmas with the chart basis).
Commit the gradient-transport lemma, the Hessian coordinate identity, the trace identity, and the assembly separately.

**Part B (restricted-domain record and the unconditional theorem).** The landed constructor fixes each coordinate domain to the entire chart target, so its weight and compatibility arguments stay full-target obligations. Add a restricted-domain variant `geometry_of_shrunk_coordinate_coefficients` that takes the shrunk cover of `exists_shrunk_chart_cover`, uses the coordinate image of each `V i` as the record's coordinate domain, and supplies the restricted chart measure, density integrability, coordinate support, and localized-Laplacian measurability fields (adapt the landed proofs of `openChart_measure`, `openChart_density_integrable`, `coordinateScalar_support`, `localizedLaplacian_continuous_of_coefficients` to the smaller domain). Feed it part A and the landed `density_inverseMetric_compatibility_of_eventuallyEq`, then prove

```lean
theorem closedLaplacianStokes_of_contMDiff_two
    (g : ClosedSmoothRiemannianMetric 3 M) (f : M → ℝ)
    (hf : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f) :
    ClosedLaplacianStokes g f
```

and the forward-flow corollary `∀ t ∈ Ici 0, ClosedLaplacianStokes (gt t) (fun x => (gt t).scalarAt x)` for a normalized flow with all-time joint C³ entries (the blocked report confirms this corollary step already compiles from an assumed static theorem).

Exact stop condition: part A's identity compiles and passes the gate, and part B is landed if reachable. A report that lands part A and displays the exact resisting field of part B is a success; a report with neither is blocked.
