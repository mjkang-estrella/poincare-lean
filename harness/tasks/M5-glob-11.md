Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-11: the Christoffel transition law — the chart-change formula

Context: `harness/reports/M5-glob-10_blocked.md` (READ FIRST — the VERBATIM velocity-component transition hypothesis). PROVEN: the reanchor assembly GIVEN the transition (`ReanchorLawFinal.lean`). THE CLASSICAL LAW: under a chart change `σ = chart₁ ∘ chart₀⁻¹`, the Christoffel action transforms as `Γ¹(σ(x))(Dσ u, Dσ w) = Dσ (Γ⁰(x)(u, w)) + D²σ(x)(u, w)` (the second-derivative correction — the transformation making the geodesic equation covariant: if `γ'' = −Γ⁰(γ)(γ',γ')` then `(σ∘γ)'' = Dσ γ'' + D²σ(γ',γ') = −Γ¹(σγ)(…)`). THE SOURCE OF THE LAW IN THIS REPO: `chartChristoffel` is DEFINED from the metric via the Koszul/Levi-Civita construction (`ChartIdentification/LocalConnectionRegularity/KoszulExistence/GeodesicChart.lean` — READ how the transition of the METRIC (the blended chart metric transforms by pullback) induces the transition of the Christoffels — the Koszul formula is natural under diffeos, so the law follows by uniqueness of the Levi-Civita connection in each chart (`LeviCivitaUniqueness.lean`!): both `Γ¹` and the σ-transported `Γ⁰` are metric-compatible torsion-free for the SAME chart-1 metric ⟹ EQUAL). ASSEMBLE the law (velocity-component form as demanded) → feed `ReanchorLawFinal` → the reanchor law → the naturality chain → `RigidStepCompatibleWith` → THE CHAIN FIRES. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-11_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ChristoffelTransition.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ChristoffelTransition` and report the actual result. Commit your work.
