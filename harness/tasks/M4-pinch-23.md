Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-23: the eigenbasis witness → the manifold reaction sign UNCONDITIONAL

Read `harness/reports/M4-pinch-22_blocked.md` — the literal next goal is displayed: produce `b : Module.Basis (Fin 3) ℝ (TM x)` and `μ : Fin 3 → ℝ` with `∀ i, g.ricciEndoAt x (b i) = μ i • b i`, then apply the proven `pinchingReactionRemainderAt_nonpos_of_scalar_pos_of_ricciEndoAt_eigenbasis`.

Route (the report's own outlook items 1-2):
1. **The fiber inner-product wrapper**: make the tangent fiber `TM x` an `InnerProductSpace ℝ` w.r.t. `g.inner x` — either (a) a type synonym `GFiber g x := TM x` carrying the instance built from `g.inner` (positive-definite + symmetric — both on main: the metric's positivity and symmetry lemmas), or (b) transport along the orthonormalization isometry to `EuclideanSpace ℝ (Fin 3)` via `metricOrthogonalBasisAt` (the pinch-7 frame) — an orthonormal basis gives a linear isometry equiv; conjugate `ricciEndoAt` through it. PICK the route that instantiates Mathlib's spectral theorem cleanest (route (b) avoids instance diamonds — likely safer).
2. **Self-adjointness**: `⟨Ric#u, v⟩_g = ⟨u, Ric#v⟩_g` (from `ricciAt_symm` + the raise definition — likely one lemma away; check what pinch-22 already added under `ricciEndoAt_selfAdjoint`).
3. **Instantiate** `LinearMap.IsSymmetric.eigenvectorBasis` (finrank = 3 via `g.finrank_tangentSpace_eq`/hn) → pull the eigenbasis back to TM x → the witness → **`pinchingReactionRemainderAt_nonpos_of_scalar_pos`** (n = 3, R > 0, NO other hypotheses).
4. Done-report + the maximum-principle outlook (report item 3: the closed parabolic max principle on Q with damping ≤ 0 and reaction ≤ 0 — the goal-3 `scalarMinimumAt/Track` machinery as template, now for a MAXIMUM of Q).

Standing protocols. No sorry/axiom. BUILD NOTE: use `lake env lean` per-file for iteration; be patient with builds. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
