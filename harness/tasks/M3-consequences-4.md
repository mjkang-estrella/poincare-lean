Read harness/worker_contract.md first and obey it strictly.

# Task M3-consequences-4: the time-tracked scalar lower bound (Hamilton's R_min monotonicity)

On main: `hamilton_finite_time_singularity'` (witness discharged at ONE time), `exists_scalarAt_isMinOn`, `laplacianAt_nonneg_of_isLocalMin`, `hamilton_scalar_minimum_riccati_step_at`, and the model's ODE comparison suite (`ode_comparison_nonneg`, `riccati_lower_bound`, `parabolic_min_principle*` — MaximumPrinciple.lean; read them).

Target: Hamilton's scalar lower-bound preservation along the flow — the closed-manifold `hamilton_scalar_lower_bound` analogue:
for a closed Ricci-flow solution on [t₀, T] (honest hypotheses: the flow + regularity classes at every (t,x) in the track, continuity/differentiability in t of the relevant quantities), if `R_min(t₀) ≥ c` then `R(y,t) ≥ [the Riccati comparison solution] ≥ c` for all t (for c ≥ 0; the sharper c/(1−(2c/n)(t−t₀)) form if clean).

Route (the classical Hamilton trick, model template `hamilton_scalar_lower_bound`):
1. Define `Rmin(t) := the infimum of scalarAt over M at time t` (compactness → attained; `exists_scalarAt_isMinOn`). Continuity/one-sided differentiability of Rmin in t is the classical subtlety — the model handles it via the supersolution comparison (`heat_supersolution_nonneg_preserved` / `parabolic_min_principle` patterns); mirror whichever formulation ports: the cleanest honest route may be the CONTRADICTION form: if R drops below the comparison at some first time (exists_first_zero, on main), at the attained minimum point the Riccati step (`hamilton_scalar_minimum_riccati_step_at`) contradicts the drop.
2. State honestly with the needed track-level regularity classes (uniform-in-(t,x) versions where required — add honest classes + witnesses as usual).
3. Corollary: nonneg scalar curvature is preserved (`c = 0` case) — a headline closed-manifold theorem.
4. Done-report.

Multi-session acceptable; the comparison skeleton + the first-drop contradiction lemma is the minimum. Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution`, report names.
