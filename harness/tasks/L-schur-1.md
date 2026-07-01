Read harness/worker_contract.md first and obey it strictly.

# Task L-schur-1: Schur lemma — Einstein implies constant scalar curvature (local model)

File: `Poincare/ModelLaplacian.lean` (append near the end, inside the existing namespace structure — note the file has a known 1-off unclosed `namespace RicciFlow`).

Context: this file contains a genuine single-chart Riemannian foundation (~710 theorems, zero sorry). Already proven and available:
- `sum_raised_pair_eq` : Σₖ φ(♯bᵏ)·G(u,bₖ) = φ(u) (raised-pair contraction).
- `fderiv_coordScalar_eq_two_ricciDerivergenceForm_of_contDiff` / contracted second Bianchi: dR = 2 div Ric, self-contained from `G` C³ (search for `fderiv_coordScalar_eq_two_ricciDivergenceForm`).
- `ricciDivergence` (Σₖ covRicciDeriv(♯bᵏ,u,bₖ)-style), `covRicciDeriv`, metric compatibility lemmas (`coord_metric_compatible`, `g_inverse_raise_metric_compat`), `metricTrace` machinery, `coordRicciForm_metric_trace` (tr_g Ric = R).

Goal (the Schur lemma, n ≥ 3): if the metric field G is Einstein as a FIELD near x — i.e. `coordRicciForm G y = (coordScalar G y / n) • (metric bilinear of G y)` for all y in a neighborhood (or globally, whichever matches the file's conventions; use a `∀ y` hypothesis if simpler) — then `fderiv ℝ (coordScalar G) x = 0`.

Proof route (verified by hand):
1. Field-level Einstein + metric compatibility (∇g = 0) ⟹ covRicciDeriv at x in direction v equals ∂_v(R/n) · G (the hard step — the covariant derivative of (R/n)·g).
2. Contract: ricciDivergence G x u = Σₖ ∂_{♯bᵏ}(R/n)·G(u,bₖ) = (1/n)·dR(u) via `sum_raised_pair_eq`.
3. Combine with contracted Bianchi dR = 2 div Ric: dR = (2/n)·dR ⟹ dR·(1 − 2/n) = 0 ⟹ dR = 0 since n ≠ 2 (add hypothesis `3 ≤ n` or `2 < finrank`).

Decompose into small lemmas, each verified with `lake build Poincare.ModelLaplacian` before moving on (incremental builds are cached; the first build may take a while — be patient, do not kill it). Commit each green lemma separately.

Target declaration to report when done: name the final theorem `schur_fderiv_coordScalar_eq_zero_of_einstein_field` (or if you must deviate, record the exact final name in your last message).
