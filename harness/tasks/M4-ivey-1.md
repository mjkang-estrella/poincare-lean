Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-1: GOAL 6 opener — the traceless pinching-improvement front (statement layer)

GOAL 6: toward Hamilton 1982's convergence core — the IMPROVING pinching estimate: on closed 3D flow with Ric > 0 initially, `|Ric°|²/R² ≤ C·R^(−δ)` for some δ > 0 (Ric° = traceless Ricci) — pinching doesn't just persist, it improves as R blows up, forcing roundness at the singularity.

On main: `hamilton_pinching_preserved` + the ENTIRE quotient-evolution toolchain (evolution of |Ric|²/R², gradient damping, spectral reaction sign, max principle for quotient tracks), the traceless vocabulary (`tracelessNormSq`-family in RicciNorm), the eigenvalue algebra (Schur forms, diagonal pins).

STATEMENT + GROUNDWORK discipline (coefficient-pin EVERYTHING on ≥2 patterns before proofs):
1. **The improved quantity**: `def tracelessPinchingAt g x (δ : ℝ) := tracelessRicciNormSqAt / scalarAt^(2−δ)`-shape — first define `tracelessRicciNormSqAt` on the manifold if only the diagonal version exists (|Ric°|² = |Ric|² − R²/3 in 3D — definitional lemma + nonneg + zero-iff-Einstein, mirroring the RicciNorm suite).
2. **The eigenvalue-level key inequality** (Hamilton 1982 Lemma 10.1 shape): for λᵢ ≥ ε·R > 0 (pinched positive eigenvalues), the reaction of |Ric°|²/R^(2−δ) gains a NEGATIVE definite term ~ −δ·(...)+ the Schur-form damping — derive the candidate polynomial inequality at the eigenvalue level, PIN on (1,1,1) (must vanish), (1,1,2), (1,2,3), and a near-degenerate pinched pattern; identify the admissible δ range as a function of the pinching constant ε. State (unproven) the eigenvalue lemma.
3. **The evolution target** (unproven Prop): the parabolic inequality for the improved quantity (the quotient machinery generalizes from exponent 2 to 2−δ — note where the pinch-18/21 lemmas need a general-exponent version vs. literal reuse).
4. Roadmap notes (≤6 subtasks: general-exponent quotient calculus → eigenvalue lemma proof → evolution assembly → max principle with the R_min blow-up from goal 3 → the improvement theorem).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation`, report names.
