Read harness/worker_contract.md first and obey it strictly (deliverable is a report; honesty rules binding).

# Task M1-asset-audit: inventory the repo's EXISTING manifold-level layer

Discovery: beyond the single-chart coordinate model (ModelLaplacian.lean etc.), this repo contains a manifold-level track over Mathlib's CovariantDerivative: KoszulExistence.lean, CurvatureTensoriality.lean, RicciFlowEquation.lean, ChartTransport.lean, CurvatureConditions.lean, MaximumPrinciple.lean, and possibly parts of other files (LocalConnectionRegularity, ChartIdentification, CurvatureConditions, Smoothability, ...). The new Poincare/Global/* files build on it.

Deliverable: `harness/reports/manifold_assets.md`, committed. For EACH manifold-level file (find them all — grep for `CovariantDerivative`, `TangentSpace I`, `ModelWithCorners` across Poincare/):

1. Key definitions and theorems (names + one-line meaning), and what they genuinely prove.
2. VACUITY/INTEGRITY check per file: does it contain opaque Prop-field certificate structures, trivially-instantiable interfaces, or hypothesis patterns that make the results empty (e.g. predicates never provable, `of_agree` lemmas with unsatisfiable agreement hypotheses)? Be adversarial — this repo previously contained a vacuous scaffold (see INTEGRITY_ASSESSMENT.md); classify each file GENUINE / MIXED / VACUOUS / LEGACY-SCAFFOLD with evidence. In particular: check whether `IsRicciFlowSolutionAt` (RicciFlowEquation.lean) is a real PDE statement (metric time-derivative = -2 Ric pointwise) and whether ANY nontrivial instance beyond the flat/static example is proven.
3. The live frontier of this track: what is the furthest genuine result toward Ricci flow on closed manifolds, and what are the 3-5 most valuable next lemmas (with precise Lean statements where possible)?
4. What in the single-chart model (ModelLaplacian.lean's scalar evolution, Bochner, pinching results) has NOT yet been ported to the manifold track and would port cleanly?

No Lean changes. Commit the report.
