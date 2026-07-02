Read harness/worker_contract.md first and obey it strictly.

# Task M0-align-mathlib: pin our PoincareConjecture to Mathlib's official spelling

Context: `Poincare/Global/Statement.lean` (already merged) defines `Poincare.PoincareConjecture`. Mathlib itself has statement-only stubs in `.lake/packages/mathlib/Mathlib/Geometry/Manifold/PoincareConjecture.lean` (`proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three` etc.). `proof_wanted` declarations are not importable terms, so restate them.

Deliverable: NEW file `Poincare/Global/Alignment.lean` (+ import in `Poincare.lean`):

1. `def MathlibPoincareStatement : Prop` — an EXACT transcription of the statement body of Mathlib's `SimplyConnectedSpace.nonempty_homeomorph_sphere_three` proof_wanted (read the Mathlib file; copy its hypotheses verbatim, including its model space/smoothness spelling and universe handling).
2. `theorem poincareConjecture_iff_mathlib : PoincareConjecture ↔ MathlibPoincareStatement` — or, if hypotheses genuinely differ (e.g. Mathlib assumes topological not smooth, or omits second countability), prove whichever implication(s) hold with an honest comment block explaining the gap, and record the mismatch in `harness/reports/M0-align_notes.md`. Do NOT weaken either statement to force an iff. Frozen statement rule applies to `PoincareConjecture` — you may not modify Statement.lean's definition; if the mismatch requires changing it, write the blocked-report instead.

Universe care: our def is universe-polymorphic; match universes explicitly.

Build with `lake build Poincare.Global.Alignment` (be patient with first build), verify, commit. Report the exact final theorem names.
