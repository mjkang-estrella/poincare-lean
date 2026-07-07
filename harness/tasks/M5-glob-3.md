Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-3: path chaining — continuation along curves with the uniform radius

Context: `harness/reports/M5-glob-2_done.md` (READ FIRST — its roadmap steps). `CartanContinuation.lean` has germ determinacy, re-anchored germs, existence, two-step continuation (staged on the rigid-10 differential surface). `UniformNormalRadius.lean` gives the uniform radius `r`. THE NEXT STAGE: continuation along an arbitrary path `γ : [0,1] → M` — subdivide by uniform continuity so consecutive points lie within `r`; chain re-anchored germs along the subdivision; prove the endpoint germ is independent of the subdivision (refinement argument via germ determinacy). This is finite-induction bookkeeping over the proven two-step lemma — genuinely mechanical but long; the homotopy-invariance stage comes AFTER (separate task).

Deliverables, in a NEW file `Poincare/Global/CartanChain.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. SUBDIVISION: for a path `γ` and the uniform radius, a finite subdivision with consecutive-point distance < r (uniform continuity of paths into the compact metric space — Mathlib `Metric`/`CompactSpace` API).
2. THE CHAIN: the iterated re-anchored germ data along the subdivision (finite recursion over glob-2's two-step lemma; keep the rigid-10 staging hypothesis as glob-2 did, clearly documented).
3. REFINEMENT INDEPENDENCE: inserting one subdivision point doesn't change the endpoint germ (germ determinacy on the overlap); conclude subdivision independence by common-refinement induction.
4. Report `harness/reports/M5-glob-3_{done|blocked}.md` (next: homotopy invariance, then the global Φ).

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanChain` and report the actual result. Commit your work.
