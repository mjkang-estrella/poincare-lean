Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-26: covDeltaGamma_koszul — differentiate the Koszul identity (SOLE deliverable)

SCOPE: one lemma family. Read `harness/reports/M3-predicates-25_blocked.md` for the frozen cyclic identity this feeds (do NOT attempt the cyclic identity itself in this task — build its enabling tool).

On main: `deltaGamma_koszul` — under honest hypotheses, `2 * (gt t₀).inner x (deltaGammaAt gt t₀ x v w) z = [∇h 3-term Koszul form]`. Your task: DIFFERENTIATE this identity in the base point, obtaining the ∇δΓ analogue:

`covDeltaGamma_koszul : [C² classes] → 2 * g(covDeltaGammaDerivAt gt t₀ x u v w, z)-shape = [∇²h second-derivative 3-term form + first-order corrections]`

Steps (each its own commit):
1. Promote `deltaGamma_koszul` to a FIELD identity near x (both sides as functions of y — the anchored Gram/extend machinery supports the RHS; the hypotheses classes are the ContMDiff/C² vocabulary on main — take the ∀ᶠ-neighborhood form if global-y is awkward, like `hNear` patterns already in the file).
2. Differentiate both sides at x via `extDerivFun` (LHS: the entry bridge `DeltaGammaEntryDerivativeBridgeAt`-machinery + metric product rule gives g(∇δΓ, z) + corrections; RHS: the ∇h terms differentiate to ∇²h-shaped `extDerivFun∘extDerivFun` entries + corrections — the closed Schwarz lemmas apply to reorder).
3. Solve for `2·g(covDeltaGammaDerivAt ...)` — the closed `covDeltaGamma_koszul`. State it cleanly; static witness sanity check.

This lemma makes the cyclic identity a finite Schwarz/swap computation (next task). Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
