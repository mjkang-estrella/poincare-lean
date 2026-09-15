# GPT Astra design review, 2026-09-15

Conversational review (codex MCP, read-only, thread `01a0a5fe-b176-7142-894e-317a252e781b`),
requested by the orchestrator on three design questions. Verbatim conclusions,
with the orchestrator's assessment after each.

## Q1. Parametrix on the finite atlas, not on ℝ³

Recommendation: set the linear problem up on a buffered refinement of the
finite chart cover of `M` with a smooth partition `χᵢ` and cutoffs `ψᵢ = 1`
near `supp χᵢ`; define `Y_M` and `X_M` as closed subspaces of finite products
of the landed scalar `Y α T` / `Graph α T` (one factor per chart and tensor
component) with support conditions and the weighted tensor transition laws as
closed conditions; parametrix `P f = Σᵢ ψᵢ pushᵢ Sᵢ(extendᵢ(χᵢ f))`, error
`R = I − L P`, target estimate
`‖R‖ ≤ C₀ C_S ω_a(ρ) + C_ρ (Λ_a T^{α/2} + T^θ) < 1`
(choose the patch radius `ρ` first, then shorten `T`). Feeds
`ParametrixNeumannCorrection.exists_right_inverse`; the principal part is
`DeTurckPrincipalIdentity.principalIdentity`. Whole-space L6 is only needed
for the survey's literal ℝ³ task 3 and can be dropped.

Assessment: adopted. Replaces survey step L6.

## Q2. Reference family for the nonlinear step

`g* = g₀ + t Q(g₀)`, unknown `v = g − g*`, residual
`N(v) = Q(g* + v) − ∂ₜ g* − DQ(g₀) v`. Correct for smooth `g₀` with
quantitative regularity: `‖N(0)‖_{Y_T} ≤ C_ref (T + T^{1−α/2})` needs a
uniform spatial `C^α` bound on `∂ₜ N(0)`; zero trace alone is insufficient
(`f = t^{α/2}` vanishes initially but has constant temporal seminorm). The
zero-trace interpolation `‖D²v‖_∞ ≤ T^{α/2}[D²v]_{α;p}` (which holds because
`v(0,·) = 0` forces `D²v(0,·) = 0`) controls the product term
`[a]_α ‖D²v‖_∞` but not the full Hessian Hölder norm. Contraction target:
`‖S N(v) − S N(w)‖_X ≤ C_S C_NL (r + T^θ) ‖v − w‖_X` with
`C_S C_NL (r + T^θ) ≤ 1/2` and `C_S C_ref (T + T^{1−α/2}) ≤ r/2`; choose `r`
first, then `T`.

Assessment: adopted as the target shape for task 5. The in-flight
multiplier task proves exactly the zero-trace interpolation and the split
product bound it names.

## Q3. The two Hamilton residuals: a mathematical correction

**The variance-energy clause `∫(R − r)² ≤ 6 ∫|Ric°|²` is not a consequence
of positive Ricci pinching.** Under `Ric ≥ 0` the almost-Schur inequality
(contracted Bianchi `div Ric° = (1/6) dR`, Poisson solvability, integrated
Bochner) gives constant 24 in dimension three, not 6; small conformal
perturbations of the round sphere by a degree-two spherical harmonic have
variance/energy ratio tending to 15 while satisfying `Ric ≥ ε R g` for any
fixed `ε < 1/3`. A Lichnerowicz eigenvalue bound cannot repair this. Hence
the S9 route to the mean floor, as parametrized by the repository constant
6, cannot be discharged along pinched flows; the clause should be kept only
as an explicit hypothesis and the mean floor should come from Hamilton's
scalar oscillation control instead.

Scalar comparison: `exists_pos_uniform_scalarAt_le_mul_meanScalar_of_compact_parameterization_of_meanLower`
exists but with an uncontrolled `C`, so it does not give the coefficient
gap. The recommended first lemma is the normalized scalar-gradient evolution
identity `(∂ₜ − Δ)|∇R|² = −2|∇²R|² + 4⟨∇R, ∇|Ric|²⟩ − 2r|∇R|²`, the start
of Hamilton's gradient argument; gradient decay, diameter control and the
mean floor then give `R_max / r → 1`. Eventual estimates do not discharge
the current all-time quantifiers.

Assessment: the 24-vs-6 point is checked against De Lellis–Topping (sharp
constant `4n(n−1)/(n−2)² = 24` for `n = 3`) and accepted. Consequence: the
mission node `hamilton-reaction-core-energy` and the energy clause in the
initial-pinching cores are honest as hypotheses but are the wrong target
for discharge. The in-flight `hamilton-residual-estimates-survey` was asked
this exact question; its report decides the restructuring. Constants and
the ratio-15 example were not independently verified here.
