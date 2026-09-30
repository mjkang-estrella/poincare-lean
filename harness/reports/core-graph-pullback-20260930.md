# Actual nonlinear derivative Graph pullback toward Hamilton existence

Date: 2026-09-29 America/Los_Angeles. Published base:
`844c8fa9d96ff809406d77c47fb8c06d717ff915`. Accepted Graph source:
`f2f4cab36602709cdf9dde3a24aa323dfb1fd75e`.

## Core obligations remain open

Neither ExistsSmoothabilitySmoothManifoldStatement nor
UniversalHamiltonConvergenceStatement is discharged. The latter is equivalent
to universal positive-Einstein existence on closed simply connected smooth
three-manifolds:

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

Smoothability still needs a replacement charted-space structure over the same
given topology carrying IsManifold infinity for every target topological M.
The exact quantified core types, stronger universal HamiltonFrontInputs and
required actual flow/compact limit/third-jet witnesses are in their
authoritative Lean definitions and core-local-parametrix-20260930.md.
The reserved Poincare.poincare_conjecture remains absent.

The central route still constructs general Ricci-flow inputs from an actual
initial metric, without sphere recognition or the final theorem as a premise.
Global continuation/surgery, independent smooth reconstruction and favorable
metric/limit construction are substantive open stages. This is a construction
program, not an assertion those stages are already formalized.

## Constructed Graph operator and concrete consumer

The previous actual metric producer constructs an atlas, buffers, local scalar
operators and globally smooth compact gated chart changes. Its nonlinear Y
pullback already handles scalar/vector/covector/Hessian carriers. This batch
constructs the actual derivative-compatible Graph operator from that F, with
no supplied operator or derivative-bound package:

```lean
∀ (F : ClosedSmoothModel 3 → ClosedSmoothModel 3),
  ContDiff ℝ ∞ F → HasCompactSupport F →
  ∀ (α : ℝ), 0 < α → α < 1 →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Set.Ioc (0 : ℝ) 1,
    ∃ Q : ParabolicSolutionGraph.Graph (E := ClosedSmoothModel 3) α T →L[ℝ]
          ParabolicSolutionGraph.Graph (E := ClosedSmoothModel 3) α T,
      ‖Q‖ ≤ C ∧ ∀ G p,
        (Q G).u p = G.u (p.1, F p.2) ∧
        (Q G).ut p = G.ut (p.1, F p.2) ∧
        (∀ v, (Q G).du p v = G.du (p.1, F p.2) (fderiv ℝ F p.2 v)) ∧
        (∀ v w, (Q G).ddu p v w =
          G.ddu (p.1, F p.2) (fderiv ℝ F p.2 v) (fderiv ℝ F p.2 w) +
          G.du (p.1, F p.2) (fderiv ℝ (fderiv ℝ F) p.2 v w))
```

The output retains the original Graph zero trace, both spatial derivative
certificates, within-Icc time derivative and full four-component sum norm.
The identities hold at all ambient points; outside the cylinder all relevant
Y carriers vanish. Actual compact smooth derivative carriers provide DF,D2F
and their bounds before T. The Hessian term uses the constructed two-slot
operator; the second chain-rule term uses the actual covector/D2F composition
CLM. Graph.ext_of_u proves linearity after certificates are present. A real
four-component norm estimate constructs the CLM with mkContinuous.

Both auxiliaries explicitly help core H and name this Graph proof as consumer.
The actual-metric application check instantiates the previous producer,
constructs its gated maps and obtains these Graph operators for those same F.
No unconstructed geometric or bound input is hidden in the interface.

The next concrete consumer is bounded destination-only tensor Graph transport.
For destination i/source j and tensor slots, construct the smooth compact
weight from theta_ij, destination partition evaluated in its inverse chart,
source outer xi_j(F_ij z), and the two actual DF_ij Jacobian components.
Theta support lies in the true overlap, so the destination scalar partition
is smooth there; the existing scalar cutoff extension makes the whole weight
globally smooth compact. Actual cutoff graph operators composed with the new
Q_F then transport each tensor entry. Finite summation must prove destination
support, symmetry and actual transition compatibility and a common norm.
Source carriers are already partition weighted; another source partition
changes reconstruction. F agrees with the true change germwise on every
gate-support point. The outer source cutoff equals one on actual local solver
outputs, so it can be removed in the desired value identity there. None of
this complete tensor assembly is supplied by the new scalar Graph theorem.

## Exact remaining operator and physical shapes

Still unconstructed: actual bounded L:X_M ->L Y_M, P:Y_M ->L X_M and
R:Y_M ->L Y_M matching the genuine DeTurck operator including lower terms,
with L.comp P=id-R and normR<1. The scalar local residual is id+R_i, so the
global sign must be proved explicitly. Then nonlinear inversion in a genuine
parabolic jet norm, matched initial-time jets and bootstrap are required.

The physical target remains:

```lean
∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, MetricEntriesJointContDiffAt gt t x 3
```

Within-Icc time differentiation does not provide ordinary joint C3 at zero;
the zero-extension obstruction remains. The physical target and frozen final
Poincare statement were not changed. Actual global flows, favorable metrics,
Hamilton front inputs and required limits remain open.

## Verification and preserved failed evidence

Root independently reran all four scoped gates from each recorded base and
reviewed the actual source-only diffs. Fresh source and exact frozen types,
forbidden-token/diff checks and foundational axiom gates passed. Focused
internal-inclusive scans permit only propext, Classical.choice and Quot.sound.
The Hessian preflight resolved Norm(CLMap YHess ->YHess) by pinning the existing
canonical Submodule.normedSpace locally; independent Lean checks proved the
norm unchanged. No new assumption or alternative norm was introduced.

All failed preflights, source/compiler attempts and final diffs are retained
in portable gzip manifests. A worker-owned expanded theorem registry scan
used excessive memory and was stopped, with its request/output/resource/exit
evidence preserved. The focused module scan checked every emitted constant
without expanded type/value export and passed. These are local Codex
orchestrator helpers, not registered Pi/Leanstral runtime Jobs. No model
service, remote harness or other worker source was altered.

The integration checkpoint at `e263e07838ea1a80e13d204f3ebfe23674a1d5f1`
passed fresh root source, full Lake build, interface, mathlib-gap, shape,
theorem-contract, semantic, root-import and axiom audits. All new module
dependencies were independently scanned without expanded metadata export.
Completion failed only because the reserved final declaration is absent.
The full source-bound receipt and outputs are archived in the integration
evidence manifest. Neither universal core is discharged; the full objective
remains active.
