# Constructed chart transport inputs for Hamilton existence

Date: 2026-09-29 America/Los_Angeles. Initial published base:
`119f94393b0ed6ed633313aaf02286ca5299995d`.

## Core obligation and route

The central objective remains `UniversalHamiltonConvergenceStatement`,
equivalent to universal positive-Einstein existence. No entire core assumption
is discharged. `ExistsSmoothabilitySmoothManifoldStatement` is separately
open, and `Poincare.poincare_conjecture` remains absent.

The Hamilton target still requires on every compact connected simply connected
Hausdorff second-countable smooth three-manifold:

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

The smoothability target still requires a replacement ChartedSpace over the
same topology with IsManifold infinity on every target topological M. The
exact quantified core and stronger HamiltonFrontInputs fields are recorded in
`core-local-parametrix-20260930.md` and their authoritative Lean definitions.

The non-circular program reuses the actual initial metric and local solver
family, constructs actual global tensor operators, then physical Ricci flow.
Continuation/surgery, independent smooth reconstruction and favorable
metric/limit construction remain substantive unproved stages. No sphere
recognition or final Poincare theorem is used as a producer input.

## Constructed maps and their consumer

The previous verified local constructor supplies actual A, psi, xi and
P_i/R_i from g0 and alpha. This batch constructs the spatial chart maps needed
for the next bounded tensor transport. It does not take a supplied map or
bound package. Its geometric hypotheses are already supplied by the previous
actual constructor; the successful `ActualMetricUse.lean` application check
instantiates the full producer-to-consumer chain from g0.

For destination i and source j,

```text
K_ij = chart_i '' (tsupport(partition_i) intersect
                  chart_j.symm '' tsupport(xi_j))
O_ij = source(chart_i.symm.trans chart_j) intersect
       destination_cutoff_one_germ_locus intersect
       change_ij preimage source_cutoff_one_germ_locus
```

The actual K is proved compact, O open and K contained in O. The inverse
source-support image stays in the true source chart; destination partition
support stays in its true destination source. Whole overlaps or chart-boundary
compactness are not assumed.

The constructor chooses theta smooth compact, in [0,1], supported in O and
equal to one as a neighborhood germ on K. A second constructed cutoff eta is
one near ALL tsupport(theta). The actual F=eta smul change is globally smooth
and compactly supported. It agrees germwise with the true chart change on
ALL tsupport(theta), and has a constructed global Lipschitz constant for each
pair. The gate prevents spurious source values from the global extension. F
is not asserted globally injective or invertible; only the genuine transition
is used inside the gate. Smooth infinity supplies higher derivatives needed
by later Jacobian-weight jet norms.

Two independent auxiliary proofs are consumed: compact buffered overlap
geometry and global vector-valued cutoff extension. Every Task explicitly
helps core H and names its subsequent consumer. These are real constructions
from inputs already produced along the selected route.

The next consumer is bounded destination-only tensor Graph transport. It must
apply the overlap gate, destination partition, source outer cutoff and genuine
Jacobian contractions, and prove actual derivative fields and a T-uniform norm.
The source carrier is already partition weighted, so another source partition
changes reconstruction. The source outer cutoff equals one on actual P_i.u
supports; its insertion is harmless there. Existing Graph.ext_of_u, actual
cutoff graph operators and verified Jacobian cocycles may be reused.

## Exact remaining operator and physical obligations

True bounded maps L:X_M ->L Y_M, P:Y_M ->L X_M and R:Y_M ->L Y_M must match the
actual global DeTurck operator, including its lower-order terms, and prove
L.comp P=id-R and normR<1. Local residual is L_i(P_i f)-f, hence local id+R_i;
the global sign must be handled explicitly. No operator contraction is
inferred from restricted scalar estimates without actual tensor assembly.

The still-open physical target is
`ClosedRicciFlowNormalization.regularRicciFlowGoal g0`:

```lean
∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, MetricEntriesJointContDiffAt gt t x 3
```

Graph within-[0,T] time derivatives and zero extension do not provide
ordinary joint C3 at zero. Nonlinear inversion in a genuine parabolic jet norm,
matched initial jets and higher regularity remain required. The target was
retained. Later flow continuation, surgery and favorable metric/limit
existence are not supplied by these spatial lemmas.

## Verification evidence

Each geometry helper and gated-map constructor passed fresh source compilation,
exact reviewed type/axiom contracts and scoped token/diff gates. Root reran all
four gates independently from their recorded bases and inspected the actual
source-only diffs. Internal-inclusive scans allow only propext,
Classical.choice and Quot.sound. All compiler attempts, including the failed
preflight set-builder scope and compact-overlap attempts, remain preserved.
Portable gzip manifests retain hashes for worker and independent evidence.
These are local Codex orchestrator helpers, not registered Pi/Leanstral Jobs.
No model service, remote harness or other worker's source changed.

## Constructed nonlinear Holder operator

`ParabolicSpatialHolderPullback.exists_spatial_Y_pullback` constructs actual
Q_T on arbitrary normed real scalar/vector/CLM-valued Y carriers, with no
complete-space premise. For every alpha>=0, a single C>=0 is chosen before
every real T, with norm(Q_T)<=C and exact Q_T f(t,z)=f(t,Fz). Compact smooth F
supplies its own L:NNReal; the proof derives the true parabolic distance
estimate and C=max(1,L^alpha), preserves cylinder membership and zero_off,
constructs the carrier with ofFunction and the CLM with mkContinuous.
Compact support of Q_T f is not claimed. Independent exact/source/axiom gates
and internal-inclusive worker scans passed; all notation-failure evidence is
preserved. The previous actual-g0 application supplies F's literal smooth
and compact premises, so no unresolved geometry/bound package is introduced.

The next Graph objective is:

```lean
∀ (F : ClosedSmoothModel 3 → ClosedSmoothModel 3),
  ContDiff ℝ ∞ F → HasCompactSupport F →
  ∀ (α : ℝ), 0 < α → α < 1 →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Set.Ioc (0 : ℝ) 1,
    ∃ Q : ParabolicSolutionGraph.Graph (E := ClosedSmoothModel 3) α T →L[ℝ]
          ParabolicSolutionGraph.Graph (E := ClosedSmoothModel 3) α T,
      ‖Q‖ ≤ C ∧ ∀ G p, (Q G).u p = G.u (p.1, F p.2)
```

Actual jets must be ut=G.ut(t,Fz), du=G.du(t,Fz) composed with DF(z), and
ddu(v,w)=G.ddu(t,Fz)(DF(z)v,DF(z)w)+G.du(t,Fz)(D2F(z)(v,w)). This is not yet
proved. The full original Graph norm and derivative fields must be retained.
Mathlib already constructs compact support, bounded norm and Lipschitz
constants for DF and D2F from F infinity/compact; the existing
ParabolicCutoffCommutator.exists_cutoff_carrier accepts vector/CLM values and
chooses bounds before T. Its bilinearY supplies actual derivative product
carriers. These verified APIs should be consumed directly.
