# C2 covariance, tensor symmetry and forcing transport — 2026-09-30

The selected core remains UniversalHamiltonConvergenceStatement. Neither that
universal existence obligation nor compatible smoothability is discharged.
The complete frozen Poincare theorem remains the goal. This batch closes
local covariance/symmetry obstacles and constructs the bounded forcing
transport needed by the actual global DeTurck residual.

## Exact remaining universal obligations

```lean
Poincare.ExistsSmoothabilitySmoothManifoldStatement : Prop
-- ∀ M [TopologicalSpace M] [T2Space M]
--   [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
--   [SimplyConnectedSpace M] [CompactSpace M],
--   ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
--     letI := charted; IsManifold (𝓡 3) ∞ M

Poincare.UniversalHamiltonConvergenceStatement : Prop
-- ∀ N [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
--   [ChartedSpace (ClosedSmoothModel 3) N]
--   [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
--   [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
--   HamiltonConvergencePinchedLimit3 N
```

The Hamilton payload still requires a genuine smooth metric with scalar
curvature differentiable everywhere, zero traceless Ricci everywhere, and
positive scalar somewhere. The sufficient finite-energy flow interface's
all-forward normalized flow, integrable energy, compact metric realization,
continuous mean-energy pair and positive scalar floor remain unconstructed.
No favorable metric or universal flow/limit witness is inferred from a
parametrix or local variation. Independent smoothability and the produced
Hamilton endpoint feed the existing checked final recognition/reduction.
Later continuation/surgery/energy/limit producers remain unproved links.

## Discharged local obstacles and consumers

`DeTurckChartLiftOverlapJets.chartLift_overlap_twoJet` derives actual
transition C3 and chartMetric(chartLift anchor2 F) neighborhood/full-two-jet
agreement with the true two-slot pullback in chart1, for arbitrary F. It
constructs the transition/neighborhood identities from true overlap rather
than taking them as inputs. Its consumer is the C2 covariance theorem.

`DeTurckC2Covariance.differential_covariance` proves whole Bilin covariance
of the full differential for an arbitrary symmetric C2 coefficient germ.
It constructs a compact smooth symmetric exact-two-jet realization in chart2,
uses the genuine metric-variation covariance, and transfers matching jets
through the proved pullback calculation retaining D3phi. Equality of q and F
as germs, Holder density and coordinate/derivative packages are never assumed.
The inverse variation against the initial metric Hessian and the full actual
background/lower terms are retained. Both cutoff-one germs remain explicit.
Its consumer is actual global L on the original Graph tensor carriers.

`BufferedTensorGraphTransport.exists_destination_Y_entry_transport`
constructs a bounded nine-input forcing row with one bound BEFORE ALL real T.
It uses the original Pi-max/Holder-sum norms, actual compact coefficient
carriers and existing scalar spatial pullback. Raw all-point values, support
and true-chart formula are proved. The destination partition appears once;
source entries keep their existing source weights and source buffer xi.
Its consumer is actual bounded transported global error/residual assembly.
A joint application constructs g0, actual atlas/buffers/gates/extensions from
the metric-adapted producer, invertibility on the actual source buffers, and
all these forcing row families. No candidate atlas or operator is supplied.

`DeTurckDifferentialSymmetry.differential_and_lower_symmetric` proves tensor
symmetry of BOTH full DQ and the combined actual zeroOrder(q)+firstOrder(Dq).
The proof constructs compact exact jets and a genuine metric family,
differentiates the already proved geometric Ricci/Lie symmetry, and subtracts
the symmetric principal Hessian contraction using the actual decomposition.
The combined lower action includes inverse variation against D2g0. Its
consumer is coupled forcing K and the residual's symmetric Y_M codomain.
A joint application uses the original Graph tensor's proved spatial C2
regularity to supply the regularity input, rather than assuming a jet package.

## Exact next local obligation

Actual bounded global operators still need construction:

```lean
L_T : X_M A α T →L[ℝ] Y_M A α T
R_T : Y_M A α T →L[ℝ] Y_M A α T
L_T.comp Pglobal = ContinuousLinearMap.id ℝ (Y_M A α T) - R_T
‖R_T‖ < 1
```

They must use the same actually produced metric, atlas, buffers, transitions,
local S/R, coefficients and Pglobal, with common constants before choosing a
smaller positive time horizon. No supplied global operator/residual package.

First freeze and construct the bounded unweighted Graph reconstruction row.
Use coefficient theta_ij * psi_i * xi_j(F_ij) * DF_ij(slot c)_a *
DF_ij(slot d)_b, replacing the destination partition by the ALREADY PRODUCED
psi_i which is one on a neighborhood of coordSupport_i. Derive actual tensor
reconstruction agreement as a germ on coordSupport_i from the real gate and
buffer identities. Preserve original Graph norm and both ordered Jacobian
slots; retain all product/chain derivative terms. Existing Graph cutoff and
spatial pullback producers construct this row without a new scalar wrapper.

Applying L_i directly to stored chi_i*h_i is wrong: its cutoff derivatives
spoil weighted overlap. Reconstruct the unweighted tensor first, apply
actual dt-DQ, then destination chi_i. Time derivatives must be handled with
the existing Graph certificates on the time interval, not ordinary joint-C3
assumptions. Both spatial covariance and combined forcing symmetry are now
available. Support/range and actual signed identity remain to prove.

The local residual is id+R_i. Full local error is R_i f_i - K_i(S_i f_i).
Its transported sum E gives LPglobal=id+E; the required Rglobal is -E.
The new Y rows give actual bounded transport for that error. Contraction,
nonlinear inversion, matched initial jets/ordinary joint regularity, physical
flow and universal continuation/surgery/favorable-flow/energy/limit production
remain open. No universal core has been marked accepted.

## Verification and preserved evidence

Root independently reran exact-base source-only diff, scoped Lean, token,
whitespace and literal/universe/allowed-axiom gates for every worker result.
All original topologies, scalar actions, norms, frozen core/target definitions
and prior work are preserved. Direct root imports expose all new modules.
All-new-module dependency scans include helpers and reject unsafe/partial
constants or non-foundational axioms. Full integration is batched once.

Every failed compiler attempt, draft/preflight, scope/name repair, final diff,
worker and independent gate is retained append-only. An uppercase draft Task
ID was rejected by schema validation before dispatch; its metadata was
preserved and the ID normalized without changing any literal type. Local
helpers are explicitly not registered Pi/Leanstral Jobs. No dirty or unmerged
historical worktree was removed and no model/GPU service was touched.
