# Fixed-chart local successor equality blocked

Date: 2026-09-08. Branch: `worker/fixed-chart-local-successor-equality`.
Frozen base: `ff85a298a835630b835e5699599db7d4021b0686`.
Verified proof head: `d2b5a259e8d646a7eee2b845d0bd99ebc60908af`.

The requested `exists_radii_of_uniformDifferentialPullback` is not proved
or declared. Its exact-signature probe fails with an unknown identifier.
The unconditional equality `OnCompact` is not established. This result
proves the uniform full-ball common-source conjunct and reduces the remaining
equality to one explicit supplied endpoint identity. It does not complete
task 9, H2, or sphere recognition.

Only the new `Poincare/Global/FixedChartLocalSuccessorEquality.lean` and this
report are changed. Existing Lean files, `Poincare.lean`, audit wiring,
other workers' files, tasks, ledgers, and `HANDOFF.md` are untouched. The
explicit worker scope takes precedence over the general handoff-update
instruction. The assigned isolated worker branch is retained. No merge or
task acceptance was performed.

## Verified partial result

The main unconditional theorem has this exact signature, in the task's
manifold and metric instance context:

```lean
theorem exists_uniform_common_source_radii
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
        (d : Data (patch C D) ⟨x, p, L⟩ z), dist z x < η →
        ball z ε ⊆ (germ (patch C D) ⟨x, p, L⟩).source ∩
          (germ (patch C D) d.successor).source
```

It chooses both positive radii before every moving anchor, alignment,
point, and actual datum. It covers the full ball in both actual sources.
There is no curvature, cutoff-one, H1, path-independence, or equality premise.
The theorem applies to every compact `K,H` satisfying the prescribed patch
inclusions, including empty sets and singleton centers.

The proof proceeds through these verified results:

1. `exists_uniform_endpoint_radius_into_open` strengthens the endpoint
   retention estimate to any prescribed open neighborhood of the compact
   anchor set. Joint continuity of the retained product endpoint and the
   fixed inverse manifold chart yields one velocity radius by compactness.
2. `exists_uniform_domain_radius_into_open` combines that estimate with the
   landed moving-anchor operator bound and normal-vector control. It keeps
   both new anchors in prescribed open neighborhoods and proves actual
   predecessor-source membership.
3. `exists_uniform_common_source_radii` chooses compact neighborhoods
   `K',H'` inside the retained open patches. The preceding theorem keeps
   successor anchors in their interiors. Task 8's domain theorem applied
   over `K',H'` then controls every successor alignment, including each
   datum's actual alignment. A separate predecessor domain radius and the
   triangle inequality provide its source inclusion on the same ball.

In the third proof, `η = min ηr (ηo / 2)` and
`ε = min (ηo / 2) ηn`. All three input radii were already chosen uniformly.
No minimum of separately chosen per-anchor or per-datum radii is taken.

The original task's `OnCompact` definition is preserved verbatim. A direct
text comparison with task 9 in `parametrization-plan-2.md` returned:

```text
ONCOMPACT_FROZEN_TEXT_MATCH=true
```

## Exact remaining statement

The source defines the remaining analytic identity as follows:

```lean
def UniformEndpointReanchoring (Q : Interpretation g) (K : Set M)
    (H : Set RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : Data Q ⟨x, p, L⟩ z), dist z x < η →
      ∀ v : E, ‖v‖ < ρ → v ∈ (Q.sourceNormal z).target →
        map Q ⟨x, p, L⟩ ((Q.sourceNormal z).symm v) =
          (Q.targetNormal (map Q ⟨x, p, L⟩ z)).symm (linear Q d.successor v)
```

For `Q = patch C D`, this compares the predecessor map evaluated at the
supplied endpoint centered at `z` with the supplied target endpoint centered
at its actual image. The velocity is in the actual successor endpoint
domain. The requested uniformity remains explicit in `η,ρ`, both chosen
before `x,p,L,z,d`. The statement does not assume a metric-ball inclusion
or a metric-ball equality conclusion.

The missing curvature-only producer has this checked proposition type:

```lean
def resisting_spec : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    UniformEndpointReanchoring (patch C D) K H
```

This is a proposition definition in a scratch probe, not a theorem. No
inhabitant or additional unproved theorem is introduced.

`exists_onCompact_of_uniformEndpointReanchoring` proves that this one
remainder gives the exact H2 `OnCompact`. It first retains successor anchors
in a compact source neighborhood. The landed normal-vector bound turns one
small ball about every such successor into vectors of norm less than `ρ`.
The endpoint identity, the exact partial inverse law, and the independently
proved common-source radii give equality on the full ball for every datum.

`exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring`
then combines this reduction with task 8's
`exists_onCompact_of_uniformDifferentialPullback`, using the minimum of the
two already uniform predecessor radii. H1 and H2 use that same `η`; the
positive evaluation radius is retained. Both analytic premises are explicit
in the theorem's name and type. This conditional theorem is the blocked
reduction required by the M5-glob-69 stop condition, not the requested
one-premise theorem under another name.

## Why the equality route stops

The inspected ODE comparison
`FTransitionGeodesicMap.mappedState_eqOn_Icc_target_of_F_transition`
needs a `C²` map and the Christoffel transition identity along the entire
source trajectory, plus a common Lipschitz region containing both target
trajectories. For the supplied patch map, the corresponding map is
`chartMap (patch C D) s` in the fixed host charts. The stored datum proves
a strict derivative and metric pullback at the single point `z`. It does
not provide that trajectory-wide transition identity or a uniform region
on which it holds. The retained source and target flow times also have to
be normalized consistently before comparing their endpoints.

`DifferentialSuccessorIntervalNaturality` proves the old preferred-chart
version. Its private
`reanchoredChartMap_expAtChart_naturality_ball_of_transition` takes old
`DifferentialInducedSuccessor.Data`, old exponentials, and a transition
hypothesis for the old chart map. Its output radius is selected after the
datum. These types and quantifiers do not supply the displayed remainder.

Task 7's `patch_germ_eventuallyEq_generic` gives agreement near the fixed
predecessor anchor. It does not give agreement near every `z` on a radius
uniform over moving anchors and alignments. Its `local_equality_transfer`
requires exactly that predecessor agreement near `z` as an input.
Witness independence identifies successors for two data of the same map;
it does not identify a predecessor map with its successor on a neighborhood.

The inspected
`exists_metricBall_eqOn_coordinateControlled_of_pathIndependence` retains
its explicit cross-history premise and selects the final radius after the
data. Neither that premise nor that radius was used here. No future global
chain-independence theorem was assumed.

The new compactness argument resolves the uniform domain estimate. This
attempt does not prove the uniform reanchoring/ODE identity. It does not
claim a counterexample to the frozen target.

## Proof commits and direct checks

Each lemma was committed after successful direct elaboration of the
cumulative new module. Every direct compiler log below is empty and the
wrapper printed `LEAN_EXIT=0`. There were no source-compiler retries.
Evidence is in `/tmp/fixed-chart-local-successor-equality-evidence/`.

| Commit | Theorem | Log |
| --- | --- | --- |
| `feba2762` | `exists_uniform_endpoint_radius_into_open` | `01-endpoint.log` |
| `82a0313d` | `exists_uniform_domain_radius_into_open` | `02-retention.log` |
| `2d439561` | `exists_uniform_common_source_radii` | `03-common-source.log` |
| `324ea12f` | `exists_onCompact_of_uniformEndpointReanchoring` | `04-equality-reduction.log` |
| `d2b5a259` | `exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring` | `05-bundle.log` |

The actual direct command for each was:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorEquality.lean
```

## Focused build and axiom checks

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh \
  /private/tmp/poincare-workers/fixed-chart-local-successor-equality \
  Poincare.Global.FixedChartLocalSuccessorEquality \
  Poincare.FixedChartLocalSuccessorEquality.exists_uniform_endpoint_radius_into_open \
  Poincare.FixedChartLocalSuccessorEquality.exists_uniform_domain_radius_into_open \
  Poincare.FixedChartLocalSuccessorEquality.exists_uniform_common_source_radii \
  Poincare.FixedChartLocalSuccessorEquality.exists_onCompact_of_uniformEndpointReanchoring \
  Poincare.FixedChartLocalSuccessorEquality.exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring
```

Exit 0. Actual `06-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartLocalSuccessorEquality.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartLocalSuccessorEquality ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3609/3609] Built Poincare.Global.FixedChartLocalSuccessorEquality (2.0s)
Build completed successfully (3609 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=7 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartLocalSuccessorEquality.exists_uniform_endpoint_radius_into_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_uniform_domain_radius_into_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_uniform_common_source_radii' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_onCompact_of_uniformEndpointReanchoring' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is replayed from an unchanged dependency. Every named theorem
has exactly `[propext, Classical.choice, Quot.sound]` as its axiom closure.
The module-wide scan covers all seven declarations, including the two
proposition definitions. This is a passing partial-module gate, not task
acceptance. No full root build or integration audit was run.

## Signature and target probes

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-equality-evidence/07-partial-signatures.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-equality-evidence/09-remainder-spec.lean
```

Both exit 0 with no compiler output. The first checks all five theorem
signatures as separate `example` declarations. The second elaborates the
curvature-only resisting proposition above.

The task-9 target was extracted from the specification, with exactly the
orchestrator-authorized `UniformDifferentialPullback` premise added and the
requested theorem name used as its proof:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-equality-evidence/08-requested-target.lean
```

Exit 1. Actual preserved compiler output:

```text
/tmp/fixed-chart-local-successor-equality-evidence/08-requested-target.lean:31:8: error(lean.unknownIdentifier): Unknown identifier `exists_radii_of_uniformDifferentialPullback`
```

Its axiom closure cannot be inspected because the requested declaration is
absent. Neither the original `exists_radii` nor the authorized one-premise
replacement has been declared with a weakened type.

Final checks:

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorEquality.lean
git diff --check
git diff ff85a298a835630b835e5699599db7d4021b0686 --check
```

Token scan: exit 1 with no matches. Both whitespace checks: exit 0 with no
output. The verified source diff is preserved as `proof.diff` and can be
regenerated with:

```sh
git diff ff85a298a835630b835e5699599db7d4021b0686 d2b5a259e8d646a7eee2b845d0bd99ebc60908af -- Poincare/Global/FixedChartLocalSuccessorEquality.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorEquality.lean
```

The next mathematical action is to prove `resisting_spec`, using the fixed
host chart map and the retained, time-normalized geodesic flows. The uniform
full-ball common-source inclusion is already available unconditionally.
