# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/uniform-buffered-pair-agreement`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/CartanSuppliedBufferedPairAgreement.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/uniform-buffered-pair-agreement_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never weaken the quantifier order).

# Task: uniform agreement of two patch interpretations on compact buffer overlaps

Read first: `harness/reports/supplied-uniform-patch-switch_blocked.md` (sections "Checked mathematical progress"
and "One remaining statement"), then `Poincare/Global/CartanSuppliedUniformPatchSwitch.lean`
(`UniformBufferedPairAgreement`, `exists_switchControl_of_uniformBufferedPairAgreement`,
`buffered_common_source`, `buffered_eventuallyEq`, `exists_fixed_anchor_switch_radius`,
`buffered_eventuallyEq_generic_forall_alignment`), `CartanSuppliedFinitePatchCover.lean` (`QuantitativeCover`,
`Buffered`, `interp`, cores/buffers/zones), `CartanSuppliedDifferentialSuccessor.lean` (`patch`, `patchFrame`,
`linear`, `map`, `germ`), `FixedChartUniformSourceNormal.lean` (`Patch`, `normal`, `endpoint`, the retained flow),
`FixedChartMappedGeodesicAssembly.lean` and `FixedChartUniformEndpointReanchoring.lean` (the mapped-state chain
rule, `geodesic_eqOn_unitInterval`, `normalizedFlow_hasDerivWithinAt`, the uniform Koszul transition law),
`ChartTransitionGeodesicMap.lean` (`GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds`,
`chartTransitionState_eventually_solves_of_initial_nhds`: the geodesic of one chart is the image of the geodesic
of another chart on the double cutoff-one zone), and `FixedChartUniformPreferredGermAgreement.lean`.

Target (frozen), in the instance context of `CartanSuppliedUniformPatchSwitch.lean`:

```lean
theorem uniformBufferedPairAgreement_of_constantCurvature
    (hcurv : HasConstantSectionalCurvature3 g 1) (B : QuantitativeCover g) :
    CartanSuppliedUniformPatchSwitch.UniformBufferedPairAgreement B
```

with the definition used verbatim, then `exists_switchControl` (the frozen task-12 target, via
`exists_switchControl_of_uniformBufferedPairAgreement`).

Mathematics. Two labels `a, b` give two source patches (hosts `chartAt E (center a.1)`, `chartAt E (center b.1)`)
and two sphere patches. At a common state `⟨x, p, L⟩` in both buffers, both interpretations map `z` to the
sphere point reached by the geodesic from `p` with initial velocity `L` applied to the initial velocity of the
geodesic from `x` to `z`; they are the same geometric construction in different coordinates. Concretely:
(1) SOURCE: for `z` in a uniform ball, `normal_a x z` and `normal_b x z` are the chart-`a` and chart-`b`
coordinates of the initial velocity of the same geodesic from `x` to `z`; prove
`normal_a x z = D(transition_{b→a})(x) (normal_b x z)` on a ball of radius uniform over the compact
`buffer a.1 ∩ buffer b.1`, by ODE uniqueness on the double cutoff-one zone (`chartTransitionState_*` gives the
transported curve solves the other chart's geodesic equation; `geodesic_eqOn_unitInterval` gives uniqueness on the
whole retained interval; the patch radii and compactness give uniformity), and then the frame law of
`patchFrame`/`linear` turns this into `linear_a s (normal_a x z) = linear_b s (normal_b x z)` (the alignment `L`
is intrinsic; the frames absorb the transition derivative — verify against the definitions in task 6 and
`FixedChartLocalSuccessorExistence.linear_metric`). (2) TARGET: the two sphere patch endpoints agree on the
resulting vectors by the same argument on `roundSphereMetric3` with the sphere charts. (3) Combine on a ball of
radius uniform over `x, p` in the compact buffer intersections and all `L`, using the already proved uniform
common-source radius (`buffered_common_source`). Commit each step; if (1) resists, deliver the exact resisting
`def` (the uniform chart-transition naturality of the patch normals) with `target_of_<resisting>`.
