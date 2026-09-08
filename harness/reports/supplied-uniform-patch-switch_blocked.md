# Supplied uniform patch switch: verified partial, blocked

Date: 2026-09-08. Branch: `worker/supplied-uniform-patch-switch`.
Frozen base: `ee68a96b187588a2818af0f2a846ba1e10a3a7d9`. Verified proof head: `2b1a2718e1048d0cb8573a92fef2ee901124bf74`.

Three of the four frozen targets are proved at their exact signatures:
`buffered_eventuallyEq`, `mesh_pos`, and `transition_eqOn`.
`exists_switchControl` remains absent. This is a worker partial result,
not acceptance or integration of task 12.

Exactly one new Lean file was added:
`Poincare/Global/CartanSuppliedUniformPatchSwitch.lean`, importing task 11.
No existing Lean file, root import, audit wiring, task file, or `HANDOFF.md`
was changed. The narrower worker contract forbids those edits; this report
serves as the handoff. Initial status was clean, and the worktree list and
HEAD identified the frozen base above. The prerequisite cover's olean was
already present.

## Checked mathematical progress

H1 gives `buffered_common_source`: `B.step` is a common source radius for
all buffered label pairs and all states. Source containment is therefore
already uniform, independently of the missing equality estimate.

`buffered_eventuallyEq` compares each supplied map with the generic map.
`exists_state_switch_radius` takes a finite minimum after fixing a state.
The stronger `buffered_eventuallyEq_generic_forall_alignment` compares the
framed source normal and inverse target normal with their generic versions,
then uses the fixed-anchor tangent-alignment operator bound. This makes the
inverse-normal input small on one neighborhood for every alignment. A finite
minimum over label pairs then proves the following stronger local result:

```lean
theorem exists_fixed_anchor_switch_radius (B : QuantitativeCover g)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ (a b : B.Label) (L : CartanMap.TangentAlignment g x p),
      B.Buffered a ⟨x, p, L⟩ → B.Buffered b ⟨x, p, L⟩ →
      ball x ρ ⊆ (germ (B.interp a) ⟨x, p, L⟩).source ∩
        (germ (B.interp b) ⟨x, p, L⟩).source ∧
      EqOn (map (B.interp a) ⟨x, p, L⟩) (map (B.interp b) ⟨x, p, L⟩)
        (ball x ρ)
```

The radius precedes all labels and alignments, but follows `x` and `p`.
All source memberships are retained. No equality of total extensions or
whole patch intersections is asserted.

`four_mul_mesh_le` proves that `4 * S.mesh` fits inside all four control
radii. The exact `transition_eqOn` uses core-to-buffer inclusion, retention
of both successor anchors in the old buffers, H2 in the old interpretation,
and `S.switch.agreement` at the actual successor. Its use of `System` is
exactly the frozen signature. No recognition theorem or global path
independence is used.

## One remaining statement

The remaining proposition is explicitly defined in the new file:

```lean
def UniformBufferedPairAgreement (B : QuantitativeCover g) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ a b : B.Label, ∃ ρ > (0 : ℝ),
    ∀ x ∈ B.source.buffer a.1 ∩ B.source.buffer b.1,
    ∀ p ∈ B.target.buffer a.2 ∩ B.target.buffer b.2,
    ∀ L : CartanMap.TangentAlignment g x p,
      EqOn (map (B.interp a) ⟨x, p, L⟩) (map (B.interp b) ⟨x, p, L⟩) (ball x ρ)
```

The missing producer is exactly:

```lean
HasConstantSectionalCurvature3 g 1 →
  ∀ B : QuantitativeCover g, UniformBufferedPairAgreement B
```

`exists_switchControl_of_uniformBufferedPairAgreement` derives
`Nonempty (SwitchControl B)` from this proposition. It chooses a finite
positive lower bound of the pair radii and intersects it with `B.step`.
The common-source part follows from the separately proved H1 consequence.
The conditional theorem does not assert the curvature-only target and does
not add a premise to final recognition.

The original resisting `SwitchControl.agreement` payload is unchanged:

```lean
letI : MetricSpace M := g.toMetricSpace
∀ (a b : B.Label) (s : CartanChain.ChainState g),
  B.Buffered a s → B.Buffered b s →
  ball s.anchor radius ⊆ (germ (B.interp a) s).source ∩
    (germ (B.interp b) s).source ∧
  EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor radius)
```

The buffer intersections are compact. That fact and
`∀ x p, ∃ ρ > 0, ...` do not justify `∃ ρ > 0, ∀ x p, ...`.
The retained S15 proof compares a fixed host to `chartAt E x` at each
individual anchor. Its preferred trajectory package, overlap neighborhood,
and inverse comparison are selected after the anchor. The proof above
removes dependence on alignment but supplies no persistence neighborhood
as the anchors vary.

The routes examined were S2/S15 germ transfer, H1 source bounds, H2
successor comparison, and finite compact minima. H2 compares one
interpretation with its own successor; it does not directly compare two
fixed hosts at a common moving state. A finite minimum can combine label
pairs once a uniform pair radius is proved. It cannot combine the
infinitely many fixed-anchor radii. A new joint fixed-host normal/flow
comparison on compact overlaps is still needed. This report does not claim
that the target is false.

## Commands and actual output

Every theorem was compiled before its separate commit. The successful
per-lemma direct Lean logs are `01-local.log`, `02-source.log`,
`03-state-retry.log`, `04-mesh.log`, `05-bounds.log`, `06-transition.log`,
`07-alignment-retry.log`, `08-fixed-anchors.log`, and `09-remainder.log`.
Every one has exit 0 and no output. They ran the exact command:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
```

The focused build command was:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedUniformPatchSwitch
```

Exit 0. Actual final output:

```text
✔ [3619/3619] Built Poincare.Global.CartanSuppliedUniformPatchSwitch (4.9s)
Build completed successfully (3619 jobs).
```

The full `build.log` preserves replayed dependency warnings. The new
module produced no warning. No overlapping full builds or root integration
audits were launched.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
git diff --check
git diff ee68a96b187588a2818af0f2a846ba1e10a3a7d9 --check
```

The scan returned exit 1 with no matches. Both diff checks returned exit 0
with no output.

`signatures.lean` copies all four signatures from plan 3. Three `example`
proofs apply the corresponding new declarations; the unproved fourth
signature is elaborated only as a proposition definition.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-uniform-patch-switch-evidence/signatures.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-uniform-patch-switch-evidence/axioms.lean
```

Both exit 0. Signature output is empty. Actual axiom output:

```text
'Poincare.CartanSuppliedUniformPatchSwitch.buffered_eventuallyEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.buffered_common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.exists_state_switch_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.mesh_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.four_mul_mesh_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.transition_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.buffered_eventuallyEq_generic_forall_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.exists_fixed_anchor_switch_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUniformPatchSwitch.exists_switchControl_of_uniformBufferedPairAgreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All nine theorem closures are exactly `[propext, Classical.choice, Quot.sound]`.

The exact missing-name probe was also run:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-uniform-patch-switch-evidence/missing-target.lean
```

Exit 1, as expected:

```text
/tmp/supplied-uniform-patch-switch-evidence/missing-target.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.CartanSuppliedUniformPatchSwitch.exists_switchControl`
```

The diagnostic `remaining-goal.lean` introduces the curvature hypothesis,
both compact buffer intersections, and the strongest checked local theorem,
then leaves the uniform pair goal open. This is an unclosed-goal probe, not
a proof. Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-uniform-patch-switch-evidence/remaining-goal.lean
```

Exit 1, with exactly the following remaining goal and context:

```text
/tmp/supplied-uniform-patch-switch-evidence/remaining-goal.lean:17:38: error: unsolved goals
M : Type u
inst✝⁴ : TopologicalSpace M
inst : ChartedSpace E M
inst✝³ : IsManifold I ∞ M
inst✝² : T2Space M
inst✝¹ : CompactSpace M
inst✝ : ConnectedSpace M
g : ClosedSmoothRiemannianMetric 3 M
hcurv : HasConstantSectionalCurvature3 g 1
B : QuantitativeCover g
this : MetricSpace M := g.toMetricSpace
a b : B.Label
hsourceCompact : IsCompact (B.source.buffer a.1 ∩ B.source.buffer b.1)
htargetCompact : IsCompact (B.target.buffer a.2 ∩ B.target.buffer b.2)
hlocal :
  ∀ (x : M) (p : RoundSphere3),
    ∃ ρ > 0,
      ∀ (a b : B.Label) (L : CartanMap.TangentAlignment g x p),
        B.Buffered a { anchor := x, target := p, alignment := L } →
          B.Buffered b { anchor := x, target := p, alignment := L } →
            ball x ρ ⊆
                (germ (B.interp a) { anchor := x, target := p, alignment := L }).source ∩
                  (germ (B.interp b) { anchor := x, target := p, alignment := L }).source ∧
              EqOn (CartanSuppliedDifferentialSuccessor.map (B.interp a) { anchor := x, target := p, alignment := L })
                (CartanSuppliedDifferentialSuccessor.map (B.interp b) { anchor := x, target := p, alignment := L })
                (ball x ρ)
⊢ ∃ ρ > 0,
    ∀ x ∈ B.source.buffer a.1 ∩ B.source.buffer b.1,
      ∀ p ∈ B.target.buffer a.2 ∩ B.target.buffer b.2,
        ∀ (L : CartanMap.TangentAlignment g x p),
          EqOn (CartanSuppliedDifferentialSuccessor.map (B.interp a) { anchor := x, target := p, alignment := L })
            (CartanSuppliedDifferentialSuccessor.map (B.interp b) { anchor := x, target := p, alignment := L })
            (ball x ρ)
```

## Compiler retries and evidence

The first finite-label attempt required an explicit `Fintype B.Label`
instance and a direct subset application in place of `heq.mono`.
Its exit-1 output is preserved:

```text
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:87:20: error(lean.invalidField): Invalid field `mono`: The environment does not contain `Function.mono`, so it is not possible to project the field `mono` from an expression
  heq
of type
  ?m.453 ∈ ball s.anchor r →
    ?m.453 ∈
      {x |
        (fun x =>
            CartanSuppliedDifferentialSuccessor.map (B.interp c.1) s x =
              CartanSuppliedDifferentialSuccessor.map (B.interp c.2) s x)
          x}
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:91:25: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Fintype (B.Label × B.Label)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:91:9: error: Tactic `rcases` failed: `x✝ : ?m.497` is not an inductive datatype
```

The first alignment-uniform attempt needed the local `Nsource` abbreviation
unfolded for the zero law and `Tendsto.eventually` to expose the preimage
predicate. Its exit-1 output is preserved:

```text
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:210:4: error: Type mismatch: After simplification, term
  ContinuousAt.tendsto
    (OpenPartialHomeomorph.continuousAt Nsource ((CartanSourceExponential.genericFamily g).anchor_mem_source x))
 has type
  Tendsto (↑Nsource) (𝓝 x) (𝓝 (↑Nsource x))
but is expected to have type
  Tendsto (↑Nsource) (𝓝 x) (𝓝 0)
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:214:4: error: Type mismatch: After simplification, term
  hnormal (ball_mem_nhds 0 (div_pos hδ hR))
 has type
  ball 0 (δ / R) ∈ Filter.map (↑Nsource) (𝓝 x)
but is expected to have type
  ∀ᶠ (z : M) in 𝓝 x, ‖↑Nsource z‖ < δ / R
```

All logs, probe sources, intermediate snippets, and `proof.diff` are under
`/tmp/supplied-uniform-patch-switch-evidence`. The final proof diff is also
durable in the commit range `ee68a96b187588a2818af0f2a846ba1e10a3a7d9..2b1a2718e1048d0cb8573a92fef2ee901124bf74`.

One theorem per verified commit:

```text
b232e721 Prove buffered supplied patch germ agreement
d93b7778 Prove uniform common sources for buffered patch pairs
8d56ce6d Prove one switch radius for all labels at each fixed state
b598fd31 Prove supplied patch switch 04-mesh
d95b25ed Prove supplied patch switch 05-bounds
0eb3a3fc Prove supplied patch switch 06-transition
4fcba6ec Make fixed-anchor patch germ comparison uniform over alignments
7dc13fbe Prove supplied switch 08-fixed-anchors
2b1a2718 Prove supplied switch 09-remainder
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
```

The next proof task is to establish `UniformBufferedPairAgreement` from
curvature at this proof head, preserving its radius-before-anchors order.
Review and integration remain with the orchestrator.
