# Proof selection and statement review

The workflow keeps three facts separate: Lean has checked a declaration, a
reviewer has checked what its statement means, and a selected mathematical
obligation has been discharged. None of these follows from a theorem count.

## Topology pilot

`GroundedTopologyStatements.lean` defines the stable source and obligation
types. `GroundedTopologyAssembly.lean` proves consequences of those sources
and the conditional assembly to `PoincareConjectureStatement`.

A source retains one component decomposition and surgery trace, the package
which owns their analytic foundation and surgery construction, and a Perelman
production source indexed by that package's flow. The new covering consumer
takes this complete source. The legacy extinction predicate remains available
for compatibility and as an index used by the older trace API; it is not the
new consumer's only geometric input.

The universal source obligation allows a chosen compatible atlas over the same
topological space. It does not assert that every supplied topological atlas is
differentiable. An independent read-back caught that stronger, unjustified
requirement in the first draft before acceptance.

The recorded component sets live in the original manifold. The partition
theorems concern those sets at each recorded stage, including the terminal
stage. They do not assert that an evolving physical manifold stays nonempty
after extinction. The inherited trace requires a nonempty event prefix; a
zero-event treatment is not supplied by this pilot.

The component payload does not yet give the carrier maps the topology,
continuity, injectivity, or spherical recognition data required for the full
geometric argument. Sharing a flow index also does not identify event regions
with high-curvature regions. Source existence and construction of the spherical
covering therefore remain separate open obligations. The conditional assembly
is not a proof of either one.

Background references are Perelman's [surgery paper](https://arxiv.org/abs/math/0303109),
his [finite extinction paper](https://arxiv.org/abs/math/0307245), and
[Morgan and Tian's exposition](https://arxiv.org/abs/math/0607607). These identify
the intended mathematical route. They are not attestations that the current
Lean source records are equivalent to the corresponding geometric definitions.

## Selecting the next proof

The mission in `harness/v2/missions/grounded-topology.json` records the selected
route. Its planned dependencies explain the work still needed. The registry's
dependencies come from Lean expressions and describe what checked declarations
actually use. Do not interchange those two relations.

Before freezing a Task, inspect its open obligation, exact expected statement,
definition dependencies, and intended consumer. Search the theorem catalog for
an existing proof or useful lemma. A checked conditional theorem does not close
the obligations represented by its inputs. Changing a statement's definition
requires a new reviewed fingerprint, not a status update.

Useful progress measures are reviewed obligations discharged, concrete inputs
preserved through consumers, and successful use of a new result on the selected
route. The number of graph nodes can increase during a sound decomposition;
there is no reliable completion percentage based on node counts.

Run the reviewed graph and create a source-bound searchable catalog:

```sh
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
python3 scripts/theorem_registry.py snapshot \
  --module Poincare.ProofProgress.GroundedTopologyAssembly \
  --output harness/v2/state/catalogs/grounded-topology.json
python3 scripts/theorem_registry.py search \
  harness/v2/state/catalogs/grounded-topology.json 'component cover'
```

The graph exits `2` when valid evidence leaves obligations open, `1` on invalid
input or failed checks, and `0` when the requested check succeeds. A snapshot is
append-only: choose a new filename to refresh it. Search rejects a snapshot
whose source identity has changed. These commands build only the selected
modules before reading Lean's environment; serialize them with other builds.
The pilot expects clean Git-backed dependency packages. It does not operate on
the worker sandbox's stripped cache as though that were a source checkout.

The Poincare mission also loads the root module so an endpoint defined outside
the pilot modules can be found. Its graph check therefore builds the root;
ordinary theorem catalog snapshots can still use one narrow module.

`fingerprint --mission <path>` prints proposed statement fingerprints. Review
the intended statement and its dependent definitions before updating a pin.
No JSON status flag can replace a checked proof.

## Frozen contracts and independent read-back

New proof Tasks use schema version `2.1`. Every required declaration has an
exact Lean type and explicit universe parameters. Definition files and the
review report are pinned by SHA-256. The review binds to the entire statement
snapshot, not just a theorem name.

Pin statement and definition modules, not a proof-only implementation module.
Proof bodies may change while their expected types stay fixed. The pilot
therefore freezes `GroundedTopologyStatements.lean` and its core definitions;
the separate assembly proofs are checked against the recorded types.

The statement author and read-back reviewer must be distinct. Give the reviewer
the Lean statements and dependent definitions without the intended source
wording. The reviewer writes the literal mathematical assertion, including
implicit parameters and limitations. The orchestrator compares that result
with the intended milestone, resolves discrepancies, and records the reviewed
snapshot before dispatch. A changed statement or definition invalidates that
review. A report establishes review provenance; it does not replace mathematical
judgment or kernel checking.

Pinned definition files are hash-checked separately from prompt context. Only
the selected context files and review report enter the prompt. This matters
for the existing multi-megabyte source modules: freezing their bytes does not
increase the worker's read scope or bypass its existing context-size limits.

Historical version `2.0` Tasks retain their original contract. The migration
does not rewrite completed jobs. The orchestrator prompt requires `2.1` for
new proof tasks.

`scripts/theorem_contract_audit.sh` checks registered statement contracts and
allowed axiom footprints. It no longer requires every theorem to have a
reflexive companion named `theorem_eq`. Existing equality lemmas remain valid
APIs. A statement contract must fail if a deliverable's expected type changes,
including a secondary deliverable. Registered contracts are a curated review
boundary, not proof that every mathematical definition in the repository is
correct.

The separate legacy shape audit retains its naming convention for unqualified
definitions. It does not misread a qualified constructor such as
`Type.ofSource` as a new definition of `Type`. Qualified definitions need actual
type contracts where they form a reviewed interface; a companion name for the
owning type never established their correctness.

## Compilation pilot

Build the two pilot modules before measuring focused elaboration. Then run:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.ProofProgress.GroundedTopologyAssembly
python3 scripts/benchmark_statement_pilot.py \
  --statements Poincare/ProofProgress/GroundedTopologyStatements.lean \
  --proofs Poincare/ProofProgress/GroundedTopologyAssembly.lean \
  --repeat 2 \
  --output harness/v2/state/benchmarks/grounded-topology.json
```

The benchmark retains commands, exit codes, raw compiler output, and elapsed
times. These are warm-cache checks of different modules, not a before/after
speedup measurement. The structural benefit is that statements do not import
their proof implementation. Keep the full integration build and audit at the
integration checkpoint. Do not introduce unresolved theorem stubs into trusted
Lean sources to obtain a faster local check.

The exact project endpoint is still the authority for completion. Even a graph
with no pending planned dependencies needs the reserved declaration, its
expected type, the allowed axiom footprint, and the full completion audit at
one clean commit.
