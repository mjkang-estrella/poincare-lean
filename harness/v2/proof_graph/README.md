# Theorem registry pilot

The registry reads Lean's compiled environment after a focused build. It
exports each selected declaration's exact expression, displayed type, binders,
documentation, defining module, direct statement references, direct proof
references, and transitive foundational dependencies. Planned mission edges
remain separate from references extracted from checked proof terms.

Create a catalog for one module and search its mathematical documentation,
types, names, and statement dependencies:

```sh
python3 scripts/theorem_registry.py snapshot \
  --module Poincare.ProofProgress.GroundedPerelmanPoincareBoundary \
  --output harness/v2/state/grounded-boundary-catalog.json
python3 scripts/theorem_registry.py search \
  harness/v2/state/grounded-boundary-catalog.json 'finite extinction'
```

Repeated `--module` flags select more modules. `--name` includes specific
declarations from their imported dependency closure. Catalogs refuse overwrite
and record the commit, local Lean source hashes, toolchain, dependency
revisions, and exporter identity. Search rejects stale or altered artifacts.
A catalog cannot certify a mission, even if somebody edits its digest.
The local pilot requires dependency packages with clean Git checkouts. It
rejects modified tracked files and untracked Lean or configuration inputs.
Published package caches without Git metadata need a separate provenance
adapter before they can use this command.

A mission uses the following format. Root orchestration owns the mission and
reviews its mathematical wording and statement pins before dispatching work.

```json
{
  "schema_version": 1,
  "id": "grounded-topology",
  "modules": ["Poincare.ProofProgress.GroundedPerelmanPoincareBoundary"],
  "endpoint": {
    "name": "Poincare.poincare_conjecture",
    "type_symbol": "Poincare.PoincareConjectureStatement"
  },
  "nodes": [{
    "id": "poincare",
    "kind": "obligation",
    "declaration": "Poincare.poincare_conjecture",
    "description": "Every closed simply connected topological 3-manifold is homeomorphic to the 3-sphere.",
    "depends_on": [],
    "expected_type_symbol": "Poincare.PoincareConjectureStatement",
    "expected_statement_sha256": "REPLACE_WITH_REVIEWED_FINGERPRINT"
  }]
}
```

An obligation may have a null or omitted candidate `declaration` while it is
open. `expected_type_symbol` must denote a closed Lean proposition. A `checked`
node instead names a proved reduction and lists its planned prerequisites
using `depends_on`. An edge points from a consumer to its prerequisite.
Its hypotheses remain in the output. An optional mission `base_commit` must
be a full commit ID and an ancestor of the current checkout.
Mission and node `references` can record source URLs and precise theorem or
section identifiers. These are review metadata and confer no proof status.

Print proposed statement pins, review them, and copy them into the mission:

```sh
python3 scripts/theorem_registry.py fingerprint \
  --mission harness/v2/missions/grounded-topology.json
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
```

The fingerprint includes the exact expected definition and its transitive
statement dependencies, definition bodies, and inductive constructors. It
excludes bodies of proof declarations. Embedded proof terms in data
definitions remain part of their structural expressions. Renaming a binder,
moving a definition, changing Lean,
or changing a dependent definition can require a new reviewed pin. This is a
conservative structural check, not a claim that equal mathematical meanings
always have the same hash.

Every graph run builds the selected modules and extracts fresh Lean evidence.
An obligation closes only when Lean finds a proof whose complete type is
definitionally equal to its frozen proposition at the same universes, with
only the project's allowed foundational dependencies. Unsafe and partial
declarations cannot discharge obligations. A theorem of type
`Goal -> Goal` does not discharge `Goal`. JSON status flags are rejected.
Cycles, dangling planned edges, missing checked declarations, and changed
statement pins also fail. Exit code 2 from `--require-closed` means valid
evidence with open obligations, while exit code 1 means invalid input or a
failed check.

`endpoint_verified` reports only the named endpoint's exact proof check.
`project_complete` remains false because this tool does not run the clean
integration checkout's full completion audit. Graph reachability, conditional
theorem counts, and successful imports cannot substitute for that audit.

The pilot uses a lexical search index with mathematical documentation. It
does not generate descriptions, rank mathematical importance, authenticate
reviewers, or dispatch Jobs. A trusted operator must review mission edits and
run this CLI from trusted source. Snapshotting and graph checks run focused
Lake builds, so serialize them with other build-producing integration work.

Run its isolated Lean regression suite with:

```sh
python3 -m unittest discover -s scripts/tests -p test_theorem_registry.py -v
LEAN_NUM_THREADS=1 lake env lean scripts/lean/TheoremRegistry.lean
```
