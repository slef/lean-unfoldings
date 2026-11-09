# Unfoldings

A Lean library for polyhedral metrics, cuts, and planar developments, with source
unfolding of convex polyhedra as its first major target. Overlapping developments
are supported; nonoverlap is a separate property and permits boundary contacts.

The design and feature checklist are in [PLAN.md](PLAN.md). The source-unfolding
construction and the sphere/disk cut-graph characterizations remain future work.
The initial library has no placeholder propositions or unfinished proofs.

## Current interfaces

- `Route.distance` constructs extended distance from finite routes. It satisfies
  the metric inequalities and is maximal among pseudometrics bounded by the
  allowed step costs.
- `MetricGluing.Realization` glues a family of metric cells using that distance.
  Compatible nonexpanding maps descend uniquely. Removing seams cannot shorten
  distance. Disconnected cells can remain infinitely far apart.
- `MetricGluing.SeamQuotient` identifies exactly finite chains of declared seams.
  It maps continuously and surjectively to the metric realization. `Exact`
  states that this map is injective; compatible nonexpanding coordinates can
  certify it. For finite compact cells the metric realization is compact and
  complete, and exactness gives a homeomorphism with the seam quotient.
- `TriangleComplex` describes finitely many nondegenerate Euclidean triangles
  and whole-edge isometric equivalences, with each edge in at most one pair.
  Its metric realization depends on an explicit set of retained seams.
  `BoundaryBank` labels the unpaired local edges. Cutting a seam gives two
  distinct bank labels; restoring it identifies their metric images pointwise.
  With every seam cut, exactness and isometric face maps are proved.
- `FacewiseDevelopment` places each original triangle exactly once, agrees on
  retained edges, and puts the incident triangles on opposite sides. Retained
  dual cycles are allowed. The map descends to the cut realization and is
  nonexpanding, even with global overlap.
- `FacewiseDevelopment.Nonoverlapping` means disjoint face interiors and is
  equivalent to multiplicity at most one. Linear separators checked on corners
  certify whole-cell nonoverlap.
- `injective_of_radial_paths` proves injectivity of a locally injective map
  when paths from one fixed source develop to radial segments. This isolates
  the eventual source-unfolding argument without assuming shortest-path or
  cut-locus existence.

The facewise interface enforces local opening at edges. Unbranched local
isometry at uncut vertices will be part of the later surface-development layer,
after vertex links and surface interiors are constructed.

For arbitrary gluing data the separation quotient may identify more points than
the generated seam equivalence; a checked example demonstrates this. Finite
triangle complexes already have compact, complete metric realizations.
Exactness for these complexes remains to be proved; it will also identify their
metric and cell-quotient topologies. Face maps are unconditionally nonexpanding;
the existence of a consistent rigid development strengthens them to isometries.

## Module map

| Module | Purpose |
| --- | --- |
| `Unfoldings.Metric.Route` | Finite routes and the generated extended pseudometric |
| `Unfoldings.Metric.Gluing` | Metric quotient, descent, and restoration of seams |
| `Unfoldings.Metric.Quotient` | Declared seam classes, exactness, compactness, and completeness |
| `Unfoldings.Metric.Unglued` | Exact metric formulas and separation with no seams |
| `Unfoldings.Geometry.Triangle` | Nondegenerate cells and full edge subspaces |
| `Unfoldings.Complex` | Finite edge-paired complexes and their cut realizations |
| `Unfoldings.Boundary` | Boundary-edge labels, bank maps, and restoration of banks |
| `Unfoldings.Development` | Facewise placements, nonoverlap, multiplicity, and metric descent |
| `Unfoldings.Geometry.Separation` | Corner certificates for whole-cell separation |
| `Unfoldings.Geometry.Hinge` | Opposite sides imply adjacent-cell nonoverlap |
| `Unfoldings.Source.Radial` | Injectivity from uniqueness of radial lifts |
| `Unfoldings.Examples.*` | Recovery, disconnectedness, shortcuts, contact, and overlap |
| `Audit` | Transitive axiom check for all imported library declarations |

Embedded-graph and cellulation theory is planned separately under
`Unfoldings/Topology/`, with no dependency on unfolding geometry, for possible
upstreaming to Mathlib.

## Build and proof audit

The project pins Lean and Mathlib **4.35.0**. Install the toolchain through elan,
then fetch Mathlib artifacts before building:

```sh
lake exe cache get
lake build
```

`lake build` checks both the library (including its examples) and `Audit`. The
audit rejects any dependency other than `propext`, `Classical.choice`, and
`Quot.sound`; in particular, it rejects `sorryAx` and native-decision axioms.

On a machine with limited disk space, fetch only the needed import closures:

```sh
lake exe cache get Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Analysis.Convex.Topology \
  Mathlib.Analysis.Normed.Affine.AddTorsorBases \
  Mathlib.Analysis.Normed.Affine.Isometry \
  Mathlib.Analysis.Normed.Operator.Banach \
  Mathlib.Topology.EMetricSpace.Lipschitz \
  Mathlib.Logic.Relation Mathlib.Topology.Separation.Hausdorff \
  Mathlib.Topology.UniformSpace.Cauchy \
  Mathlib.Topology.IsLocalHomeomorph \
  Mathlib.Topology.Instances.Real.Lemmas \
  Mathlib.Tactic.FinCases Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith
lake build
```

To skip Mathlib's automatic full-cache hook when updating dependencies, use
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`, followed by the selected cache fetch.

## Provenance

The earlier scaffold is preserved in Git history. Its classification target and
assumed global gluing metric were replaced by the constructed route metric.
The design also uses ideas from
[slef/EdgeUnfoldings](https://github.com/slef/EdgeUnfoldings/tree/56caca8cdc44dbc2f839e93808088d56ea3f0780/lean_statement),
particularly whole-face separation certificates and transitive axiom auditing.
No six-vertex classification theorem is a dependency of this library.
