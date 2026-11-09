# Unfolding library plan

The first major target is the source unfolding of a convex polyhedral sphere.
The library will also represent overlapping developments, surfaces with boundary,
and arbitrary conforming triangulations. Small complete theorems should exercise
the definitions before the source-unfolding construction depends on them.

Checkboxes mean implemented and checked by Lean, not merely stated. Future
theorems live in this checklist until their proofs exist; the public library
must not contain `sorry`, `admit`, extra axioms, or predicates defined as `True`.

## Mathematical interfaces

1. **Triangle complex.** Finitely many nondegenerate closed Euclidean triangles
   with specified full-edge isometric identifications. This is initially a
   complex, not automatically a manifold. Boundary, orientability and vertex-link
   conditions are additional properties. Self-identifications and flat
   subdivision vertices must not be silently excluded.
2. **Metric realization.** Construct distance from finite routes within cells
   and across declared seams. Use extended distances for disconnected spaces.
   Face maps are nonexpanding in general. Local or global isometry requires a
   theorem with appropriate hypotheses. The separation quotient exists for
   arbitrary gluing data; showing that it makes exactly the intended
   identifications is a separate theorem for finite triangle complexes.
3. **Cut surface.** Retain a subset of the seams and reconstruct distance.
   Boundary banks and vertex copies remain distinct unless the retained
   identifications connect them. The metric is not the restriction of the old
   surface metric, and the surface is not just the complement of the cut set.
4. **Development.** `FacewiseDevelopment` places every face exactly once by a planar rigid motion,
   agreeing on retained seams and placing incident faces on opposite sides.
   The retained dual graph may have cycles around flat vertices. Nonoverlap is
   a separate predicate; global injectivity, especially on the boundary, is a
   stronger property and must not be required of every development. A later
   surface-development interface must additionally ensure unbranched local
   isometry at all interior vertices. Edge opening alone does not exclude a
   branched vertex with total angle an integer multiple of a full turn.
5. **Embedded convex surface.** A finite convex hull with nonempty spatial
   interior, its maximal facets, and an independent input triangulation. Its
   ambient chord metric, intrinsic surface metric, and cut metric are distinct.
6. **Source unfolding.** Construct shortest paths, cut locus, a flat cut disk,
   and its development. Prove injectivity on retained interiors by uniqueness of
   radial lifts. Obtain the usual nonoverlap conclusion and describe boundary
   copies and contacts separately.

The words *face*, *maximal facet*, *input edge*, *subdivision edge*, *primal cut
graph*, and *retained dual graph* must remain distinct in definitions and theorem
statements. Refinement may introduce edges; an original-edge theorem must say
which edges were used.

## Phase 0 Toolchain and proof discipline

- [x] Pin a supported stable Lean and Mathlib release and record the inspected
  upstream infrastructure.
- [x] Replace the old placeholder scaffold; retain its history in Git.
- [x] Use explicit imports and a small public umbrella module.
- [x] Audit all library declarations for proof dependencies, allowing only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Build examples and the audit in the default Lake target.
- [x] Record exact commands and the current checked boundary in README/LOG.

## Phase 1 Constructed route distance

- [x] Finite routes with length, concatenation and reversal.
- [x] Extended path distance as the infimum of route lengths.
- [x] Self-distance, symmetry and triangle inequality.
- [x] Maximality among pseudometrics bounded by the allowed step costs.
- [x] Monotonicity under increasing step costs.
- [x] A family gluing construction using actual within-piece distances and
  zero-cost seam transitions, not a supplied global pseudometric.
- [x] Separation quotient and nonexpanding canonical face maps.
- [x] Compatible nonexpanding face maps descend uniquely.
- [x] Removing seams cannot decrease intrinsic distance.
- [x] Single-cell realization recovers its original metric.
- [x] Distinct disconnected cells have infinite distance.

## Phase 2 Triangles and the first development

- [x] Nondegenerate Euclidean triangles, closed carriers and planar interiors.
- [x] Full edge subspaces and isometric edge equivalences.
- [x] Finite triangle complexes with one pairing per edge.
- [ ] Boundary-edge and boundary-vertex API.
- [x] Route-metric realization with an explicit set of retained seams.
- [x] Canonical map forgetting cuts and its nonexpansion property.
- [x] Facewise developments, seam agreement, and strict opposite-side condition.
- [x] Developments descend to nonexpanding maps on the cut metric.
- [x] A consistent rigid development makes each face map isometric.
- [x] The opposite-side condition implies disjoint interiors at retained hinges.
- [x] Separate nonoverlap predicate and finite multiplicity.
- [x] Nonoverlap equivalent to multiplicity at most one.
- [x] Halfplane and finite-vertex separation certificates.
- [x] A two-triangle hinge has an outward, nonoverlapping development.
- [x] Examples distinguishing boundary contact from interior overlap.
- [ ] Example of a valid retained dual cycle around a flat subdivision vertex.

## Phase 3 Topology of the realization and cuts

### Embedded graphs and surface cellulations

This part is independent of unfolding and is a candidate for eventual Mathlib
upstreaming. Keep its definitions and proofs in `Unfoldings/Topology/` with
generic namespaces and imports that do not depend on triangles, developments,
convex polyhedra, or intrinsic metrics.

- [ ] Finite graphs with cyclic incidence orders (rotation systems), including
  loops and parallel edges where boundary contraction requires them.
- [ ] Distinguish abstract face walks from actual complementary regions.
- [ ] Combinatorial surface cellulations and their topological realizations.
- [ ] Planar/spherical embeddings and their compatibility with rotation data.
- [ ] Euler's formula `V - E + F = 2` for connected spherical embeddings and
  `V - E + F = 1 + c` for arbitrary nonempty finite spherical embeddings.
- [ ] Derive Euler's formula from the embedding/cellulation theory; do not use
  the formula itself as the definition of a topologically spherical surface.
- [ ] Primal/dual incidence, connectedness and complementary spanning trees.
- [ ] Tree complements, regular neighborhoods, and relative boundary versions.
- [ ] Separate any needed polygonal Jordan/separation theorem from graph
  counting; a rotation system alone is not a proved embedding in the sphere.
- [ ] Small examples covering isolated vertices, bridges, cycles, loops,
  parallel edges and disconnected graphs.

The first metric and development modules do not depend on this package. The
cut-graph disk equivalences and later cut-locus graph arguments will use it.

### Metric realizations and cuts

- [x] Quotient by finite seam chains with the original cell-quotient topology.
- [x] Continuous surjection from seam classes to the metric realization.
- [x] Exactness criterion using compatible nonexpanding separating coordinates.
- [x] Counterexample showing additional metric collapse for unrestricted gluing.
- [ ] Zero route distance identifies exactly the finite gluing equivalence.
- [x] Exactness implies agreement of quotient and metric topology for finite
  compact cells; apply after proving exactness for triangle complexes.
- [x] Compactness and completeness of finite closed complexes.
- [ ] Finite vertex classes, links, and manifold conditions.
- [ ] Local Euclidean disks at face and paired-edge interiors; half-disks at
  boundary-edge interiors.
- [ ] Cone/sector neighborhoods at cyclic/interval vertex links.
- [ ] Curvature is derived from the incident triangle angles.
- [ ] A nonempty embedded edge cut graph on a sphere, with no isolated points,
  produces one disk iff it is a tree.
- [ ] Interior edge cuts on a disk, ignoring existing boundary edges, produce
  one disk iff they form a forest with exactly one original-boundary point per
  tree. The empty forest is allowed.
- [ ] Include all nonflat interior vertices in the cuts iff the resulting disk
  has flat interior. Boundary corners need not be flat.
- [ ] A flat metric disk admits a development, allowing overlap; uniqueness up
  to planar rigid motion after fixing the orientation convention.
- [ ] Do not generalize the disk/tree statement to layouts with holes.

## Phase 4 Subdivision and cone fans

- [ ] Elementary triangle subdivision induces a canonical metric isometry.
- [ ] Iterated conforming refinement preserves the metric and curvature.
- [ ] Facewise placements commute with refinement.
- [ ] Nonoverlap is unchanged by conforming subdivision.
- [ ] Finite fan developments with positive sector angles and real cumulative
  headings, not just angles modulo a full turn.
- [ ] A radially slit fan is nonoverlapping **iff** its total angle is at most
  `2 * Real.pi`.
- [ ] At equality the terminal banks may coincide; above a full turn there is
  interior overlap near the apex.
- [ ] Lateral pyramid unfolding and a complete convex-pyramid net as benchmarks.

## Phase 5 Embedded convex surfaces and shortest paths

- [ ] A minimal convex-polyhedron adapter, keeping maximal facets separate from
  its input triangulation.
- [ ] Continuous surface paths and length via Mathlib total variation.
- [ ] Path reversal, joining, restriction and constant-speed reparameterization.
- [ ] Shortest-path existence via compactness and lower semicontinuity.
- [ ] Intrinsic surface metric, correct topology, compactness and geodesics.
- [ ] Intrinsic distance on an embedded planar facet equals its Euclidean chord.
- [ ] Prove equivalence with the triangle route metric; this is the bridge
  between the embedded and abstract libraries.
- [ ] Shortest paths develop straight in flat charts and do not pass through
  positive-curvature vertices in their interiors.
- [ ] Local uniqueness and continuation of a geodesic with a given initial germ.

## Phase 6 Source unfolding

- [ ] A generic source in a regular face interior and normalized shortest routes.
- [ ] Source distance and the locus of nonunique shortest paths.
- [ ] Finite face-sequence descriptions and local Voronoi descriptions.
- [ ] Cut-locus closedness, finite embedded graph structure, and tree structure.
- [ ] Every nonflat vertex belongs to the cut locus.
- [ ] The completed slit surface is a flat disk with identified boundary copies.
- [ ] Existence of the source development and radial developed shortest paths.
- [x] Abstract injectivity criterion from existence and uniqueness of radial lifts.
- [ ] Apply that criterion to retained source-unfolding interiors.
- [ ] Boundary coverage, nonoverlap of every original face piece, and a precise
  source-unfolding theorem for every convex polyhedron.
- [ ] Treat nongeneric sources and exceptional route ties as a later extension.

The radial injectivity criterion is a useful early theorem in its own right.
It does not assert shortest-path or cut-locus existence and must not hide these
construction obligations in a structure field named `isSourceUnfolding`.

## Later targets and Fewest Nets

- [ ] Star unfolding after the source-unfolding theorem.
- [ ] Positive hinge openings and two-bank developments.
- [ ] Radially monotone polygonal histories and quantitative perturbation bounds.
- [ ] Complete one-ended forest cuts and intrinsic polygonal-gap insertion.
- [ ] Completeness for finite noncompact complexes with controlled ends.
- [ ] Local-isometry/covering arguments for completed flat planes.
- [ ] Original-edge restriction to a disk with one boundary root per tree.

These later features are motivated by Fewest Nets, but its normal partitions,
optimized progress bodies, and numerical certificates belong in a downstream
application rather than the unfolding core.

## Upstream research and reuse

As of 2026-11-08 the latest stable release is Lean/Mathlib **4.35.0**, with
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The newer source still
offers binary metric gluing, extended metric separation quotients, variation
and curve-length tools, covering-space theory, and basic polygons. It does not
supply the finite triangle path-metric/source-unfolding library needed here.
The Riemannian `PathELength` API is useful background but is not a substitute for
polyhedral cone metrics or cut surfaces.

Relevant prior work is slef/EdgeUnfoldings, branch `codex/lean-formalization`,
snapshot `56caca8cdc44dbc2f839e93808088d56ea3f0780`, especially:

- `Definitions.lean`: embedded convex polyhedra, maximal facets and successful
  edge nets. Its nonoverlap and retained-dual-tree requirements should be
  separate from our general development interface.
- `SurfacePaths`, `SurfaceDistance`, `IntrinsicSurfaceMetric`: continuous-path
  length and a compact geodesic intrinsic boundary metric.
- `HingePlacement`, `FaceChainDevelopment`, `TreeFrames`: rigid alignment,
  opposite-side development and consistent transport of coordinate frames.
- `PlacedFaces`, `Separation`, `VertexCertificate`: finite separation
  certificates with boundary contact allowed.
- `ConvexFiniteSelection`: piecewise nonexpansion on convex domains.
- `Audit.lean`: transitive proof-dependency checking.

Reuse should keep the generic statements independent of the six-vertex
classification and document adapted proofs. Its `UncutSurface` complement is
useful for interiors, but does not replace our completed cut metric. Its
single-valued folding-back helpers are local tools, not general models of
overlapping developments.
