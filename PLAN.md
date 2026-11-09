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
   complex, with metric manifold neighborhoods to be constructed. Its vertex
   links now have derived cyclic/interval orders; orientability remains a
   separate global property. Self-identifications and flat subdivision vertices
   must not be silently excluded.
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
- [x] With no seams, the full family metric is exactly within-cell distance or
  infinity across distinct cells; separated cells give an exact quotient.

## Phase 2 Triangles and the first development

- [x] Nondegenerate Euclidean triangles, closed carriers and planar interiors.
- [x] Full edge subspaces and isometric edge equivalences.
- [x] Finite triangle complexes with one pairing per edge.
- [x] Boundary edges, distinct bank labels, nonexpanding bank maps, and
  pointwise bank identification when restoring a seam.
- [x] Boundary-vertex classes and their incidence with boundary banks.
- [x] Route-metric realization with an explicit set of retained seams.
- [x] Canonical map forgetting cuts and its nonexpansion property.
- [x] Facewise developments, seam agreement, and strict opposite-side condition.
- [x] Developments descend to nonexpanding maps on the cut metric.
- [x] A consistent rigid development makes each face map isometric.
- [x] The opposite-side condition implies disjoint interiors at retained hinges.
- [x] Extend any closed-edge isometry to a planar rigid motion; construct an
  outward hinge placement and a nonoverlapping development for every two-triangle hinge.
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
- [x] Capped distance barriers and exactness for finitely many closed isometric
  seams whose equivalence classes are finite in each cell.
- [x] Exactness for triangle complexes with all seams cut.
- [x] Zero route distance identifies exactly the finite gluing equivalence,
  for every retained-seam set, with self-pairings and corner identifications allowed.
- [x] Agreement of quotient and metric topology for every finite triangle complex.
- [x] Compactness and completeness of finite closed complexes.
- [x] Route distance equals the infimum of lengths of continuous paths on every
  cut triangle realization; every finite distance is attained by a metric geodesic.
- [x] Retained-face connectivity implies finite distances, an ordinary intrinsic
  metric preserving edistance/topology, and geodesics between all points.
- [x] Finite corner-quotient vertex types, injective metric images, boundary-bank
  endpoint incidence and surjective vertex-copy maps when restoring seams.
- [x] Actual positive corner angles, triangle angle sums, total vertex angles,
  and conservation of total angles across cut copies.
- [x] Endpoint permutations, corner edge germs, and the within-corner and
  retained-seam involutions, preserving self-pairings.
- [x] Germ components equal the actual retained vertex classes.
- [x] Construct cyclic/interval link orders, listing each corner once; boundary
  links have exactly two unpaired germs. Generic finite-involution proofs are
  independent of triangle geometry and metric realizations.
- [x] Ordered corner angles sum to the actual total vertex angle.
- [x] Local metric excision: keeping the incident seams preserves a whole small
  intrinsic ball, via the canonical map restoring distant cuts.
- [x] Vertex-star seam systems preserve the central class, unique central vertex
  copy and total angle, and have the same small intrinsic ball.
- [x] Supporting corner wedges, positive opposite-edge clearance, radial
  invariance and wedge-ball/cell-ball isometries.
- [x] Spatial foldings give one class representative per original cell and
  injective face labels among the incident corner copies.
- [x] Construct tangent metric fans from the actual corner wedges. Index cells
  by `CornerAt`; index radial seams by retained seam, direction and endpoint.
  Glue nonnegative radial extensions of the original paired edge points.
- [x] Identify all tangent apices using link connectivity. Lift compatible
  distances to the apices and prove exact radial distance; derive an ordinary
  metric and compact closed balls, hence properness and completeness.
- [x] Tangent route distance equals continuous-path intrinsic distance;
  explicit radial paths are genuine constant-speed geodesics.
- [x] Spatial foldings extend to the tangent model and imply cone-cell isometry
  when supplied.
  - [x] Tangent folding preserves every apex distance and is proper for all
    retained-seam sets. An embedded original surface gives a closed spatial
    embedding of every actual uncut tangent fan, proved by positive dilation
    into the constructed exact local neighborhood and back.
- [x] For spatial foldings, compare whole small tangent and original vertex
  balls. A uniform wedge/triangle radius, exact radial distances and local
  route bounds in both directions construct an isometry agreeing with every
  incident face coordinate. All sufficiently near original representatives
  have incident face labels, giving whole-ball surjectivity.
- [ ] Extend the local tangent comparison to abstract complexes without a
  supplied spatial folding, including possible same-face corner copies.
- [x] Construct radial dilations for every nonnegative scale, prove exact
  intrinsic distance scaling, and reciprocal homeomorphisms at positive scales.
  This construction does not require a spatial folding.
- [ ] Establish flat-vertex charts and angular metric cone/sector neighborhoods,
  including self-pairings.
  - [x] A cyclic actual tangent fan at total angle two pi is isometric to the
    whole Euclidean plane, without a spatial-folding hypothesis.
  - [x] Flat interior vertices of spatially folded complexes have constructed
    whole Euclidean ball charts in the original intrinsic metric, agreeing
    with every incident face coordinate.
- [x] Constructed isometries between Euclidean disks and intrinsic open balls
  at every face-interior point, without a global development hypothesis.
- [x] Barycentric affine coordinates and local supporting half-plane geometry
  at nonvertex triangle-edge points.
- [x] Constructed isometries from Euclidean half-disks onto intrinsic open balls
  at every nonvertex point of an unpaired boundary bank.
- [x] Outward hinge triangles intersect exactly in their seam and cover an
  edge-interior planar neighborhood; local chords give intrinsic upper bounds.
- [x] Quantitative class barriers and short-route localization for local metric
  lower bounds without a global development premise.
- [x] Local Euclidean disks at paired-edge interiors with distinct incident faces,
  agreeing with both original face maps in outward hinge coordinates.
- [ ] Paired-edge charts for self-pairings inside one original face.
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

- [x] Piecewise nonexpansion on convex sets from finite closed covers, using
  local center bounds and continuous induction along segments. This supports
  metric refinement, facet chords and flat-fan inverse maps. Continuity is
  derived; pieces need no global extensions and need not themselves be convex.
- [ ] Elementary triangle subdivision induces a canonical metric isometry.
- [ ] Iterated conforming refinement preserves the metric and curvature.
- [ ] Facewise placements commute with refinement.
- [ ] Nonoverlap is unchanged by conforming subdivision.
- [x] Polar developments keep real headings. The open positive-radius strip
  is injective iff its angular width is at most a full turn; above a full turn,
  collisions occur at every positive radius.
- [x] Supporting triangle wedges have unique positive boundary-ray coefficients
  and genuine interiors given by strictly positive coefficients.
- [x] Positive-span sectors have genuine closed convex carriers and interiors,
  supporting half-plane descriptions, and closed-interval polar coordinates.
- [x] Construct normalized rigid coordinates on every actual triangle wedge.
  The other edge ray has argument equal to its actual Euclidean corner angle;
  the whole wedge maps isometrically onto the corresponding closed sector.
- [x] Consecutive corners in every constructed link chain cross an actual
  retained radial seam, with direction and endpoint transport recorded.
- [x] Construct finite slit angular fans from closed Euclidean sectors, with
  positive angles below pi and real cumulative headings. Consecutive matched
  rays define the route metric; rigid placements descend to a development at
  every total angle. Cells are isometric, apices coincide, and radial distances
  are exact. Ordered actual links supply angle lists with the correct total.
- [ ] Identify the slit angular fan with the corresponding actual tangent
  wedges, respecting the first/last germ orientation, and close flat cyclic
  fans when their total angle is a full turn.
  - [x] Rigid sector reflection exchanges the banks; directed actual corner
    frames follow the initial/terminal germ convention.
  - [x] Actual radial seam witnesses exist at every prescribed nonnegative
    radius, with matching radii and exact directed-frame coordinates.
  - [x] The angular-to-tangent comparison descends from the actual seams,
    preserves every apex distance, and is surjective for a covering link order.
    No spatial folding is needed.
  - [x] Prove the inverse comparison for interval links, with both round trips
    checked on the original cells; obtain an actual angular-fan isometry at
    every boundary vertex, without a spatial-folding hypothesis.
  - [x] Close cyclic links using their actual radial seam. At a full turn,
    classify all closed-bank fibers, construct the planar bijection, and
    prove the inverse nonexpanding on the whole plane from its finite closed
    sector cover. Obtain the Euclidean cone isometry and original flat chart.
- [x] A radially slit angular fan is nonoverlapping **iff** its total angle is at most
  `2 * Real.pi`.
- [x] At equality the terminal banks coincide in the development; above a full
  turn there is genuine two-piece interior overlap at every positive radius.
- [ ] Lateral pyramid unfolding and a complete convex-pyramid net as benchmarks.

## Phase 5 Embedded convex surfaces and shortest paths

- [x] Spatial rigid face placements, their cut-metric maps, exact within-cell
  distances and spatial/intrinsic topology for embedded surfaces.
- [x] A geometric convex-boundary adapter using the actual finite corner hull,
  nonempty spatial interior, and embedded triangle coverage of its frontier.
- [x] Derive sphere topology and connectedness from convexity, then ordinary
  intrinsic metrics and geodesics; allow flat subdivision corners.
- [ ] Separate maximal facets from input triangulation cells and connect to an
  arbitrary finite-hull/polytope input, including existence of a triangulation.
- [x] Extended length for continuous paths in arbitrary extended pseudometric
  spaces, via Mathlib total variation; chord bound, reversal, concatenation,
  Lipschitz bounds and preservation by isometries.
- [x] Bounded-speed reparameterization of rectifiable paths, preserving their image.
- [x] Shortest-path existence in compact extended metric spaces for endpoints
  joined by a rectifiable path, using compactness and lower semicontinuity.
- [x] Clopen compact finite-distance components with their ordinary metric,
  and length-preserving lifts of rectifiable paths to those components.
- [x] Codomain restriction preserves path length and geodesics; affine
  subpaths preserve constant speed, including reversed and degenerate intervals.
- [x] Intrinsic path metric, correct topology, compactness and geodesics for
  finite triangle complexes and their cut realizations.
- [x] Connect the embedded convex-boundary model to that constructed intrinsic metric.
- [x] Intrinsic distance within each original embedded triangle equals its
  Euclidean chord, for all retained-seam sets.
- [x] Saturated nonexpanding geodesic images are affine straight paths in strictly
  convex normed spaces; embedded-face visits are single closed time intervals.
- [ ] Extend chord exactness from individual triangles to maximal planar facets.
  - [x] The embedded inverse is isometric on every convex spatial subset
    of a convex boundary. Every straight boundary chord has exact intrinsic
    length and a unique geodesic, crossing arbitrary subdivision triangles.
  - [ ] Connect this theorem to the eventual maximal-facet representation.
- [ ] Prove equivalence with the triangle route metric; this is the bridge
  between the embedded and abstract libraries.
- [x] Shortest paths develop straight in flat charts and do not pass through
  positive-curvature vertices in their interiors.
  - [x] Geodesics contained in an isometric Euclidean chart have the exact
    affine endpoint coordinates. Apply this to contained subpaths.
  - [x] Convex charts construct actual ambient geodesics. An explicit endpoint
    margin confines all competing paths to a ball chart and gives uniqueness.
  - [x] Apply straightness, construction and ambient uniqueness to the actual
    whole-ball charts at flat interior vertices.
  - [x] Below a full turn the slit development is injective, including its
    boundary. Convex fans of angle less than pi have the exact Euclidean
    sector metric and geodesics between nonapex endpoints avoid the apex.
  - [x] Lift covered chords across finite closed pieces, including in
    reentrant fans. Prove strict shortcuts in any pointed heading interval
    inside a slit fan and transfer them to the actual tangent metric.
  - [x] Construct isometric lifts of selected pointed heading intervals even
    in overlapping angular fans, with no total-angle bound. Strict shortcuts
    survive every nonexpanding comparison preserving radial distances.
  - [x] Append a repeated first sector and continue the actual cyclic map
    through its closing bank. Obtain strict tangent shortcuts for every
    pair of nonapex points when the total angle is less than a full turn.
  - [x] Transfer strict shortcuts through the constructed whole-ball chart.
    Nonconstant original intrinsic geodesics avoid every such interior
    vertex at all interior parameter times. No convex angle bound is assumed
    implicitly: deriving those bounds from embedded convex geometry remains.
- [x] Local uniqueness and continuation of a geodesic with a given initial
  interval through regular points. Prove two-point determination in a chart
  and propagate agreement by continuous induction; the path endpoints need
  no chart. Regularity uses genuine Euclidean metric-ball charts, constructed
  at face interiors, retained nonvertex seams with distinct incident faces,
  and flat interior vertices.
- [ ] Derive the full regular/singular point classification for an embedded
  convex boundary, including all allowable flat subdivision vertices.
  - [x] A positive-curvature interior vertex is an actual spatial extreme
    point. Otherwise convexity supplies a boundary chord through it, whose
    intrinsic geodesic contradicts vertex avoidance. Nonextreme interior
    vertices therefore have angle at least a full turn.
  - [ ] Prove the convex upper angle bound, with strictness at extreme
    vertices, and identify every nonextreme subdivision vertex as flat.
    - [x] Construct a strict supporting functional with a uniform positive
      margin at every finite-hull extreme point. Construct the actual compact
      convex transverse section and the radial projections of all other
      generators; at triangulation vertices the section is nonempty.
    - [x] A positive functional level cuts a two-ray wedge in the segment
      between its radially normalized endpoints, preserving the apex angle.
    - [x] The whole transverse body section is exactly the convex hull of
      the radial projections of the other generators, via rescaled finite
      barycentric weights. Apply this to every actual spatial extreme vertex.
    - [x] Construct an ambient interior center in that same section and
      affine Euclidean coordinates on its level plane. Obtain an actual
      compact convex planar vertex figure, with zero in its interior,
      finitely many noncollinear hull generators and a circular boundary.
    - [x] Sum the lateral triangle angle budgets. A transverse apex gives
      strictness at every nonstraight base corner.
    - [x] Derive supporting planes for every original input triangle from
      convexity, including subdivisions of maximal facets. Identify the
      figure boundary with the sliced spatial surface; exclude nonincident
      faces by the strict support margin. Prove each incident face section
      is its actual radial segment and these segments cover the boundary.
    - [x] Construct planar endpoints from actual link germs; prove mate
      invariance, nondegenerate sections with the genuine apex angles,
      consecutive and closing endpoint agreement, and exact chain coverage.
    - [x] Prove the section misses all original corners; characterize
      equal endpoints exactly as equal germs or seam mates. Deduce that the
      cyclic chain has no repeated initial endpoints using embeddedness.
    - [x] Prove open sections lie in original face interiors and cannot meet
      other sections. Construct the actual simple Mathlib polygon with at
      least three vertices and exact boundary; its spatial apex-angle sum
      is the genuine surface total angle. Apply the strict pyramid budget.
    - [x] Supply the nonstraight corner automatically for every nonempty
      finite pyramid. Prove the figure's central triangles noncollinear,
      with positive angles below pi and unique boundary points on rays.
    - [x] Use gauge normalization and frontier ray uniqueness to prove
      coverage and open-cone separation. Derive globally consistent radial
      orientation, exact cumulative headings, and one full turn of the actual
      central fan from nonoverlap and its closing ray.
    - [x] Prove exact center splitting of each boundary corner angle,
      including straight subdivisions. Sum the central triangles to derive
      the actual polygon angle sum; combine with the strict lateral budget.
      Interior extreme vertices have genuine total angle below two pi,
      giving extremality iff positive curvature and geodesic avoidance.
    - [x] Derive that the uncut convex boundary has no unpaired banks,
      using continuous radial projection across each triangle edge and exact
      seam classes. Obtain cyclic links at every vertex, remove the interior
      premise from extreme-vertex curvature/avoidance, and construct regular
      charts at every nonvertex surface point.
    - [ ] Prove the upper angle bound also at nonextreme vertices and obtain
      flatness and regular charts at every nonextreme subdivision vertex.
      - [x] A body chord through a nonextreme vertex supplies a common nonzero
        direction in every incident rigid face plane. The intersection of
        distinct incident planes is the actual seam direction line, so every
        genuine crease lies along that one common axis.
      - [x] Equal spatial unit directions classify exactly equal germs or
        seam mates, by small positive radial lifts to regular original-edge
        points. Initial directions in an embedded cyclic chain are distinct.
        The common axis therefore permits at most two genuine creases.
      - [x] A nonconstant cyclic list has no more labels than changes. Derive
        at most two incident planes and a small spatial vertex star.
      - [x] Radial projection identifies the actual nearby boundary with
        the two supporting half-planes. Construct the local vertex hinge,
        including coincident planes. Transfer a whole intrinsic Euclidean
        chart in the coincident-plane case from convex spatial patches.
      - [ ] Transfer the chart in the genuine two-plane hinge case, and
        complete the angle equality at nonextreme vertices as well.
        - [x] The actual tangent image agrees with the original surface near
          the vertex; radial homogeneity extends the local support-hinge
          equality to the whole tangent fan. Prove its spatial inverse is
          isometric on every convex subset of the actual image.
        - [ ] Select a genuine incident crease when the planes differ,
          use its constructed outward hinge placement to parametrize the
          two half-planes, and transfer the intrinsic chart.

## Phase 6 Source unfolding

- [ ] A generic source in a regular face interior and normalized shortest routes.
- [ ] Source distance, the set of nonunique shortest paths, and its closure.
  Cone vertices can be cut-locus leaves with a unique incoming geodesic, so the
  nonuniqueness set alone is not the complete closed cut locus.
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
