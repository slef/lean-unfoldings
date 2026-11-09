# LOG

## Session Log

### 2026-11-09 — metric excision and vertex-star neighborhoods

- Strengthened generic finite closed-seam localization: compatibility only at
  incident seams makes a map constant on the chosen class and nonexpanding on
  a whole sufficiently small intrinsic neighborhood.
- Constructed whole-ball isometries for seam excision, using the canonical map
  that restores cuts. Applied this to triangle complexes without a development
  or manifold assumption.
- Isolated each vertex's incident seams. Proved that its complete corner class,
  unique central vertex copy, total angle, and a whole small metric ball remain
  unchanged after cutting all distant seams.
- Constructed actual convex closed supporting wedges at triangle corners and
  wedge-ball/cell-ball isometries. Proved positive clearance to the opposite
  edge and invariance of the wedge under nonnegative radial scaling.
- Proved that spatially foldable complexes have at most one representative of
  a point class in any original cell; incident corner classes therefore use
  distinct original faces.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1151 declarations, and `git diff --check` passes.
- The metric tangent fan/cone and its comparison with these star neighborhoods
  remain to be constructed; no source-unfolding conclusion is assumed here.

### 2026-11-09 — constructed vertex-link orders

- Constructed the endpoint permutation of every full-edge isometry, including
  reversal. Defined the two actual edge germs at every tagged triangle corner.
- Proved uniqueness and symmetry of retained seam germ pairings. Seam transport
  is an involution with fixed points precisely at unpaired boundary banks;
  turning within a corner is a fixed-point-free involution.
- Proved that germ connectivity is exactly retained metric-vertex equivalence.
  Thus a vertex link has no hidden disconnected components. Boundary incidence
  is equivalent to existence of an unpaired link germ.
- Proved a geometry-independent finite two-involution classification by maximal
  nonrepeating interval chains. Closed systems give cycles, and boundary systems
  give intervals with exactly two unpaired endpoints. One-interval cycles are
  allowed, so loops/self-pairings are preserved.
- Applied that classification to every cut vertex link, constructing its cyclic
  or interval corner order. Each incident corner occurs exactly once and its
  ordered Euclidean angles sum to the actual vertex total angle.
- Verification: selected Fin-tuple/endpoint-geometry cache fetch and `lake build`
  pass; the audit checks 1083 declarations, and `git diff --check` passes.
- Metric fan/cone neighborhoods and geometric convex-vertex angle bounds remain
  unproved; no such conclusion was made a link-order input.

### 2026-11-09 — vertex copies and actual angle sums

- Defined vertices as quotients of tagged original corners by retained-seam
  chains. Proved their images inject into the actual metric realization and
  characterize exactly its original corner points.
- Constructed surjective maps between vertex copies when restoring cuts,
  commuting with the metric maps. Defined boundary incidence using endpoints
  of the actual unpaired banks.
- Defined corner angles from Euclidean geometry, proved each is strictly
  between zero and pi, and proved each triangle's sum is pi.
- Defined total angles of retained vertex classes. Proved positivity, the
  global sum `number of triangles * pi`, and conservation of angle when a
  vertex splits into cut copies. No cone-chart or curvature-bound conclusion
  has been assumed.
- Verification: selected triangle-geometry cache fetch and `lake build` pass;
  the audit checks 929 declarations, and `git diff --check` passes.
- Vertex-link classification and metric cone/sector charts are next.

### 2026-11-09 — spatial convex boundaries and face visits

- Added compatible rigid spatial face placements. They descend through every
  cut metric and make every original cell isometric. Spatial injectivity stays
  separate; for embedded uncut surfaces, proved equality of intrinsic and
  spatial subspace topology. Rigid foldings rule out same-face edge pairings.
- Added a geometric convex-boundary adapter: the actual finite corner hull has
  nonempty spatial interior, and the embedded triangle union is exactly its
  frontier. Flat/subdivision corners are allowed. Maximal facets are not yet
  represented by a separate API.
- Used Mathlib's gauge-rescaling homeomorphism to derive sphere topology,
  connectedness, finite intrinsic distances and shortest paths. The generic
  bounded-convex-boundary theorem lives separately in `Topology/`.
- Proved strict-convexity straightness of saturated nonexpanding geodesic images,
  including their affine parameterization. Proved face no-re-entry on embedded
  surfaces and that each visited closed face occupies one closed time interval.
- Proved that finite metric distances are equivalent to retained face-incidence
  connectivity; geometric convex boundaries therefore have connected dual incidence.
- Verification: selected Mathlib cache fetch and `lake build` pass; the audit
  checks 892 declarations, and `git diff --check` passes.
- Cone geometry, vertex avoidance, cut-locus construction and source unfolding
  remain open; this adapter assumes no geodesic or unfolding conclusion.

### 2026-11-09 — retained-edge Euclidean ball charts

- Proved a generic local development estimate for finite closed seam systems:
  cell maps need agree only across seams incident to the chosen finite class.
- Constructed local hinge coordinates and proved exact intrinsic/Euclidean
  distance equality in a small ball around each nonvertex retained-seam point
  with distinct incident faces. This uses the actual route metric and does not
  require a global development.
- Constructed isometries from whole Euclidean balls onto whole intrinsic balls,
  agreeing with both original incident face maps in their outward hinge frames.
- Self-paired edges remain supported by the complex API; their charts need a
  two-patch argument inside one original cell and are not claimed here.
- Verification: selected Mathlib cache fetch and `lake build` pass; the audit
  checks 804 declarations, and `git diff --check` passes.

### 2026-11-09 — hinge neighborhoods and metric localization

- Proved barycentric reconstruction, exact edge membership, and proportionality
  of affine supporting functions vanishing along an edge.
- Proved that outward hinge triangles intersect exactly in their shared edge
  and cover a planar ball around every nonvertex seam point. Chords crossing
  the two sides meet the actual seam, giving intrinsic distance upper bounds
  in a full triangle complex.
- Added a generic short-route localization theorem: a local nonexpanding step
  estimate gives a metric lower bound whenever the radius budget is satisfied.
- Exposed quantitative capped-distance class barriers. Small metric balls at
  a nonvertex seam class use only its two tagged representatives; for distinct
  incident faces the coordinate distances are controlled by intrinsic distance.
- Added retained-face connectivity, ordinary intrinsic metrics for connected
  complexes, and geodesics between all pairs in those complexes.
- Verification: `lake build` audits 741 declarations; `git diff --check` passes.
- The paired-edge chart still needs the local model map and its lower-bound
  application; no full paired-edge chart is claimed at this milestone.

### 2026-11-09 — boundary half-ball charts

- Constructed the affine basis and barycentric coordinate functions for every
  triangle. Characterized carrier/interior membership by coordinate signs.
- Proved that nonvertex edge points have positive endpoint coordinates,
  zero opposite coordinate, and positive clearance from the other two edges.
  This gives an actual local supporting-half-plane description.
- Proved clearance of every nonvertex unpaired-bank point from retained seams.
  Constructed isometries from Euclidean half-balls onto entire intrinsic open
  balls in the cut realization, agreeing with the original bank's face map.
- Verification: `lake build`, the transitive axiom audit, and `git diff --check`.
- Paired-edge and vertex charts remain open.

### 2026-11-09 — geodesics for constructed cut metrics

- Constructed straight paths in triangle cells with exactly their Euclidean
  length. Constructed continuous realization paths from every finite-cost route.
- Defined continuous-path intrinsic distance and proved that it equals the
  constructed route metric when cell distances are realized by cell paths.
- Applied compact shortest-path existence and the endpoint-saturation geodesic
  criterion. Every finite-distance pair in every cut triangle realization is
  joined by an actual constant-speed metric geodesic. No manifold, embedding,
  convexity or global development premise was used.
- Added a chosen-geodesic API after proving existence. It makes no uniqueness
  or cut-locus assertion.
- Verification: `lake build`, the transitive axiom audit, and `git diff --check`.

### 2026-11-09 — compact shortest-path existence

- Generalized the speed-bound length estimate to arbitrary extended
  pseudometric targets. Added metric geodesics and proved their length and
  minimizing properties; an endpoint-distance speed bound forces a geodesic.
- Adapted the reference's natural-parameterization argument to arbitrary metric
  spaces. The newer Mathlib continuity theorem shortens the accumulated-length
  proof. Pauses and zero-length paths are handled.
- Proved compactness of bounded-speed families and lower semicontinuity of
  length. Constructed shortest paths between any rectifiably joined points of
  a compact metric space, with a speed bound by the minimizing length.
- Constructed clopen finite-distance components of extended metric spaces and
  their ordinary metrics. Rectifiable paths lift without changing length.
  This extends shortest-path existence to compact extended metric spaces.
- Verification: targeted constant-speed and Arzela-Ascoli cache fetches;
  `lake build` and `git diff --check` pass. The audit checks 612 declarations.
- The continuous-path/route-distance bridge is the next cut-metric step.

### 2026-11-09 — constructed hinges and continuous path length

- Extended arbitrary closed-segment isometric embeddings to planar rigid
  motions. Constructed edge-line reflection and proved its signed-area reversal.
- Constructed strict outward hinge placements and nonoverlapping developments
  for arbitrary nondegenerate triangles with full-edge isometric pairings.
- Added `Path.eLength` for arbitrary extended pseudometric targets. Proved the
  chord lower bound, reversal and concatenation formulas, Lipschitz bounds and
  invariance under isometries.
- Rechecked the EdgeUnfoldings reference at the same pinned commit. Its generic
  variation arguments are useful for path length and bounded-speed compactness;
  its shortest-branch continuation results inspected here impose additional
  small-polyhedron hypotheses and cannot be used as general convex-surface facts.
- Verification: selected cache fetches for reflection and bounded variation;
  `lake build` and `git diff --check` pass. The audit checks 566 declarations.
- Constant-speed replacement and shortest-path existence are next.

### 2026-11-09 — face-interior metric charts

- Proved quantitative seam-clearance estimates for general metric-cell gluing.
  Compatible single-cell functions extend by constants to other cells; capped
  distances bound intrinsic distance from below.
- Proved that a sufficiently small intrinsic ball consists exactly of the
  corresponding original cell ball and constructed an isometry between them.
- Separated supporting-height lemmas from the development-dependent hinge
  module without changing their statements. Proved all triangle edges lie
  outside the carrier interior and constructed positive clearance radii.
- Constructed Euclidean ball charts at every face-interior point of every cut
  triangle complex, agreeing with its original face map. No global placement or
  manifold conclusion was assumed.
- Verification: `lake build` passes without warnings; 512 declarations pass the
  transitive axiom audit; `git diff --check` passes.
- Paired-edge and vertex charts remain under construction.

### 2026-11-08 — triangle-complex exactness

- Proved that closed-edge isometries preserve endpoints, and distinct edges of
  a nondegenerate triangle intersect only at its corners.
- Proved finiteness of every retained-seam class: corner classes lie in a finite
  set, and a nonvertex point has at most one undirected seam neighbor. The
  relation-theoretic lemma is independent of all metric and triangle geometry.
- Adapted triangle edge pairings to the general closed-seam theorem. Proved
  exactness for all retained-seam sets and an unconditional homeomorphism
  between the original cell quotient and the constructed metric realization.
- Added separation of unpaired bank interiors, while allowing endpoints to be
  identified through other retained seams.
- Verification: selected cache fetch for strict convexity and linear-combination
  tactics; `lake build` and the transitive axiom audit.

### 2026-11-08 — closed-seam separation theorem

- Continued toward the full source-unfolding construction, starting with metric
  exactness for retained seams.
- Constructed capped distance-to-class barriers, including cells with no class
  points. Proved nonexpansion and zero-set characterization for closed classes.
- Proved that finite classes with positive local transport radii give exactness.
  Finite sets and closed seam images supply uniform positive radii.
- Bundled finite closed isometric seams and proved exactness whenever their
  equivalence classes are finite in each original cell. Cells need not be compact.
- Moved the unchanged corner-case lemma into the triangle foundation and added
  compactness of closed triangle edges and their metric subspaces.
- Verification: targeted cache fetch for Hausdorff distance and Lipschitz
  infrastructure, followed by `lake build` and the transitive axiom audit.
- Triangle-specific finite seam-class geometry is the next construction step.

### 2026-11-08 — unglued metric and boundary banks

- Committed seam-quotient and compactness work as `152855f` (320 declarations
  passed the transitive axiom audit).
- Proved the exact no-seam metric formula for arbitrary families: original
  distance within cells, infinity between cells. Proved isometric cell maps and
  exactness for separated cells, including completely cut triangle complexes.
- Added boundary-edge predicates and monotonicity under cutting. The unique
  pairing condition proves that either side of a seam is a boundary edge iff
  that seam is cut.
- Added the two distinct local bank labels, nonexpanding maps of their closed
  edges, and pointwise bank identification when the seam is restored. Bank
  labels do not imply that all their endpoints have distinct metric images.
- Added hinge examples checking bank creation, infinite distance between cut
  cells, and restoration of the original bank pairing.
- Boundary-vertex classes, local manifold charts, and exactness with retained
  seams remain open.
- Verification: `lake build` including examples and the transitive axiom audit;
  `git diff --check`. No additional Mathlib imports needed a cache download.

### 2026-11-08 — seam quotient and compactness

- Committed the verified foundation as `2e73201`.
- Defined the seam quotient independently of the route topology. Proved that
  its points agree exactly along finite seam chains, and constructed its
  continuous surjection to the metric realization.
- Defined metric exactness, characterized it by injectivity of that surjection,
  and proved a criterion using compatible nonexpanding separating coordinates.
- Proved compactness and completeness for finite compact-cell realizations,
  hence for every finite triangle complex and every retained-seam subset.
- Proved that exactness supplies a homeomorphism between the seam quotient and
  the metric realization. Exactness itself for triangle complexes remains open.
- Added a checked example where gluing all nonzero real points also collapses
  zero in the metric quotient, although zero is a separate seam class.
- Verification: selected `lake exe cache get` for `Mathlib.Logic.Relation`,
  `Mathlib.Topology.Separation.Hausdorff`, and
  `Mathlib.Topology.UniformSpace.Cauchy`, then `lake build` including the axiom
  audit; `git diff --check`.

### 2026-11-08

- Set source unfolding of convex polyhedra as the first major target. Added the
  full feature checklist in `PLAN.md`, including the fan nonoverlap equivalence,
  sphere/disk cut criteria, and a separate embedded-graph/Euler development for
  possible Mathlib upstreaming.
- Upgraded to stable Lean/Mathlib 4.35.0; Mathlib is pinned by the manifest to
  `56a005855ea17e0b0958f73ec801ae140b0a1679`. Checked the newer metric gluing,
  extended metric, path-length, and polygon infrastructure before choosing it.
- Replaced the placeholder classification and supplied-metric scaffold with
  proved finite-route distance, constructed family gluing, descent of compatible
  maps, and nonexpansion when restoring cut seams.
- Added nondegenerate triangular cells, full-edge isometric pairings, explicit
  retained seams, and facewise developments with strict opposite-side opening.
  Nonoverlap remains a separate predicate, equivalent to multiplicity at most
  one; it permits boundary contacts.
- Proved that placements descend to the cut metric, that a consistent rigid
  development makes its cell maps isometric, and that opposite-side opening
  gives disjoint interiors at every retained hinge.
- Proved the source-facing radial injectivity criterion. It assumes actual
  radial paths and local injectivity; shortest-path and cut-locus construction
  remain explicit future tasks.
- Added checked examples for single-cell metric recovery, infinite distance
  between disconnected cells, endpoint identifications, a nonoverlapping hinge
  with boundary contact, and coincident developed triangles with multiplicity
  two.
- Added the default `Audit` target. It uses Lean 4.35's public `collectAxioms`
  interface and inspects declarations in every imported unfolding module,
  including dependencies behind opaque exported theorem signatures.
- Verification: the following selected cache fetch succeeded, followed by
  `lake build`. The full build checks the library and its examples; the audit
  checks 287 declarations and permits only `propext`, `Classical.choice`, and
  `Quot.sound`. No `sorry` or `admit` remains in the source.

  ```sh
  lake exe cache get Mathlib.Topology.EMetricSpace.Basic \
    Mathlib.Analysis.InnerProductSpace.PiL2 \
    Mathlib.Analysis.Normed.Operator.Banach \
    Mathlib.Topology.IsLocalHomeomorph \
    Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum \
    Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
  lake build
  ```

- Remaining metric boundary: exactness of the zero-distance quotient for finite
  triangle complexes, quotient topology, compactness, vertex links, and local
  charts. `FacewiseDevelopment` does not yet assert unbranchedness at interior
  vertices. The old scaffold remains available in Git history.

### 2026-06-19

- Verified that the current uncommitted workspace changes are the consolidated
  scaffold developed in this chat.
- Verification: `/Users/sl/.elan/bin/lake exe cache get` succeeded with no
  downloads needed, and `/Users/sl/.elan/bin/lake build` succeeded.  The only
  remaining warning is the intentional `sorry` on
  `Unfoldings.convex_metric_bounded_unfolding_thickness_iff`.
- Prepared the current state for commit.

### 2026-06-06

- Read `/Users/sl/Downloads/CODEX_BRIEF_GraphBasedUnfolding.md`.
- Implemented the simplified graph/cell-structure scaffold directly in
  `Unfoldings/Abstract.lean`.
- Consolidated the project layout so there is only one abstract layer: no root
  `Abstract.lean` and no separate `PolyhedralUnfolding` library.
- Verification after consolidation: `lake exe cache get` succeeded with no
  downloads needed, and `lake build` succeeded.  The only remaining warning is
  the intentional `sorry` on
  `Unfoldings.convex_metric_bounded_unfolding_thickness_iff`.

## Definition Choices

The entries below describe the historical scaffold. Current interfaces and
choices are documented in `README.md` and `PLAN.md`.

- `TriangulatedSurface` is the primary surface model.  It records finite
  vertex, edge, and triangular-face types explicitly rather than using
  `SimpleGraph` alone.
- Edges currently store ordered endpoint pairs with `edgeVerts : E → V × V`.
  This is the simplified first scaffold; it can later be replaced by `Sym2 V`
  or a more structured incidence model.
- Convexity is modeled as nonnegative Gaussian curvature at every vertex:
  `∀ v, 0 ≤ S.curvature v`.
- Cone points are vertices with nonzero curvature.
- Refinements are refinements of the triangulated cell structure, preserving
  old vertex curvature and making all new vertices flat.
- Cut trees live in a refinement, have finite vertex and edge support, are
  intended to be trees, and span all cone points.
- General unfoldings are represented by explicit planar placements of
  triangular pieces.  The hard metric compatibility conditions are placeholders
  for now.
- Thickness is face-counting: `multiplicityAt` counts the unfolded triangular
  face interiors containing a plane point.

## Bridge Notes

- No bridge lemmas yet.

## Stuck Points

- None.

## Cost / Usage

- Not recorded by the local toolchain.

## Times

- Initial scaffold work recorded on 2026-06-06.
