# LOG

## Session Log

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
