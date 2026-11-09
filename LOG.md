# LOG

## Session Log

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
