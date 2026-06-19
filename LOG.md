# LOG

## Session Log

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
