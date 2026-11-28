# Roadmap

Results that are in scope for the library and do not yet have a statement in an
abstract file. An entry leaves this file when its theorem is stated in a
`*/Abstract.lean` module, proved without `sorry`, and listed in `Audit.lean`.

[PLAN.md](PLAN.md) is the working checklist of the proofs. This file is
shorter: it says what a reader will be able to check once a target is reached.
The [book](https://slef.github.io/lean-unfoldings/) explains the statements
that exist, and marks the ones below as not yet formalized.

Nothing in this file is checked by Lean. The statements are proposals.

## 1. Star unfolding

**Source.** B. Aronov and J. O'Rourke, *Nonoverlap of the star unfolding*,
Discrete & Computational Geometry 8 (1992), 219–250.

**Mathematics.** Let `x` be a point of a convex polyhedron with `n` vertices,
with exactly one shortest path from `x` to each vertex. Cut the surface along
these `n` paths. The result is a disk that is flat in its interior, so it
develops in the plane.

- **Nonoverlap.** The development is injective. Its image is a simple polygon
  with `2n` corners: the `n` vertices alternate with `n` images of `x`.
- **Voronoi property.** The distance on the surface from `x` to the point shown
  at `z` is the Euclidean distance from `z` to the nearest image of `x`.
  Equivalently, the cut locus of `x` develops onto the Voronoi diagram of the
  images of `x`, restricted to the polygon.

**Proposed statement.** A predicate `IsStarUnfolding K source region fold` next
to `IsSourceUnfolding` in `Unfoldings/Source/Abstract.lean`, with the same
arguments. It would ask:

1. `IsNetOf K.surface region fold`, the existing definition of a net, unchanged;
2. a map `project : region → M.Surface` that is continuous, surjective and
   agrees with `fold`, as in `IsSourceUnfolding`;
3. that `project` preserves distances near every interior point of the region;
4. that the frontier of the region is a simple polygon (the predicate
   `SimplePolygon` of `Unfoldings/Cap/Abstract.lean`, which would have to be
   shared or repeated);
5. that `project` maps the frontier onto the union of `n` shortest paths, one
   from the source to each vertex;
6. the Voronoi property: `M.distance (M.point source) (project z)` is the
   infimum of `‖z - c‖` over the points `c` of the region with
   `project c = M.point source`.

The theorem would then read: for every polyhedron `K` and every source that is
not a vertex and has a unique shortest path to every vertex, there are a region
and a folding with `IsStarUnfolding K source region fold`.

**Open points.**

- *Sources with several shortest paths to a vertex.* Cutting one chosen path to
  each vertex still gives a flat disk. Whether to state the theorem for every
  such choice, and whether the proof of Aronov and O'Rourke covers it, has to
  be decided before the statement is fixed.
- *Sources at a vertex.* The obstruction of the source-unfolding theorem is
  absent here, since the source lies on the outline. Such a source needs no cut
  to itself and changes the count of corners; a first statement can exclude it.
- *A vertex of the triangulation that is not a vertex of the polyhedron* needs
  no cut. The statement must speak of the extreme points of the hull, as the
  hypothesis `nonextreme` of `source_unfolding` does.

**What exists.** The source-unfolding theorem; the cut locus as a finite tree
whose leaves are the vertices (`Unfoldings/Source/CutTree.lean`); developments
of cut surfaces (`Unfoldings/Source/ActualCut.lean` and the modules around it).
The star unfolding consists of the pieces of the source unfolding between
consecutive shortest paths to vertices, glued along the cut locus instead of
around the source. A proof may be able to reuse the source unfolding in this
way; the proof of nonoverlap in the paper is a separate argument.

**Illustration.** The book computes the star unfolding in the browser
(`book/src/assets/viz/geom.js`, `starUnfolding`) and tests the two properties
above numerically on the solids of its figures (`book/test/geom.test.mjs`).
This is an illustration and a sanity check of the proposed statement, not part
of the formalization.

## 2. Sources at vertices

The source-unfolding theorem excludes sources at vertices of the polyhedron,
where no neighbourhood of the source is flat. The layout of the shortest paths
around such a source needs a definition in which the source is a corner of the
net and not an interior point. In the proofs this needs sector-valued source
frames (see the README).

## 3. Fewest Nets

The tools needed for the Fewest Nets paper, downstream of the star unfolding.
[PLAN.md](PLAN.md), section "Later targets and Fewest Nets", tracks them. They
will get entries here when their statements are settled.
