# The source-unfolding theorem

```headline source-unfolding
title: Every point of a convex polyhedron that is not a vertex has a source unfolding
source: @sharir1986
key: yes
theorems: SourceAbstract.source_unfolding

Let $K$ be a triangulated convex polyhedron and let the source be a point of its surface that is not a vertex of $K$. Then there are a region of the plane and a folding map that form a net of the surface of $K$, with the source at the origin, such that the interior of the net is the surface minus the cut locus of the source, its frontier folds onto the cut locus, and the radial segments of the net are exactly the shortest paths from the source.
```

## The statement

@stmt SourceAbstract.source_unfolding

The theorem takes a mesh `M` ([Chapter 1](meshes.html)), a polyhedron `K` on it ([Chapter 5](polyhedra.html)) and a tagged point `source` ([Chapter 2](gluing.html)). Its hypothesis `nonextreme` says that the position of the source in space is not an extreme point of the convex hull of the corners, that is, not a vertex of the polyhedron. Its conclusion is that some region and some folding map satisfy [[SourceAbstract.IsSourceUnfolding]] ([Chapter 7](source-unfoldings.html)).

The proof shown under "show proof" is one line. It hands the fields of `M` and `K` to a theorem of `Source/AbstractBridge.lean`, which translates them into the internal vocabulary of the library and applies the construction proved there. Lean checks that this translation is faithful: if the bridge proved something else, the line would not compile.

::: check
- **The hull in the hypothesis is the hull in the definition.** The expression `convexHull ℝ (Set.range fun p => K.place p.1 (M.vertex p.1 p.2))` is, symbol for symbol, the one in the fields `interior_nonempty` and `boundary` of [[SourceAbstract.Polyhedron]].
- **Which sources are allowed.** Every point in the interior of a face, every point in the interior of an edge of the polyhedron, and every corner of the triangulation that is not a vertex of the polyhedron. The docstring says: "Sources on creases and flat subdivision vertices are included; no generic-position assumption is needed."
- **`Face Seam : Type`.** The types of faces and seams live in the lowest universe. This is no restriction for finite types.
- **The conclusion is an existence statement.** `∃ region fold, …`. The theorem does not name the net or give a way to compute it.
:::

## Why vertices are excluded

The exclusion is not only a limitation of the proof. For a source at a vertex, the statement in this form would be false.

Property d of [[SourceAbstract.IsSourceUnfolding]] puts the source at an interior point of the net, and property h says that the folding preserves distances near every interior point. So a small disk of the plane around the origin would be isometric to a neighbourhood of the source on the surface. At a vertex of a convex polyhedron the angles of the faces add up to less than $2\pi$, so a circle of small radius $r$ around the vertex has length less than $2\pi r$. No neighbourhood of a vertex is isometric to a flat disk.

For a source at a vertex one can still develop the shortest paths around the source, but the source then sits at a corner of the outline of the layout, not in its interior. Stating that case requires a different definition. The README of the library lists it as remaining work.

## What the theorem does not say

- **No algorithm, no complexity.** Algorithms for shortest paths on polyhedra compute this structure, starting with @sharir1986; the Lean theorem is about existence only.
- **Convex polyhedra only.** [[SourceAbstract.Polyhedron]] requires the surface to be the boundary of a convex hull.
- **Dimension three only.** @miller2008 extend source unfoldings to convex polyhedra of higher dimension. Nothing of that is formalized here.
- **No count of pieces.** The net is a finite union of convex polygons; the theorem gives no bound on their number.
- **Nothing about the star unfolding**, the other general unfolding of convex polyhedra [@aronov1992], which the README lists as future work.

## Where the result comes from

The planar layout of a convex polyhedron obtained by cutting along the ridge points of a source was introduced for computing shortest paths by @sharir1986. @demaine2007 present it, under the name source unfolding, together with the star unfolding. @miller2008 give a general treatment in all dimensions.
