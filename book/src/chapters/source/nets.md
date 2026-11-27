# Nets

A net of a surface is a flat piece of paper, with fold lines, that folds up to the surface. This chapter defines nets for an arbitrary surface in space. The definition knows nothing about sources, shortest paths or convexity; those come in [Chapter 7](source-unfoldings.html).

## Convex polygons

@decl SourceAbstract.Polygon

A set of the plane is a `Polygon` when it is compact, has an interior point, and is the intersection of finitely many closed half-planes. Each half-plane is given by an affine function $h_i$ from the plane to the reals, as the set where $h_i \ge 0$.

::: check
- **These are convex polygons.** An intersection of half-planes is convex. The pieces of a net will be convex; a net as a whole need not be.
- **No degenerate pieces.** A segment or a point is an intersection of half-planes too, but has empty interior.
- **Compactness excludes unbounded pieces**, and with it the case of no half-plane at all, which gives the whole plane.
- A constant function is an affine function. It gives a "half-plane" that is everything or nothing. This is harmless: it changes nothing, or contradicts the interior condition.
:::

## Nets of a surface

@decl SourceAbstract.IsNetOf

`IsNetOf surface region fold` relates three things: a set `surface` of space, a set `region` of the plane, and a map `fold` from the region to space. It is a conjunction of six conditions.

1. **The region is a disk.** There is a homeomorphism between `region` and the closed unit disk. The paper is in one piece and has no holes.
2. **Folding is continuous.** The paper is not torn.
3. **Folding covers the surface exactly.** The image of `fold` is `surface`: every point of the surface is covered, and nothing sticks out.
4. **Folding is injective on the interior.** Two different points in the interior of the region go to different points of the surface. Only points of the boundary of the paper may meet, as they must when the surface is closed.
5. **Folding is rigid on each piece.** The region is the union of finitely many convex polygons with pairwise disjoint interiors, and on each polygon `fold` coincides with an isometry `motion i` from the plane into space.
6. **The outline is polygonal.** The frontier of the region is a finite union of segments.

::: check
- **Non-overlap is built in.** The region is a subset of the plane. A layout in which two parts of the unfolded surface lie on top of each other is not a subset of the plane with a map to the surface; it cannot be expressed as a `region` and a `fold` satisfying condition 4. For most unfolding questions non-overlap is the hard part, and here it is carried by the shape of the definition: one planar set, and injectivity on its interior.
- **Lengths are preserved.** Conditions 2, 4 and 5 make `fold` a local isometry from the interior of the region to the surface: on each piece it is rigid, and across the common side of two pieces it is continuous, so the two rigid pieces are hinged along that side. Paths in the interior of the net keep their length when folded.
- **The cuts are not named.** The definition does not say where the surface was cut. The cuts are wherever `fold` fails to be injective, which is on the frontier. In particular the cuts may run through the interior of faces. Edge unfoldings, where the cuts follow edges, are the subject of [Part III](part-caps.html).
- **The pieces are not the faces.** A piece is a convex polygon on which the folding is rigid. A face of the polyhedron may be cut into several pieces, and nothing here relates pieces to the triangles of a mesh: `IsNetOf` takes only a set `surface`.
- **`∃ hz : x.val ∈ region, fold ⟨x.val, hz⟩ = …`** is how the definition evaluates `fold`, whose domain is the region, at a point `x` known to lie in a piece. It says: `x` is in the region, and `fold` there equals the rigid motion.
- **Mirror images.** An isometry from the plane into space has no handedness, so the mirror image of a net is a net.
- **Condition 6 adds little.** The frontier of a finite union of convex polygons already consists of segments. The condition is harmless, and makes the statement explicit.
:::
