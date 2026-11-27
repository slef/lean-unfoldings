# Convex polyhedra

So far nothing lives in space. A convex polyhedron is a mesh together with a rigid placement of each of its triangles in $\R^3$, such that the placed triangles fit together into the boundary of a convex body.

## The definition

@decl SourceAbstract.Polyhedron

A polyhedron on the mesh `M` has one piece of data and four conditions.

- **`place f`**: for each face, an affine isometry from the plane to space, written `Plane →ᵃⁱ[ℝ] Space`. It is a rigid placement of the whole plane of the face: it preserves distances, and it sends the triangle of face `f` to a congruent triangle in space. The point `x` of face `f` lands at `place f x`.
- **`joined`**: glued points land at the same place. For every seam `s` and every point `x` of its first edge, the placement of `x` by the first face equals the placement of `identify s x` by the last face.
- **`embedded`**: only glued points land at the same place. If two tagged points have the same position in space, they are related by a chain of gluing steps, that is, they are the same point of the surface.
- **`interior_nonempty`**: the convex hull of all placed corners has an interior point. The body is three-dimensional.
- **`boundary`**: the union of the placed triangles is exactly the frontier of that convex hull.

Together, `joined` and `embedded` say that the placement is a well-defined injective map from the surface into space. The last two conditions say that its image is the boundary of a convex polytope.

::: check
- **The convex body is the hull of the corners.** The expression `convexHull ℝ (Set.range fun p => place p.1 (M.vertex p.1 p.2))` is the convex hull of the finitely many points where the corners of all faces land. It is a convex polytope. `frontier` is its topological boundary.
- **No conclusion is hidden.** The fields mention gluing, positions in space and a convex hull. They do not mention distances on the surface, shortest paths, nets or unfoldings. The docstring states this as the intent.
- **The surface must be closed, edge to edge.** Nothing in `Mesh` forces every edge to be glued, but `boundary` and `embedded` do: the boundary of a polytope has no edge, so every edge of a triangle must be met by another triangle, and by `embedded` coinciding points must be glued. Since seams pair whole edges, the triangles must meet edge to edge.
- **The taping direction is forced.** [Chapter 1](meshes.html) noted that a seam could match two edges in either direction. `joined` leaves only the direction that agrees with the positions in space.
- **Flat seams are allowed.** Two triangles in the same plane, such as the two halves of a square face, satisfy all the conditions. A polyhedron in this sense is a *triangulated* convex polyhedron, and its triangulation may be finer than its faces.
- **Mirror images are allowed.** An affine isometry of the plane into space has no handedness. A triangle may be placed "face up" or "face down".
- **Can it be satisfied?** The abstract file constructs no example of a `Polyhedron`. If the conditions were contradictory, every theorem about polyhedra would hold for no reason. The conditions are the ordinary description of a triangulated convex polyhedron, and the figures of this book use five instances (computed numerically, not in Lean). A formal example in the abstract file, say a tetrahedron, would settle this point by machine.
:::

## The surface in space

@decl SourceAbstract.Polyhedron.surface

`K.surface` is the union of the placed triangles, a subset of space. By the condition `boundary` it equals the frontier of the convex hull. It is the set that a net must fold onto ([Chapter 6](nets.html)).

## Vertices

The source-unfolding theorem excludes sources at the vertices of the polyhedron. It says so with a Mathlib notion: a point of a convex set is an *extreme point* when it is not strictly between two other points of the set. The extreme points of a convex polytope are its vertices in the usual sense: the corners where the surface is actually pointed.

::: check
A corner of the *mesh* need not be a vertex of the *polyhedron*. The centre of a square face, if the face is cut into four triangles meeting there, is a corner of four triangles and is not an extreme point. A corner in the middle of an edge of the polyhedron is not extreme either. The theorem allows sources at all such points.
:::
