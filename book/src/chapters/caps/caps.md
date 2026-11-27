# Convex caps

A convex cap is what remains of a convex polyhedron above a plane: a dome over a convex ground region, with its rim on the ground. This chapter defines caps as placements of a mesh in space.

@viz cap {"height": 0.25}

## Horizontal projection and the footprint

@decl CapAbstract.horizontal CapAbstract.footprint

`horizontal p` forgets the third coordinate of a point of space: it sends $(x, y, z)$ to $(x, y)$. In the Lean text, `p i.castSucc` is coordinate `i` of `p` for `i` in $\{0, 1\}$, and `WithLp.toLp 2` packages the pair as a point of the Euclidean plane. The third coordinate `p 2` is the *height*.

The `footprint` of a placement is the horizontal projection of the union of the placed triangles: the shadow of the surface on the ground at noon.

## The definition of a cap

@decl CapAbstract.Cap

A cap on the mesh `M` has two pieces of data: a rigid placement `place f` of each face in space, as for polyhedra ([Chapter 5](polyhedra.html)), and a vector `normal f` for each face. The ten conditions fall into four groups.

**The faces fit together.**

- `joined`: glued points land at the same place in space.

**The normals are the upward unit normals.**

- `unit`: `normal f` has length 1.
- `tangent`: `normal f` is orthogonal to every direction of the plane of face `f`. Here `(place f).linear` is the linear part of the placement, which sends directions of the plane to directions in space.
- `upward`: the third coordinate of `normal f` is positive.

A plane in space has two unit normals, opposite to each other. `unit` and `tangent` leave these two candidates, and `upward` selects the one pointing up. It also excludes vertical faces, whose normals are horizontal.

**The surface is convex and is a graph over its footprint.**

- `supporting`: every point of the surface lies on or below the plane of every face. The expression `place p.1 p.2.val - place f 0` is the vector from a point of the plane of `f` to the position of the tagged point `p`; its inner product with the upward normal is at most $0$.
- `projection`: two tagged points with the same horizontal projection are the same point of the surface (they are related by a chain of gluing steps, with all seams kept).
- `convex` and `interior_nonempty`: the footprint is a convex set with an interior point.

**The rim is on the ground and the cap is above it.**

- `rim`: every point of every boundary edge has height $0$.
- `above`: every corner of every face has height at least $0$.

::: check
- **`place f 0` is a point of the plane of the face, not necessarily of the face.** It is the image of the origin of the plane of `f`. Any point of that plane serves to write the half-space condition, because by `tangent` the normal is orthogonal to the plane.
- **`projection` is also the embedding condition.** Two points with the same position in space have the same horizontal projection. So `projection` implies that the placement is injective on the surface, the property called `embedded` for polyhedra, and says more: no vertical line meets the surface twice.
- **`supporting` makes the surface convex.** The surface lies below each of its face planes, so it is the upper boundary of a convex body. It is this condition, and not `convex`, that makes the cap bulge outward; `convex` is about the shape of the ground region.
- **Heights of all points.** `above` speaks about corners. Every point of a face is a convex combination of its corners, and height is an affine function, so all points have height at least $0$.
- **The rim is planar.** By `rim` the whole boundary lies in the horizontal plane of height $0$. A dome whose rim goes up and down is not a cap in this sense. The library also treats such surfaces, which it calls roofs, but that theorem has no abstract file yet.
- **Is it the usual notion?** @orourke2018 defines a convex cap as the intersection of the surface of a convex polyhedron with a half-space. Such a cap has a planar rim and lies on one side of it, as here. The Lean definition adds that the cap is a graph over the ground, which holds for the nearly flat caps of the theorem, where every normal is close to vertical.
- **Can it be satisfied?** As for polyhedra, the abstract file constructs no example. The figure above shows a surface that satisfies the ten conditions numerically, for every position of the slider.
:::

## Tilt

The theorem measures how flat a cap is by the angle between each normal and the vertical. Since `normal f` is a unit vector, its third coordinate `normal f 2` is the cosine of that angle. The hypothesis of the theorem is written `Real.cos φ ≤ K.normal f 2` for every face: the angle is at most $\varphi$. The figure reports the largest of these angles as the *tilt*.
