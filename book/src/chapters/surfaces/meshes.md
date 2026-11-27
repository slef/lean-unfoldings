# Triangles and meshes

A mesh is a finite collection of triangles together with a list of *seams*. Each triangle is drawn in its own copy of the plane. Each seam names two edges and says how the points of one correspond to the points of the other. This chapter defines these ingredients; [Chapter 2](gluing.html) uses the seams to identify points.

## The plane, space and corners

@decl SourceAbstract.Plane SourceAbstract.Space SourceAbstract.Corner

`Plane` is $\R^2$ and `Space` is $\R^3$, both with the Euclidean distance. These are abbreviations for Mathlib's `EuclideanSpace`, so everything Mathlib knows about Euclidean spaces applies. The coordinates of a point `p` of the plane are written `p 0` and `p 1`.

A triangle has three corners, numbered 0, 1 and 2: `Corner` is the type `Fin 3` of natural numbers below 3.

@decl SourceAbstract.next

`next` moves to the following corner in the cyclic order $0 \to 1 \to 2 \to 0$.

## Triangles and edges

A triangle is given by the positions of its three corners, a function `vertex : Corner → Plane`.

@decl SourceAbstract.triangle SourceAbstract.edge

`triangle vertex` is the convex hull of the three corners: the filled, closed triangle, including its edges and corners. `edge vertex i` is the closed segment from corner `i` to corner `next i`. So edge 0 joins corners 0 and 1, edge 1 joins corners 1 and 2, and edge 2 joins corners 2 and 0. An edge is named by the corner it starts from.

::: check
- Both are *sets of points* of the plane, not combinatorial objects. A point of a triangle is a point of $\R^2$ that lies in this set.
- Nothing here requires the three corners to be distinct or non-collinear. That requirement belongs to the mesh, below.
:::

## Meshes

@decl SourceAbstract.Mesh

A mesh over a finite type `Face` of faces and a finite type `Seam` of seams consists of the following.

- **`vertex f i`**: the position of corner `i` of face `f`. Each face has its own coordinates. Two faces that are neighbours on the surface may sit anywhere in their respective planes; the coordinates of different faces are unrelated.
- **`nondegenerate`**: for each face, the quantity $(x_1 - x_0)(y_2 - y_0) - (y_1 - y_0)(x_2 - x_0)$ is not zero, where $(x_i, y_i)$ is corner $i$. This is twice the signed area of the triangle, so the condition says that the three corners are not collinear.
- **`first s`** and **`last s`**: the two edges that seam `s` pairs. An edge of the mesh is named by a pair (face, corner), meaning edge `corner` of that face. The book calls such a pair a *local edge*.
- **`distinct`**: a seam pairs two different local edges. An edge is never glued to itself.
- **`identify s`**: a distance-preserving bijection from the first edge of the seam onto the last. This is the taping instruction: the point `x` of the first edge is to be glued to the point `identify s x` of the last.
- **`unique`**: if two seams have a local edge in common, on either side, they are the same seam. So each local edge takes part in at most one seam.

@viz mesh {"solid": "tetrahedron"}

The figure shows the mesh of a regular tetrahedron: four triangles and six seams. The solid on the left is only there to show what the seams achieve; the mesh itself is the picture on the right.

::: check
- **Whole edges only.** `identify s` is a bijection between two entire edges. A mesh cannot glue an edge to half of a longer edge. Triangulations with a corner of one triangle in the middle of an edge of another are not meshes.
- **Equal lengths are forced.** A distance-preserving bijection between two segments exists only when they have the same length. So a seam between edges of different lengths cannot be written down.
- **Two ways to tape.** Between two segments of equal length there are exactly two distance-preserving bijections: one matches the start of the first edge with the start of the second, the other with its end. The mesh may use either. Nothing in `Mesh` says that the choice is the one that produces an orientable surface. For a polyhedron the choice is forced by the placement in space ([Chapter 5](polyhedra.html)).
- **Either orientation.** `nondegenerate` allows the signed area to be positive or negative. A face may list its corners clockwise or counterclockwise.
- **Edges may stay free.** A local edge that occurs in no seam is a boundary edge. A mesh may have a boundary, may be disconnected, and need not close up. Being a closed surface is again a property of polyhedra, not of meshes.
- **Two edges of one face may be paired.** `distinct` only excludes pairing a local edge with itself.
- **Flat vertices and flat edges are allowed.** A square face of a cube is not a triangle, so it must be given as two triangles with a seam along a diagonal. The mesh does not distinguish this seam from a seam along a true edge of the cube.
- **Finiteness** is carried by the instances `[Fintype Face] [Fintype Seam]`.
:::

@viz mesh {"solid": "cube"}

The mesh of a cube has twelve triangles and eighteen seams. Six of the seams lie along diagonals of the square faces; on the solid they are drawn dashed.
