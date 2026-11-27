# Meshes with cuts

The cap theorem is about cutting a surface along some of its edges. So its file needs meshes in which a seam can be *kept* or *cut*. This chapter covers the part of `Unfoldings/Cap/Abstract.lean` that sets this up.

## The same mesh, defined again

@decl CapAbstract.Plane CapAbstract.Space CapAbstract.Corner CapAbstract.next

@decl CapAbstract.triangle CapAbstract.edge

@decl CapAbstract.Mesh

These declarations are word for word those of [Chapter 1](meshes.html), in the namespace `CapAbstract` instead of `SourceAbstract`. Everything said there applies: each face has its own coordinates, a seam pairs two whole edges by a distance-preserving bijection, a local edge belongs to at most one seam, and edges may stay unpaired.

::: check
- **Two different Lean types.** `CapAbstract.Mesh` and `SourceAbstract.Mesh` have the same fields but are distinct structures. A theorem about one says nothing, formally, about the other. This is the price of keeping each abstract file self-contained: a reader of one theorem never has to open the other file.
- **One real difference.** Here `Face` and `Seam` may live in any universe (`Type*`); in the source file they are in `Type`. The cap theorem itself quantifies over meshes with `Face Seam : Type`, so nothing depends on this.
- **Boundary matters here.** A cap is a surface with boundary: the edges of its rim are in no seam. For the closed polyhedra of [Part I](part-surfaces.html) unpaired edges were permitted by `Mesh` and excluded by `Polyhedron`; here they are essential.
:::

## Points on edges

@decl CapAbstract.Mesh.Point CapAbstract.Mesh.edgePoint

A tagged point is, as before, a face together with a point of its closed triangle. `edgePoint a x` takes a local edge `a` (a face and a corner) and a point `x` of that edge, and returns `x` as a tagged point of the face. The body of the definition is the proof that a point of an edge lies in the triangle: an edge is the segment between two corners, and the triangle is convex and contains its corners.

## Gluing along the retained seams

@decl CapAbstract.Mesh.glue CapAbstract.Mesh.Surface

Here is the addition. The gluing relation takes a set `retain` of seams, and only those seams glue: `M.glue retain p q` holds when a seam `s` *in `retain`* and a point `x` of its first edge exist such that `p` is `x` on the first edge and `q` is `identify s x` on the last. The surface `M.Surface retain` is the quotient.

- With `retain = Set.univ`, all seams are kept, and `M.Surface Set.univ` is the surface of the mesh as in [Chapter 2](gluing.html).
- With a smaller set, the seams outside `retain` are cut. `M.Surface retain` is the cut surface: the same triangles, attached along fewer edges.

::: check
- **Cuts follow whole edges.** A seam is either kept entirely or cut entirely. There is no way to cut along part of an edge or across a face. This is what "edge" in "edge unfolding" means.
- **Vertices come apart as far as the cuts allow.** Two tags of the same corner of the original surface remain identified in the cut surface only if a chain of *retained* seams connects them. Cutting all the seams at a corner but one leaves the corner attached along that one.
- As in [Chapter 2](gluing.html), the relation is directed and the quotient uses its symmetric and transitive closure.
:::

## Boundary edges

@decl CapAbstract.Mesh.boundaryEdge

A local edge is a boundary edge when it is neither the first nor the last edge of any seam. This refers to the original mesh, before any cut: it is the rim of the cap, not an edge made free by cutting.

## The acute margin

@decl CapAbstract.Mesh.AcuteMargin

`M.AcuteMargin α` says that every angle of every triangle is at most $\pi/2 - \alpha$. In `EuclideanGeometry.angle p q r` the angle is measured at the middle point `q`. Here the middle point is corner `i`, and the other two are the next corner and the one after it, so the expression is the angle of the triangle at corner `i`.

::: check
- **For $\alpha > 0$ all triangles are acute**, and uniformly so: no angle comes closer than $\alpha$ to a right angle. The theorem assumes $\alpha > 0$.
- **Angles in the plane are angles in space.** The condition is about the triangles of the mesh in their own planes. Placing a triangle in space by an isometry does not change its angles, so these are the angles of the faces of the cap, not of their projections to the ground.
- **Angles are in radians.**
:::
