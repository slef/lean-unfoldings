# Intrinsic distance

The distance between two points of a polyhedron can be measured in two ways: straight through the solid, or along the surface. The first is the Euclidean distance in space. The second is the *intrinsic* distance, the one an ant walking on the surface experiences, and it is the one that matters for unfolding. It depends only on the mesh, not on how the mesh sits in space.

## The definition

@decl SourceAbstract.Mesh.distance

The definition does not mention paths. It considers every function $d$ that assigns to two points of the surface a value in $[0, \infty]$ and satisfies four conditions:

1. $d(a, a) = 0$;
2. $d(a, b) = d(b, a)$;
3. $d(a, c) \le d(a, b) + d(b, c)$;
4. for two points $a$, $b$ of the same closed triangle, $d$ of the corresponding points of the surface is at most the Euclidean distance $|a - b|$ in the plane of that triangle.

The first three say that $d$ is an extended pseudometric. The fourth says that walking straight inside a face is always possible, so the distance between two points of one face is at most the straight-line distance. The intrinsic distance is the pointwise supremum of all such $d$.

::: check
- **Reading the nested supremum.** In `⨆ d, ⨆ (_ : P d), d x y` the inner supremum ranges over the *proofs* of the condition `P d`. If the condition holds, there is one proof and the inner value is `d x y`. If it fails, there is none, and the supremum of nothing is $0$. So functions that violate the conditions contribute $0$, and the outer supremum is taken over the admissible ones.
- **The supremum is itself admissible.** A pointwise supremum of functions satisfying 1 to 4 satisfies them again. So `M.distance` is the *largest* function with these properties. This is an easy fact, but it is not stated in the abstract file.
- **It respects the gluing by construction.** $d$ is a function of points of the surface, where glued points are already equal. Crossing a seam costs nothing.
- **Values in $[0, \infty]$.** `ENNReal` includes $\infty$. On a disconnected mesh, points of different components are at distance $\infty$. On a polyhedron every distance is finite.
- **It does not use space.** The definition mentions only `M`. Two points on opposite faces of a thin box are far apart for this distance, however close they are in space.
:::

## Why this is the length of the shortest route

The usual definition goes through *routes*. A route from $x$ to $y$ is a finite sequence of straight steps, each inside one closed triangle, where the end of one step and the start of the next are the same point of the surface. Its length is the sum of the Euclidean lengths of its steps. The distance is the infimum of the lengths of all routes from $x$ to $y$.

The two definitions agree. Call $\rho(x, y)$ the infimum over routes.

- Every admissible $d$ is at most $\rho$. Along a route, condition 4 bounds $d$ of each step by its length, and the triangle inequality adds the steps up. So the supremum is at most $\rho$.
- $\rho$ is admissible. It is symmetric, satisfies the triangle inequality because routes concatenate, vanishes on the diagonal, and a single straight step gives condition 4. So the supremum is at least $\rho$.

This is the standard construction of the metric of a space glued from pieces, as the largest metric that does not exceed the given one on each piece [@burago2001, Section 3.1].

::: caveat The route formula is not a theorem of the abstract file
The file defines the distance by the supremum and does not prove that it equals the infimum over routes. The argument above is short, but it is this book's, not Lean's. Inside the library, the lemma `maximal_edist` of `Source/AbstractBridge.lean` identifies the supremum with the library's own route metric; that lemma is internal, and its statement uses internal definitions. A short theorem in the abstract file stating the route formula would let a reader check this point without leaving the reading interface.
:::

## Trying it

In the figure of [Chapter 7](source-unfoldings.html), pointing at the net shows a point of the surface together with both distances from the source: the distance along the surface, and the distance straight through the solid. The second is never larger.
