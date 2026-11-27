# Shortest paths and the cut locus

With a distance on the surface we can say what a shortest path is, and where shortest paths from a given point stop being unique. That place is the cut locus. It is the set along which the source unfolding cuts the surface open.

## Shortest paths

@decl SourceAbstract.Mesh.Shortest

`Path a b` is Mathlib's type of continuous maps $p$ from the unit interval $[0,1]$ to a space, with $p(0) = a$ and $p(1) = b$. Here the space is the surface, with the quotient topology of [Chapter 2](gluing.html).

A path $p$ from $a$ to $b$ is `Shortest` when, for all parameters $s$ and $t$,

$$\dist(p(s), p(t)) = \dist(a, b) \cdot |s - t|.$$

Taking $s = 0$ and $t = 1$ gives nothing new, but every other pair does. The condition says two things at once: the path never takes a detour, since each of its parts realizes the distance between its ends; and it moves at constant speed, since the distance covered is proportional to the time elapsed.

::: check
- **The parametrization is fixed on purpose.** A geometric shortest curve can be traversed in many ways: slowly at first, with pauses, and so on. All of these are different elements of `Path a b`. Requiring constant speed leaves exactly one path for each geometric shortest curve. The next definition counts shortest paths, so this matters.
- **`edist s t`** is the distance $|s - t|$ between two parameters, as an element of $[0, \infty]$.
- **A path from a point to itself** is shortest exactly when all its points are at distance $0$ from each other. On a polyhedron that is the constant path.
- **Length is not mentioned.** A path with this property has length $\dist(a, b)$, the smallest possible, but the definition does not need a notion of length.
:::

## The cut locus

@decl SourceAbstract.Mesh.cutLocus

Fix a point of the surface, the *source*. A point $x$ is reached in two ways when there are two different shortest paths from the source to $x$. The cut locus of the source is the closure of the set of such points.

::: check
- **`p ≠ q` compares paths as functions.** Because shortest paths have constant speed, two of them are different exactly when they are different curves.
- **Why the closure.** On a convex polyhedron the cut locus is a tree. Its branches consist of points reached in two or more ways. Its leaves are the vertices of the polyhedron, and a vertex is reached by only one shortest path. Without the closure the leaves would be missing, and the cut locus would not be a closed set. The docstring makes the same remark.
- **The closure is taken in the quotient topology** of the surface.
- **The source itself** is not in the cut locus when it is not a vertex: a small disk around it is flat, shortest paths inside it are unique, and the source is not in the closure.
:::

These facts about the shape of the cut locus on a convex polyhedron go back to the study of shortest paths on polyhedra by @sharir1986, where the points reached in several ways are called ridge points, and are presented in the book of @demaine2007. They are stated here for orientation. The abstract file does not prove them, and the source-unfolding theorem does not need them in its statement: it speaks about the cut locus only through the definition above.

@viz source {"solid": "cube"}

In the figure, the cut locus of the source is drawn in orange on the solid. Move the source: the cut locus always reaches all eight corners. The planar picture on the right is the subject of [Part II](part-source.html).
