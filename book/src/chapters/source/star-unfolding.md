# The star unfolding

The source unfolding cuts the surface along the cut locus and keeps the shortest paths whole. The *star unfolding* does the opposite. It cuts along a shortest path from the source to every vertex, and keeps the cut locus whole. It is the second general unfolding of convex polyhedra [@demaine2007].

::: todo Not yet formalized
The library does not yet define the star unfolding, and nothing in this chapter is checked by Lean. The chapter records what the definition and the theorem should say, so that they can be compared with the source unfolding. The target is the first entry of the repository's [roadmap](https://github.com/slef/lean-unfoldings/blob/main/ROADMAP.md).
:::

@viz source {"solid": "dodecahedron", "unfolding": "star"}

On the left, the orange lines are shortest paths from the source to the vertices, and the dashed lines are the cut locus. On the right, the surface has been cut along the orange paths and laid flat. The menu switches between this and the source unfolding of the same solid from the same source.

## The construction

Let $x$ be a point of a convex polyhedron with $n$ vertices, and suppose that exactly one shortest path joins $x$ to each vertex. This holds for all $x$ outside a set of area zero. Cut the surface along these $n$ paths.

- **The cut surface is a disk.** The cuts form a tree with $x$ at its centre, and a sphere cut along a tree is a disk.
- **The disk is flat inside.** The surface of a polyhedron is flat except at its vertices, and every vertex is now on the boundary of the disk.

A flat disk can be developed: there is a map to the plane that preserves distances near every point. Each cut has two sides, so the outline of the development has $2n$ sides. Its corners are the $n$ vertices, and between them $n$ copies of the source, one in each angle between two consecutive cuts. The angles at the copies of the source add up to $2\pi$.

What is not clear is that the development does not overlap itself.

::: note The theorem of Aronov and O'Rourke
Let $x$ be a point of a convex polyhedron with exactly one shortest path to each vertex. Cut the surface along these shortest paths. Then the cut surface develops in the plane without overlap, onto a simple polygon. The cut locus of $x$ develops onto the part inside the polygon of the Voronoi diagram of the images of $x$ [@aronov1992].
:::

The second sentence says that a point of the polygon folds to a point of the surface whose distance from $x$ is the distance in the plane to the nearest image of $x$. The figure shows this: point at the net, and the blue segment starts at the image of the source in the same region of the dashed diagram.

## Compared with the source unfolding

Cut the surface along the cut locus and along the shortest paths to the vertices, both. It falls into $n$ pieces. Each piece is bounded by two consecutive shortest paths and by the part of the cut locus between the two vertices they reach.

- The source unfolding joins the $n$ pieces around the source. The shortest paths to the vertices become interior segments, and the cut locus becomes the outline.
- The star unfolding joins the same pieces along the cut locus. The cut locus becomes interior, and the shortest paths to the vertices become the outline.

Each piece has the same shape in both. Switch the menu of the figure between the two unfoldings to see the pieces move.

| | Source unfolding | Star unfolding |
|---|---|---|
| Cuts | the cut locus of the source | one shortest path from the source to each vertex |
| The source | one point, in the interior | $n$ points, corners of the outline |
| The vertices | on the outline | corners of the outline |
| Shape | star-shaped about the source | a simple polygon with $2n$ corners, in general not star-shaped |
| Distance from the source | distance to the origin | distance to the nearest image of the source |
| In this library | [[SourceAbstract.IsSourceUnfolding]], [Chapter 8](source-theorem.html) | not yet formalized |

## What a formal statement needs

The definition [[SourceAbstract.IsNetOf]] of [Chapter 6](nets.html) applies unchanged: a star unfolding is a net of the surface. The additional properties, in the style of [Chapter 7](source-unfoldings.html), would be the following.

1. A map `project` from the region to the abstract surface that agrees with the folding, as in properties a to c of a source unfolding.
2. `project` preserves distances near every interior point, as in property h.
3. The frontier of the region is a simple polygon. [Chapter 11](edge-unfoldings.html) has a definition of that, [[CapAbstract.SimplePolygon]], in the other abstract file.
4. `project` maps the frontier onto the union of $n$ shortest paths ([[SourceAbstract.Mesh.Shortest]]), one from the source to each vertex.
5. The distance on the surface from the source to `project z` is the least distance from $z$ to a point of the region that `project` sends to the source.

::: caveat Questions the statement must settle
- **Sources with several shortest paths to one vertex.** Cutting along one of them, for each vertex, still gives a flat disk. The theorem as stated above assumes that there is only one. The figure cuts one of them in this case, and its tests include such sources, but that is no argument.
- **Sources at vertices** are excluded from the source-unfolding theorem ([Chapter 8](source-theorem.html)) because the source must be an interior point of the net. Here the source is on the outline, so that obstruction is absent. A source at a vertex needs no cut to itself, and the count of corners changes; a first statement can exclude it.
- **Corners of the triangulation that are not vertices of the polyhedron** must not be cut to. The statement has to speak of the extreme points of the convex hull, as the hypothesis of the source-unfolding theorem does.
:::

## What the figure computes

The figure starts from its source unfolding ([Chapter 7](source-unfoldings.html)). It finds the vertices on the outline of that net, cuts the net along the segments from the origin to them, and moves the resulting pieces by rigid motions of the plane so that the two sides of every edge of the cut locus coincide. It does not use the theorem above.

The test suite of this book checks, for each solid in the menu and several sources, that there is one piece for each vertex, that the outline closes up and encloses the area of the surface, that no two pieces overlap, and that for every piece the nearest image of the source is its own. These are numerical checks on examples, including the regular dodecahedron and the truncated icosahedron. They are not a proof of anything.

## Where the result comes from

@aronov1992 proved that the star unfolding does not overlap, and that the cut locus develops onto a Voronoi diagram. @demaine2007 present the star unfolding together with the source unfolding, and trace the construction to Alexandrov.
