# Source unfolding

Take a convex polyhedron and a point on it, the source. Cut the surface along the cut locus of the source, the set of points that are reached by more than one shortest path. What is left can be laid flat in the plane without overlap, with the source at the origin, so that every shortest path from the source becomes a straight segment from the origin. This is the *source unfolding*. It exists for every convex polyhedron and every source, and it is one of the two general ways known to unfold a convex polyhedron without overlap when cuts across faces are allowed [@demaine2007].

Part II states this as a theorem of Lean, for sources that are not vertices.

| Chapter | Defines |
|---|---|
| [Chapter 6](nets.html) | convex polygons, and what it means for a planar region to be a net of a surface in space |
| [Chapter 7](source-unfoldings.html) | the additional properties that make a net a source unfolding |
| [Chapter 8](source-theorem.html) | the theorem, and what it does and does not say |

The definitions of [Part I](part-surfaces.html) are all used. The same file, `Unfoldings/Source/Abstract.lean`, contains them.
