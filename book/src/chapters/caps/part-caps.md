# Edge unfolding of caps

An *edge unfolding* cuts a polyhedral surface only along its edges and lays the faces flat. Whether every convex polyhedron has an edge unfolding without overlap is a well-known open problem [@demaine2007]. @orourke2018 proved that it can be done for a class of surfaces: convex caps that are nearly flat and whose faces are acute triangles.

Part III states that theorem in Lean. Its abstract file, `Unfoldings/Cap/Abstract.lean`, is independent of the file used in [Part I](part-surfaces.html) and [Part II](part-source.html): it has its own namespace, `CapAbstract`, and defines everything it needs again.

| Chapter | Defines |
|---|---|
| [Chapter 9](cap-meshes.html) | the mesh again, surfaces obtained by keeping only some seams, boundary edges, and the acute margin |
| [Chapter 10](caps.html) | horizontal projection, the footprint, and a convex cap |
| [Chapter 11](edge-unfoldings.html) | simple polygons, and edge unfoldings whose outline is a simple polygon |
| [Chapter 12](cap-theorem.html) | the theorem, and what it does and does not say |

Unlike the source unfolding, an edge unfolding needs no distance on the surface, no shortest paths and no cut locus. The definitions of this part are combinatorial and Euclidean.
