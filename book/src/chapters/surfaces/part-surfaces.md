# Surfaces

Part I defines the objects that the source-unfolding theorem is about. All of it comes from one file, `Unfoldings/Source/Abstract.lean`.

A polyhedral surface is described the way one would describe a paper model before assembling it: a finite set of flat triangles, and a list of which edge is taped to which. Nothing in this description lives in space. Distances on the surface, shortest paths and the cut locus are all defined from the triangles and the taping alone. Space enters only at the end, when a convex polyhedron is defined as a way of placing the triangles.

| Chapter | Defines |
|---|---|
| [Chapter 1](meshes.html) | the plane, triangles, edges, and a mesh: triangles with paired edges |
| [Chapter 2](gluing.html) | points of a mesh, the gluing relation, and the surface as a quotient |
| [Chapter 3](distance.html) | the intrinsic distance of the surface |
| [Chapter 4](cut-locus.html) | shortest paths and the cut locus of a point |
| [Chapter 5](polyhedra.html) | a convex polyhedron: a placement of the mesh as the boundary of a convex body |
