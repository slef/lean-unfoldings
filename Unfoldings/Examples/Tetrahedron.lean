module

public import Unfoldings.Examples.Tetrahedron.Source
public import Unfoldings.Examples.Tetrahedron.Cuts

/-!
# A complete concrete tetrahedron benchmark

The four declared faces and six paired edges form the certified convex boundary
of the tetrahedron with vertices `(0,0,0)`, `(1,0,0)`, `(1,1,0)`, `(1,1,1)`.
`sourceUnfolding` instantiates the full source-unfolding theorem at a crease
midpoint. `baseCutDisk` constructs the disk from a specific three-edge cut tree.
The no-cuts and all-seams-cut configurations are proved not to be disks.
-/
