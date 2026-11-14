# Normal selections and common-potential forests

The next target connects actual convex polyhedral boundaries to the paper's
whole-face normal selections, clipped extensions, and compatible forests.
The existing arbitrary-rim theorem assumes a convex projected footprint;
selected component projections need not be convex.

## Spherical normal selections

- [x] Construct actual outward unit supporting normals for all original triangles,
  including coplanar subdivisions: [SupportingNormals](../Unfoldings/Polyhedron/SupportingNormals.lean).
- [x] Recover the whole convex body from the original face halfspaces:
  [FaceHalfspaces](../Unfoldings/Polyhedron/FaceHalfspaces.lean).
- [x] Convert spherical convexity to gnomonic convexity and preserve closedness:
  [SphericalConvex](../Unfoldings/Geometry/SphericalConvex.lean).
- [x] Transfer the intrinsic component-disk theorem to spherical normal selections
  on an actual roof: [SphericalSelection](../Unfoldings/Roof/SphericalSelection.lean).
- [x] Construct the exact scalar upper graph over the full convex body projection:
  [UpperGraph](../Unfoldings/Polyhedron/UpperGraph.lean), using actual
  [upward face planes](../Unfoldings/Polyhedron/UpperPlanes.lean).
- [x] Construct the complete upper roof of an actual convex polyhedron, retaining
  original triangles and seam classes, including at silhouette vertices:
  [UpperRoof](../Unfoldings/Polyhedron/UpperRoof.lean).
- [x] Allow every containing hemisphere by constructing an orthogonal frame:
  [NorthFrame](../Unfoldings/Geometry/NorthFrame.lean).
- [x] Prove intrinsic disks for the original whole-edge spherical normal components:
  [NormalSelection](../Unfoldings/Polyhedron/NormalSelection.lean).

## Exact clipped extension

- [x] Construct the finite vertex conjugate and clipped conjugate of an actual roof:
  [ClippedExtension](../Unfoldings/Roof/ClippedExtension.lean).
- [x] Construct a finite polyhedral representation for polygon clipping, using
  actual arrangement triangles: [ClippedPolyhedral](../Unfoldings/Roof/ClippedPolyhedral.lean).
- [x] Preserve every selected original whole triangle and the exact full physical
  supporting-face domain, including coplanar subdivisions.
- [x] Identify `{G > h}` exactly with original domain points whose full normal cell
  lies inside the slope polygon, including unbounded rim normal cones:
  [ClippedStrictRegion](../Unfoldings/Roof/ClippedStrictRegion.lean).
- [ ] Identify that original normal-cell condition with the union of interiors of
  whole-face selected components under the no-boundary-gradient assumption.
- [x] Prove that full-dimensional extension normal cells occur only at actual
  original lifted corners; surviving normal cells are exactly clipped original cells.
- [ ] Connect that normal-cell statement to positive intrinsic curvature on a
  constructed spatial triangulation of the finite extension.
- [x] Prove constant-cell exterior rays, equality with the boundary potential, and
  avoidance of every closed selected original face:
  [ClippedExteriorRay](../Unfoldings/Roof/ClippedExteriorRay.lean).

## Compatible common-potential forests

- [x] Choose an original incident edge within half the projected corner bound of
  any requested direction: [MeshDirectionProgress](../Unfoldings/Geometry/MeshDirectionProgress.lean).
- [ ] Assemble those local choices into original-edge rooted forests.
- [ ] Prove strict potential progress and one boundary root per restricted tree.
- [ ] Construct finite compatible exterior continuations, including root contacts.
- [ ] Bound every incoming history at every merger by the same active slope.
- [ ] Derive positive radial margins and subpath length constants on whole paths.
- [ ] Cover all extension curvature and preserve the original-edge restrictions.

These are construction goals. No final theorem may take the desired extension,
forest, or history bounds as an unexplained certificate.
