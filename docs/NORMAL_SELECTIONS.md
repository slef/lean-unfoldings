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
- [ ] Construct the complete upper roof of an actual convex polyhedron, retaining
  original triangles and seam classes, including at silhouette vertices.
- [ ] Allow every containing hemisphere by constructing an orthogonal frame.
- [ ] Prove intrinsic disks for the original whole-edge spherical normal components.

## Exact clipped extension

- [ ] Construct the finite convex dual and its clipping to a compact slope polygon.
- [ ] Preserve each selected original whole face with exactly its original domain.
- [ ] Identify the strict difference from the boundary-slope envelope with the
  interiors of the whole-face selected components.
- [ ] Identify every positive-curvature extension vertex and its clipped normal cell.
- [ ] Prove constant-cell exterior rays and their avoidance of closed selected faces.

## Compatible common-potential forests

- [ ] Choose original outgoing edges from the active potential slope.
- [ ] Prove strict potential progress and one boundary root per restricted tree.
- [ ] Construct finite compatible exterior continuations, including root contacts.
- [ ] Bound every incoming history at every merger by the same active slope.
- [ ] Derive positive radial margins and subpath length constants on whole paths.
- [ ] Cover all extension curvature and preserve the original-edge restrictions.

These are construction goals. No final theorem may take the desired extension,
forest, or history bounds as an unexplained certificate.
