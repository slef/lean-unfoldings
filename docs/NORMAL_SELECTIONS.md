# Normal selections, clipped extensions, and compatible forests

These three construction milestones are implemented. They prepare the geometric
input for the Fewest Nets development argument; they do not yet prove its
nonoverlap or counting theorems.

## Start here

| Result | Main API |
| --- | --- |
| Intrinsic disks for whole-polyhedron normal selections | [`ConvexBoundary.spherical_normal_selection_component`](../Unfoldings/Polyhedron/NormalSelection.lean) |
| Exact finite extension preserving original faces | [`ConvexRoof.clippedPhysicalModel`](../Unfoldings/Roof/ClippedPhysicalCurvature.lean) |
| Strict region equals selected component interiors | [`ConvexRoof.clippedExtension_strict_region_iff_component`](../Unfoldings/Roof/SelectedStrictRegion.lean) |
| Construct compatible original-edge and exterior routing | [`ConvexRoof.exists_compatiblePotentialRouting`](../Unfoldings/Roof/CompatiblePotentialRouting.lean) |
| One boundary root per component tree | [`CommonPotentialRouting.component_rootedForest`](../Unfoldings/Roof/ComponentPotentialForest.lean) |
| Uniform bounds on whole paths and subpaths | [`CompatiblePotentialRouting.follows_length_bound`](../Unfoldings/Roof/CompatiblePotentialPaths.lean), [`follows_radial_margin_along_outgoing`](../Unfoldings/Roof/CompatiblePotentialWholePaths.lean) |

## Spherical normal selections

- [x] Construct actual outward unit supporting normals for all original triangles,
  including coplanar subdivisions.
- [x] Recover the body from the original face halfspaces and construct its exact
  upper graph over the full convex projected footprint.
- [x] Build the complete upper roof using the original upward triangles and seams,
  including silhouette vertices and vertical neighboring faces.
- [x] Construct orthogonal frames for arbitrary containing hemispheres and prove
  spherical convexity becomes gnomonic convexity.
- [x] Identify selected adjacency with original whole seams and prove intrinsic
  component disks, injective projections, and Jordan frontiers.

See [NormalSelection](../Unfoldings/Polyhedron/NormalSelection.lean) and
[UpperRoof](../Unfoldings/Polyhedron/UpperRoof.lean). Selected component footprints
can be nonconvex.

## Exact clipped extension

- [x] Construct the finite dual from actual lifted original roof vertices and clip
  its conjugate to a compact slope polygon.
- [x] Preserve all selected closed original triangles and the exact full physical
  supporting-face domains, including coplanar subdivisions.
- [x] Construct a finite polyhedral representation using dual arrangement triangles.
- [x] Identify the strict difference from the boundary-slope potential exactly with
  selected component interiors when no original face slope lies on the polygon boundary.
- [x] Identify surviving normal cells as clipped original cells.
- [x] Construct conforming physical meshes respecting prescribed finite lines.
  An inner slope disk makes every horizontal section compact.
- [x] Prove that every positive intrinsic curvature vertex is an original lifted
  corner. This uses actual angular defect, with no tilt restriction.
- [x] Prove constant active cells on open exterior rays and avoidance of every
  closed selected original face.

The principal modules are [ClippedExtension](../Unfoldings/Roof/ClippedExtension.lean),
[SelectedStrictRegion](../Unfoldings/Roof/SelectedStrictRegion.lean), and
[ClippedPhysicalCurvature](../Unfoldings/Roof/ClippedPhysicalCurvature.lean).

## Compatible common-potential forests

- [x] Choose original incident edges within half the selected projected corner bound.
- [x] Construct strict-potential original-edge forests and restrict the same choices
  to every selected component, with exactly one boundary root per restricted tree.
- [x] Construct consistent outward directions, stop at first root contacts, and
  attach the exterior forests to the original ones.
- [x] Prove retained open exterior pieces are disjoint, including coincident-ray cases,
  and that each final component has a straight contact-free terminal ray.
- [x] Control every incoming merger history by every active potential slope there.
- [x] Prove length and positive radial margins on whole paths, including arbitrary
  partial edges and unbounded terminal tails.
- [x] Construct the cut carrier, cover every positive-curvature extension vertex,
  keep the original selected edges, and avoid selected closed faces on open exterior rays.

For projected corner angles at most `2β` on selected faces, an annulus
`B_a ⊆ K ⊆ B_b` gives `C = b / (a cos β)` for subpath length. Write `ρ = a/b`
and `β' = arccos(ρ cos β)`. Under `ρ > tan β`, `β' + ζ < π/2`, and
`ζ ≥ arccos ρ`, the constructed directions have the positive radial margin
`min(cos(β + β'), cos(β' + ζ))`. No acuteness is required outside selected faces.
The API states the inner disk using an open ball; closedness supplies its closure.

No theorem assumes the desired extension, forest, or history estimates as an
unexplained certificate. The constructors build the data from the input geometry.

## Next target

Use these geometric forests in the intrinsic cut and development construction,
then prove the gap-grafting nonoverlap theorem. Normal-cover selection and Euler
counting for Fewest Nets follow that development theorem.
