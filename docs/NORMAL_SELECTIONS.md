# Normal selections, clipped extensions, and compatible forests

The normal-selection, clipped-extension, and compatible-forest constructions are
implemented, including bounded embedded cut forests. They prepare the geometric
input for the Fewest Nets development argument. Supported fine-edge forests now
give flat intrinsic cut disks and local isometric developments. Gap-grafting
nonoverlap and counting remain to be proved.

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

## Embedded cuts and the next bridge

- [x] Embed every original whole seam in the intrinsic surface and identify its
  exact projected straight segment.
- [x] Realize the compatible finite parents as an embedded straight rooted forest:
  distinct open edges are disjoint and avoid every original vertex.
- [x] Include the complete terminal rays in a pairwise disjoint family of open
  cut pieces, handling coincident rays and first contacts.
- [x] Construct a common envelope level strictly above all original vertices.
  Truncate each terminal ray at its actual positive-time level intersection.
- [x] Prove the resulting finite straight graph is a forest with exactly one
  boundary root per tree. Precisely its new leaves lie on the actual sublevel
  frontier; all open edges lie in the interior.
- [x] Preserve original selected interior parents exactly and retain coverage of
  every actual positive-curvature vertex on physical extension meshes.
- [x] Construct a conforming physical mesh respecting every original triangle
  line and cut segment, including endpoint constraints; cover each segment
  exactly by whole fine edges and locate actual removed seams.
- [x] Use local common-potential growth to select supported increasing fine-edge
  parents. Derive their boundary-rooted cut forest and actual intrinsic cut disk.
- [x] Cover all positive curvature on that mesh, prove every retained interior
  copy is flat, and construct a rigid locally isometric development.
- [x] Prove that selected fine cut seams are exactly the full prescribed cut
  network; the fine forest omits none of those seams.
- [x] Prove every fine parent follows one oriented coarse segment and transfer
  whole-path length estimates to all fine parent histories up to the boundary.
- [ ] Construct complete one-ended forest cuts and intrinsic polygonal gaps.
- [x] Prove completeness of finite noncompact gluings from compatible uniformly
  Lipschitz cell heights whose sublevels are compact.
- [ ] Construct those heights on the actual gap end cells.
- [x] Prove that a simply connected flat boundary gluing of finitely many closed
  convex planar cells admits a surjective global isometry to the plane. Derive
  local homeomorphisms, complete-cell rigidity, and the covering argument.
- [ ] Construct the actual grafted gluing and prove its local Euclidean regularity
  and simple connectedness, then apply the global theorem to obtain nonoverlap.

Start with [`truncatedCutEmbedding`](../Unfoldings/Roof/TruncatedCutEmbedding.lean).
Its hypotheses are the constructed compatible routing, no original slope on the
clipping polygon boundary, and any level above the original vertex heights;
[`exists_truncation_level`](../Unfoldings/Roof/TerminalTruncation.lean) supplies
such a level. An inner slope disk makes this level section compact by the existing
coercivity theorem. No cut-disk or nonoverlap conclusion is assumed in this API.

The remaining noncompact step needs cells with controlled unbounded ends,
completed cut metrics with distinct banks, and actual metric gap insertion.
The existing finite triangle gluing and flat-disk development theorems provide
parts of that argument, but do not by themselves prove it.

The mesh result is
[`exists_compatibleMesh_development`](../Unfoldings/Roof/CompatibleMeshForest.lean).
It constructs supported fine-edge cuts, their intrinsic disk, and a local isometric
development; it does not assert nonoverlap. The supporting finite physical model
and routing are constructed by the earlier APIs. The generic metric lemma
[`completeSpace_of_compact_sublevels`](../Unfoldings/Metric/CoerciveGluing.lean)
also applies to unbounded cells; its cellwise height hypotheses still need to be
verified for the eventual grafted surface.

The global metric theorem is
[`exists_global_planar_isometry`](../Unfoldings/Metric/FlatPlanarGluing.lean).
It allows unbounded closed convex cells and assumes only boundary identifications,
local metric Euclidean charts, and simple connectedness (with local path
connectedness). It constructs the development and proves its global isometry;
cellwise rigidity, quotient completeness, a covering map, and nonoverlap are
not supplied as conclusions disguised as hypotheses. The finite complete cell
cover gives a closed map with finite fibers, so this proof avoids a separate
continuation-to-infinity argument. The actual gap construction must still
establish its geometric and topological inputs.

Exact network retention is
[`compatibleMesh_retain_eq_prescribed`](../Unfoldings/Roof/CompatibleMeshRetention.lean).
Thus [`exists_prescribedCompatibleCut_development`](../Unfoldings/Roof/PrescribedCompatibleCutDisk.lean)
constructs the intrinsic flat disk for all prescribed cuts, rather than an
unspecified supported subforest. The proof uses the unique forward coarse edge
and the actual fine-edge embedding to force every prescribed seam into the
selected parent forest. Fine parent histories follow the original routing and
retain its length constant.

## Heading perturbations and actual hinge openings

[HeadingPerturbation](../Unfoldings/Geometry/HeadingPerturbation.lean) proves the
mesh-independent chord estimate and the explicit perturbed radial and length
constants. [SuffixOpening](../Unfoldings/Geometry/SuffixOpening.lean) rotates each
actual bank suffix about its current hinge, preserving translations and link
lengths. [OpeningBudget](../Unfoldings/Geometry/OpeningBudget.lean) controls all
these rotations by their total absolute angle. Curvature spent once bounds that
budget; signed original-curvature comparisons have oscillation at most twice
the total curvature. The geometric saved-frontier fan invariant, the comparison
with intrinsic banks, and construction of positive Jordan gaps remain open.

## Polygonal banks and source-rotation gaps

[PolygonalRay](../Unfoldings/Geometry/PolygonalRay.lean) retains a finite chain
and its actual straight infinite tail, without imposing nonoverlap. Source-radial
tests prove the carrier a proper embedded half-line, parameterized by its exact
radius. [PolygonalRayOpening](../Unfoldings/Geometry/PolygonalRayOpening.lean)
extends actual hinge rotations to the tail and preserves radial monotonicity
under the quantitative opening budget.

[PolygonalRayFrame](../Unfoldings/Geometry/PolygonalRayFrame.lean) constructs an
ambient plane homeomorphism that straightens the bank. Its image of a closed
sector is an actual source-rotation gap: closed, with nonempty interior and
frontier exactly the two polygonal banks, meeting only at their source.
[UnboundedArrangement](../Unfoldings/Geometry/UnboundedArrangement.lean) removes
the compactness restriction on finite affine-boundary cell decompositions.
[PolygonalGapCells](../Unfoldings/Geometry/PolygonalGapCells.lean) constructs the
actual supporting lines and a finite closed full-dimensional convex cover of
each source-rotation gap, with pairwise-disjoint cell interiors.

The source-rotation gap is the first case. Nesting successive internal hinge
openings, saved-frontier fan bookkeeping, and the intrinsic graft construction
remain to be proved before claiming compatible-cut nonoverlap.

## Internal hinge gaps

[HingeGap](../Unfoldings/Geometry/HingeGap.lean) identifies the exact old and
moved infinite suffixes as the gap banks. [SmallHingeGap](../Unfoldings/Geometry/SmallHingeGap.lean)
proves that a sufficiently small opening stays clear of the prefix kept fixed.
The proof controls every intermediate rotation with the original radial and
length constants, then sweeps the whole gap by these actual banks.

These results treat individual hinge gaps. Nesting multiple openings and the
intrinsic saved-frontier construction remain open.

## Intrinsic polygonal gap metrics

[RotationGapMetric](../Unfoldings/Geometry/RotationGapMetric.lean) constructs the
actual intrinsic polygonal metric on each gap. The proved finite convex cell
cover gives completeness and agreement with the planar topology, including the
banks. An explicit closed-sector homeomorphism gives contractibility and finite
route distances; every interior point has a metric-ball Euclidean chart.

The general [PolygonalClosedCover](../Unfoldings/Metric/PolygonalClosedCover.lean)
result applies to unbounded finite closed convex-cell regions as well.

## Length-weighted radial blocks

[RadialBlockBounds](../Unfoldings/Geometry/RadialBlockBounds.lean) derives chord,
radial, and length bounds from length-weighted polar-block comparisons, allowing
variable intrinsic link speeds and unbounded total polar winding. The relative
chord error is `C*(S-1) + S*B*C*(1+C*K/δ)`.

[ChainPolarVariation](../Unfoldings/Geometry/ChainPolarVariation.lean) proves the
geometric weighted variation estimate from actual radial progress and prefix
length bounds, with the exact factor `K = sqrt(1-γ²)`. The remaining geometric
input is the one-sided intrinsic-bank turn comparison, obtained in the paper
using radial-wedge Jordan closures. It is still an explicit hypothesis here.

## Radial-wedge Jordan closures

[RadialWedgeClosure](../Unfoldings/Geometry/RadialWedgeClosure.lean) constructs
the actual three-segment closure of a radially ordered path in any pointed
positive-span wedge. The proof derives a simple path parametrization, constructs
an outward closing point beyond a supporting side, and proves every required
segment intersection before applying Jordan arc concatenation.

[ConvexCellRegion](../Unfoldings/Geometry/ConvexCellRegion.lean) constructs exact
face selections for regular closed regions when full convex-cell interiors
avoid the frontier. The remaining turn-comparison bridge must apply this to
an actual physical mesh and identify its boundary fans.

## Geometric Jordan angle balance

[JordanAngleBalance](../Unfoldings/Cap/JordanAngleBalance.lean) proves that the
actual boundary-fan excess along an interior Jordan curve equals the angular
curvature strictly inside its constructed whole-face filling. The cap mesh must
respect the curve; full-star incidence and the exact face selection are proved.
No Euler formula or supplied region-disk certificate is used.

The next bridge constructs the respecting physical mesh for each polygonal
closure and identifies the path and connector heading changes with these fans.

## Constructed closure meshes

[PolygonalClosureMesh](../Unfoldings/Roof/PolygonalClosureMesh.lean) constructs
a conforming physical cap refinement respecting every path and closing link.
The complete proper equation family and triangle-interior curve avoidance are
proved. The exact geometric Jordan angle balance applies to this constructed
mesh; its footprint and original spatial support labels are retained.

## Intrinsic Jordan fans

[JordanIntrinsicDisk](../Unfoldings/Cap/JordanIntrinsicDisk.lean) constructs the
actual whole-face intrinsic disk, with projection a homeomorphism onto the
closed Jordan domain. [JordanFanAngles](../Unfoldings/Cap/JordanFanAngles.lean)
identifies each of its vertex fans with exactly the original selected corners,
for intrinsic angles and arbitrary projected corner weights. No fan or disk
certificate is assumed.

## Ordered bank turn comparison

[JordanContourTurns](../Unfoldings/Cap/JordanContourTurns.lean) proves the exact
intrinsic/projected exterior-turn comparison in the constructed contour order.
[JordanBankTurnBounds](../Unfoldings/Cap/JordanBankTurnBounds.lean) reduces a
bank portion's error to enclosed curvature and aggregate closing-link error.
[ComplementaryBankTurns](../Unfoldings/Cap/ComplementaryBankTurns.lean) controls
switching sides by the actual original path curvature. The closing-link error
still needs its geometric section and endpoint estimates.
