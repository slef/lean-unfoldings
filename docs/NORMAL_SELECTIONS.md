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

These results treat individual hinge gaps. The finite-trace result below now
proves interior nonoverlap of successive openings; the branching saved-frontier
construction remains open.

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

## Canonical intrinsic bank rolling

[BoundaryRolling](../Unfoldings/Complex/BoundaryRolling.lean) constructs an actual
planar chain using intrinsic bank lengths and real fan turns, including for
curved Jordan patches. Its [development bridge](../Unfoldings/Development/BoundaryRolling.lean)
proves exact agreement with developed edges and positions when a global
facewise development exists; in that case the full contour closes.

## Projected metric and exact bank order

[AffineProjection](../Unfoldings/Complex/AffineProjection.lean) constructs a
separate projected metric complex. It retains the original seam classes,
vertex names, directed banks and complete contour order, with exact projected
fan angles. Separated actual projected triangles supply its global identity
development, allowing the same rolling API to describe the geometric bank.

## Actual real bank headings and speeds

[JordanRollingBounds](../Unfoldings/Cap/JordanRollingBounds.lean) applies the
geometric Jordan comparison to real unreduced headings of actual rolled bank
portions. [JordanBankStretch](../Unfoldings/Cap/JordanBankStretch.lean) proves
the exact edgewise heading/speed factorization and bounds stretch between one
and reciprocal normal height. These are the actual bank data needed by the
length-weighted radial estimates. Geometric closing-link bounds are still open.

## Generic closure incidences

[VertexAvoidingWedgeClosure](../Unfoldings/Geometry/VertexAvoidingWedgeClosure.lean)
constructs actual generic source and closing points, preserving radial progress
and Jordan simplicity. All three closing links avoid prescribed vertices
except their allowed fixed endpoints. Both new corners avoid any prescribed
finite affine supports, including the original mesh lines. Endpoint trimming
and geometric intrinsic section-turn estimates still need to be connected.

## Trimmed bank endpoints

[GenericEndTrimming](../Unfoldings/Geometry/GenericEndTrimming.lean) chooses
endpoints strictly inside the first and last actual links, avoiding prescribed
vertices. Every intermediate original corner, normalized direction, turn and
intrinsic/projected edge factor is retained. Carrier containment and radial
progress follow from exact increasing edge subparametrizations.

## Fully regular closing lines

[GenericBankClosure](../Unfoldings/Geometry/GenericBankClosure.lean) combines
trimming and generic closure construction. Every original bank turn remains;
all three complete extended closing lines avoid the prescribed vertices. This
provides the regularity input of the existing actual section-trace API.

## Constructed intrinsic straight-section turns

[IntrinsicSectionTurns](../Unfoldings/Cap/IntrinsicSectionTurns.lean) constructs
each regular section crossing's actual outward hinge turn, proves agreement
with any retained development, and bounds the total by `2φ` independently of
mesh size. The paper's sharper `2φ sin φ` bound remains open; the current bound
is useful for a qualitative small-tilt comparison.

## Actual fan turn contraction

[JordanVertexTurnBound](../Unfoldings/Cap/JordanVertexTurnBound.lean) bounds each
actual intrinsic Jordan boundary fan's absolute exterior turn by its genuine
spatial bend. The proof uses both sides of the original corner link and applies
to reflex fans and arbitrary-valence flat subdivision vertices. Ordered
straight-connector summation and corner distortion estimates remain open.

## Straight-link fan errors

[JordanStraightVertex](../Unfoldings/Cap/JordanStraightVertex.lean) proves that
the actual contour error on a straight projected bank is bounded by its spatial
bend. Its selected projected fan is exactly a halfplane, so the projected
exterior turn vanishes. This applies to actual subdivision vertices as well.

## Actual straight boundary sections

[BoundarySectionConstruction](../Unfoldings/Cap/BoundarySectionConstruction.lean)
constructs physical traces from actual projected bank coordinates and adjacency.
[JordanStraightSection](../Unfoldings/Cap/JordanStraightSection.lean) bounds the
sum of absolute contour fan errors on a straight interval by `2φ`, including
subdivision vertices. Deriving those ordered intervals from the constructed
three-link closure, and bounding its closing corners, remain open.

## Uniform corner comparison

[RelativeFaceAngleError](../Unfoldings/Cap/RelativeFaceAngleError.lean) derives
relative angular distortion from actual projection length bounds and continuity.
[JordanCornerError](../Unfoldings/Cap/JordanCornerError.lean) sums it over actual
fans: one positive tilt makes every Jordan corner error arbitrarily small,
independently of valence and without generic-position assumptions.
[CyclicBoundarySection](../Unfoldings/Cap/CyclicBoundarySection.lean) also removes
the enumeration-origin restriction on ordered straight sections. The remaining
bank comparison must derive its closing-link contribution from actual geometry.

## Straight-link sums without traversal data

[ActiveSectionVariation](../Unfoldings/Cap/ActiveSectionVariation.lean) bounds
turning at arbitrary distinct collinear active-face contacts by `2φ`, using
actual disjoint inclination intervals.
[JordanSectionSet](../Unfoldings/Cap/JordanSectionSet.lean) applies this to any
selected contour vertex set with collinear positions and opposite projected
bank rays. No sorted order, adjacency or cyclic-interval data are inputs.
Deriving the ray condition from local straightness of the constructed curve
remains to be connected.

## Derived geometric bank comparison

[JordanClosingLink](../Unfoldings/Cap/JordanClosingLink.lean) derives each `2φ`
closing-link bound from the actual closed curve decomposition. Opposite bank
rays follow from local straightness and actual bank separation.
[RadialBankTurnComparison](../Unfoldings/Cap/RadialBankTurnComparison.lean)
bounds the geometric bank's error by `Ω + 6φ + 8πε`, with corners counted once.
[RadialBankThreshold](../Unfoldings/Cap/RadialBankThreshold.lean) makes that error
arbitrarily small at one positive tilt, independently of the input mesh.
[ClosureBankComparison](../Unfoldings/Roof/ClosureBankComparison.lean) applies it
to the actual physical closure-respecting refinement; its tilt and avoidance
properties are constructed. Relating these bank portions to successive saved
openings, proving nesting, and assembling the complete graft remain open.

## Short radial windows

[LocalHeadingBudget](../Unfoldings/Geometry/LocalHeadingBudget.lean) derives a
weighted heading bound from local polar windows, without a global heading cone.
[LocalRadialBlocks](../Unfoldings/Geometry/LocalRadialBlocks.lean) applies it to
actual radial margins and length bounds.
[RayWindowClosure](../Unfoldings/Geometry/RayWindowClosure.lean) constructs
supported Jordan closing links after genuine endpoint trims, from a short
source-ray angle sum. Internal vertices and turns are retained. Relating the
geometric bank sum to the actual rolled bank remains open.

## Completion across comparison connectors

[CompletionRegion](../Unfoldings/Roof/CompletionRegion.lean) constructs a cap
preserving the extended roof on any compact region.
[CompletedBankComparison](../Unfoldings/Roof/CompletedBankComparison.lean)
preserves the whole Jordan filling and derives a uniformly small geometric
bank error on that actual cap. Closing points may lie outside the original
footprint; flat input roofs are included.

## Actual marked contour correspondence

[JordanContourSegments](../Unfoldings/Cap/JordanContourSegments.lean) identifies
the actual Jordan curve with its consecutive physical bank segments and proves
that no open bank contains another contour vertex.
[MarkedClosureCompletion](../Unfoldings/Roof/MarkedClosureCompletion.lean)
constructs a completion with all four closing corners retained as actual mesh
vertices. [MarkedContourPartition](../Unfoldings/Roof/MarkedContourPartition.lean)
derives each entire bank's membership in the radial bank or one closing link.
The rolling interval and saved-opening correspondence remain to be extracted.

## Actual cyclic bank rolling

[JordanContourBankInterval](../Unfoldings/Cap/JordanContourBankInterval.lean)
now extracts the geometric bank's strict cyclic interval from its two actual
contacts. [JordanCyclicRolling](../Unfoldings/Cap/JordanCyclicRolling.lean)
identifies its geometric turn sum with the actual intrinsic/projected real
heading change, retaining full turns.
[CompletedRollingComparison](../Unfoldings/Roof/CompletedRollingComparison.lean)
constructs a roof-preserving physical completion with uniformly small actual
bank rolling error. Transport to the original cut-bank histories and the
saved-opening invariant remain open.

## Constructed short-window comparison

[ShortWindowRolling](../Unfoldings/Roof/ShortWindowRolling.lean) now combines
the trim, closure, physical completion and actual rolling comparison. One
uniform positive tilt works for every short radial window.
[CompletionCombinedConstraints](../Unfoldings/Roof/CompletionCombinedConstraints.lean)
retains original-face sides and comparison lines on the same mesh, reusing the
existing metric equivalence for arbitrary retained original cuts. Transporting
the actual cut-bank fan histories and proving the saved-opening invariant
remain open.

## Exact polar windows and numerical tolerances

[PolarWindowRolling](../Unfoldings/Roof/PolarWindowRolling.lean) uses exactly
the strict polar-variation windows in the weighted heading estimates; source
rays and links come from the actual original subchain.
[RollingRadialBlockThreshold](../Unfoldings/Roof/RollingRadialBlockThreshold.lean)
chooses one positive heading tolerance and tilt controlling both actual rolling
and weighted radial loss, with the bounds valid at every smaller positive tilt.
These remain comparison models until bank-history transport is established.

## Exact angles through physical completion subdivisions

`CompletionFacePatch` develops the actual fine triangles in each original face
into exactly that original metric triangle, with genuine opposite-side hinges.
`TriangularFootprintAngles` identifies a triangular footprint's corner fan
with its actual Euclidean corner angle. Together these give the exact sum of
all physical fine corner angles over every original corner.

`SubdivisionCornerAngles` transports this conservation through an arbitrary
conforming cut-metric equivalence. Every original retained vertex copy has a
unique fine vertex above it, and its one-sided total angle is unchanged.
`CompletionSubdivisionAngles` proves these statements for the actual physical
completion, for every choice of retained original seams. The angle conservation
is proved from the mesh geometry, rather than supplied as a hypothesis.

The original cut-bank histories still need to be matched to the reference
Jordan banks. Saved-frontier fan bookkeeping, successive-gap nesting and the
complete intrinsic graft remain open.

## Straight inserted bank vertices and exact bank coverage

`CompletionInsertedAngles` identifies the actual cut fan at each new mesh
vertex inside an original face or open original bank. Its angle is respectively
`2 * pi` or `pi`; inserted bank vertices contribute exactly zero real exterior
rolling turn. This uses the exact cut metric and isolation of nonvertex bank
points, together with the physical face-patch geometry.

`CompletionBankSubdivision` covers each entire original cut bank by genuine
whole fine bank edges on its specified side. Their metric images are exactly
the original bank image, including endpoints. It reuses the general constrained
whole-edge subdivision theorem. `SubdivisionWeightedAngles` also preserves
arbitrary original face weights, hence every regional old-corner angle sum.

A traversal matching these banks to the reference Jordan contour and the
saved-frontier construction is still required; the gap-grafting nonoverlap
conclusion remains open.

## Actual directed refinements and real bank rolling

`FiniteIntervalPartition` and `SegmentPartitionOrder` construct the unique
increasing order of a finite genuine segment partition. `CompletionBankOrder`
proves that physical fine pieces of an original side satisfy these hypotheses.
`CompletionDirectedBank` identifies this order with the actual intrinsic
boundary successor, with no bank repeated in either direction.

`CompletionBankRolling.exists_original_cutBank_straight_roll` constructs the
entire directed fine refinement of every original cut side. It reaches the
correct original endpoints and has exactly zero extra real heading on every
prefix. `original_bankEnd_totalAngle_at_old_corner` also identifies endpoint
fans with their original one-sided cut fan angles, including branching cuts.
These results concern actual cut metric copies, not angles modulo a full turn.

The remaining comparison must match the original path's selected fans to the
reference Jordan bank, then control the saved-frontier history and successive
gaps. The complete intrinsic graft and final nonoverlap are still open.

## Unreduced subtree parent-bank holonomy

`Complex/SubtreeRolling.exists_subtree_real_bank_heading` chooses the actual
entering bank of any selected nonroot subtree and its actual opposite exit
bank. Rolling the original cut contour from that entrance gives real exit
heading plus `pi` exactly equal to the descendant curvature sum. The proof
uses the actual one-sided original fan turns and includes all branching copies.
It does not pass through angles modulo a full turn.

`Cap/SubtreeRealHeading` bounds this actual correction between zero and total
cap curvature. `CyclicRegionTurns` proves the additive finite-region
cancellation, and `FiniteCyclicTurns` applies it to genuine real heading prefixes.
Matching these corrections to the saved-frontier history still remains.

## Parent membership changes and fine-vertex radial margins

`SubtreePotentialWeights` telescopes original parent differences along each
root path before summing nested descendant weights. `SubtreeBankPotential`
chooses actual opposite-bank rolling headings for all nonroots and bounds
any signed parent-membership-change sum by total cap curvature. No root-path
crossing-count certificate is supplied. Relating a saved-frontier history to
these changes remains a separate geometric task.

`ActiveRayProgress` proves that an actual maximizing slope cannot lose its
forward dot-product bound as we advance along a compatible straight piece.
This yields the alternative fine-vertex margin
`cos (2 * annularHistoryAngle (a / b) beta)` under the explicit stronger
condition `2 * annularHistoryAngle (a / b) beta < pi / 2`.
`AnnularFineMargin` proves positivity and chooses a positive routing width
before meshing whenever `arccos (a / b) < pi / 4`.

`CompatibleFineMargins` handles arbitrary partial histories and next steps,
including terminal rays. `CompatibleMeshMargins` applies it to actual selected
fine parent histories. `CompatibleSubhistoryMargins` gives the same bound at
every earlier fine anchor and whole-point radial monotonicity, including
sources inside edges. This avoids splitting a history at its last coarse
vertex. It does not assert the paper's sharper numerical threshold.

## Source-centered hinge-gap coordinates

Actual outward hinge sweeps now have continuous, injective circle contacts above
the hinge radius. [`hingeExteriorHomeomorph`](../Unfoldings/Geometry/HingeExteriorCoordinates.lean)
identifies the entire corresponding gap with the opening interval times the open
radius half-line. The gap meets the closed hinge-radius ball only at its hinge.
These results assume radial monotonicity throughout the actual opening; the
quantitative opening-budget theorem supplies that control for small openings.
[`strictMono_hingeCircleAngle`](../Unfoldings/Geometry/HingeCircleOrder.lean)
proves strict counterclockwise order of contacts within each actual hinge gap,
using its terminal-ray limit. Nonoverlap across successive gaps remains open.

[`openings_radial_contact_inner_pos`](../Unfoldings/Geometry/OpeningCircleThreshold.lean)
keeps contacts of actual opening sequences in a common open source halfplane
when `3 * openingBudget < radialMargin^2`. It assumes the opened bank is outward;
existing opening estimates supply that condition under their subhistory bounds.
The bound is independent of the number of fine edges. It does not yet establish
nonoverlap of the successive gaps.

## Nonoverlap of finite positive opening traces

[`exists_nonoverlapping_positive_opening_gaps`](../Unfoldings/Geometry/OpeningGapNonoverlap.lean)
constructs the actual successive hinge gaps and proves pairwise disjoint
interiors. More strongly, every earlier gap interior misses each later closed
gap. Inputs are original subhistory length and positive radial-margin bounds,
positive opening angles below pi, and the sufficient budgets
`D * openingBudget < radialMargin` and
`3 * openingBudget < radialMargin^2`.

The proof constructs all intermediate radial tests and a common angular frame;
no intermediate safe-bank or nonoverlap certificate is assumed. This is a
single-bank-trace theorem. The remaining application must construct and compare
the actual branching saved-frontier histories, identify their curvature events,
and assemble the complete intrinsic graft.

[`exists_subtree_residual_budget`](../Unfoldings/Cap/SubtreeResidualBudget.lean)
identifies actual unreduced parent-bank holonomy minus immediate-child
holonomies with the original junction curvature. Any distinct list of these
actual residuals spends at most total cap curvature. The remaining geometric
fan-surgery proof must identify the saved-frontier updates with these residuals.

## Complete two-bank Jordan regions

[`exists_positive_opening_trace_gap`](../Unfoldings/Geometry/PositiveOpeningTraceGap.lean)
constructs a geometric polygonal Jordan region between the exact original and
final banks of a trace whose first positive opening is at the source. It proves
the whole frontier identity, source-only bank contact, nonempty interior,
regular closedness, a finite convex-cell cover, intrinsic completeness and
contractibility. The intrinsic region is homeomorphic to a closed sector.

The remaining grafting step must identify the local gap corner angles as the
complements of the actual incident surface fans, then construct the saved
frontier surgery and the complete flat gluing. These are additional conclusions;
they are not included in the geometric Jordan-region theorem.

## Complete unbounded starting surface

[`wholeSurface_complete`](../Unfoldings/Geometry/SpatialEnvelopeWholeMetric.lean)
proves completeness of the intrinsic polygonal metric on the entire finite
support-plane envelope. Its actual closed convex spatial cells cover it, and
horizontal projection gives a homeomorphism to the plane. The surface is
contractible and has finite intrinsic distances. No outer truncation or
separate end-height certificate is needed for this starting-surface result.

The finite-cell route to the final global planar isometry uses completeness
of actual closed cells. Constructing the cut-and-grafted cells, their local
Euclidean charts and their global topology remains necessary.

[`closedCoverIsometryEquiv`](../Unfoldings/Metric/PolygonalCoverGluing.lean)
identifies the actual intrinsic region with its finite closed convex-cell metric
gluing, using actual coincident-point seams. It handles unbounded and redundant
cells and proves that no extra identifications arise. Thus the initial roof and
constructed Jordan gaps can share the gluing API without assuming a separate
metric compatibility certificate.

[`wholePlanarGluingIsometryEquiv`](../Unfoldings/Geometry/SpatialEnvelopeWholeGluing.lean)
gives the complete physical roof an exact planar-cell gluing model using its
actual rigid support-plane coordinates and physical coincidence seams. This
transfers the intrinsic metric and plane topology, including redundant supports.

[`exists_twoBankGap_boundary_gluing`](../Unfoldings/Geometry/TwoBankGapGluing.lean)
constructs a complete contractible finite planar-cell gluing of the actual
Jordan gap, with full-dimensional cells and boundary-only seams. Its explicit
isometry sends each cell point to that same physical point of the gap. Exact
complementary corner charts still have to be proved before graft flatness.

[`exists_wholePartition`](../Unfoldings/Geometry/SpatialEnvelopePartition.lean)
constructs full-dimensional unbounded roof partitions aligned to any prescribed
finite proper affine cut-support lines. Their physical-seam gluing has exactly
the complete intrinsic roof metric and plane topology; seams and prescribed
lines lie on actual cell frontiers. This supplies cells for the cut construction,
without yet constructing the duplicated cut banks or their local fans.

[`exists_tangentCell_ball_isometry`](../Unfoldings/Geometry/AffineArrangementConeChart.lean)
constructs exact local isometric coordinates on every finite affine cell,
using its active inequality cone. These are charts of individual cells; the
actual bank angles and compatibility of the assembled graft fan remain open.

[`PhysicalSeams`](../Unfoldings/Metric/PhysicalSeams.lean) supplies exact metric
quotients for finite selected closed physical attachment pieces. Finite closed
physical cells give completeness and the actual seam-quotient topology even
with unbounded seams. This supports cut-space construction while leaving the
choice and cyclic ordering of the actual retained bank pieces to be proved.

[`PolygonalCut`](../Unfoldings/Metric/PolygonalCut.lean) constructs a complete
metric from closures of the actual uncut cell attachments, and recovers the
original intrinsic metric for an empty cut set.
[`exists_cutToPolygonal_ball_isometry`](../Unfoldings/Metric/PolygonalCutLocal.lean)
proves whole-ball restoration isometries away from closed cuts. These results
establish the metric construction; identifying its bank fans with the original
forest and filling their complementary angles remains necessary.

[`WholePartition.Cut`](../Unfoldings/Geometry/SpatialEnvelopeCut.lean) gives the
whole roof actual complete cut metrics in rigid planar cells, with boundary-only
seams and exact whole-ball restoration away from closed horizontal cuts. The
remaining bank-fan topology proof must identify the quotient copies at cut
points, their cyclic sectors and the original forest banks before grafting.

[`mem_closure_attachment_iff`](../Unfoldings/Geometry/AffineArrangementGerm.lean)
characterizes actual retained attachments at a cut point by common tangent
directions outside all cut-piece germs. This is an exact geometric test for
finite affine-cell cuts. Converting the resulting adjacency into the original
cyclic forest bank fans remains necessary.

[`carrier_eq_iUnion_closedChamber`](../Unfoldings/Geometry/PolygonalRayInequalities.lean)
represents the exact original polygonal cut carrier by finite affine cells,
including its entire terminal ray. Thus the local active-cone attachment tests
apply to the original geometry without substituting a proxy cut set.

[`mem_closure_family_attachment_iff_unit`](../Unfoldings/Geometry/PolygonalRayGerm.lean)
tests actual retained attachments at polygonal cut points on the unit direction
circle. It uses the exact original edges and whole terminal rays, including
finite branching families. Cyclic ordering of the resulting bank fans remains open.

[`segment_cellGerm_start`](../Unfoldings/Geometry/SegmentEndpointGerm.lean) and
its terminal-endpoint counterpart identify the actual incident edge vectors in
the affine cut models. The terminal-ray source has the same exact outgoing-ray
model. These identifications retain the original geometric directions.

[`eventually_mem_parent_cuts_iff_directions`](../Unfoldings/Geometry/ParentCutGerm.lean)
identifies each original forest vertex's local cut with its actual labeled
outgoing parent ray and incoming child rays. Its unit directions form a finite
set. The cyclic order of the complementary bank sectors still has to be linked
to the metric corner fans.

[`segment_cellGerm_interior`](../Unfoldings/Geometry/SegmentInteriorGerm.lean)
and [`ray_cellGerm_interior`](../Unfoldings/Geometry/RayInteriorGerm.lean)
identify all ordinary cut points with the original two-sided edge line. Every
segment or terminal-ray germ is supported on those original directions.
