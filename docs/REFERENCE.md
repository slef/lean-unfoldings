# Library reference

Start with the [README](../README.md) for the main result and a usage example.
The [plan](../PLAN.md) tracks implemented features and remaining work;
the [log](../LOG.md) records proof-development milestones.

## Module index

Modules are grouped by topic and sorted by name. Each link opens the Lean
source, including its module documentation and declarations.

- [Source unfoldings](#source-unfoldings)
- [Convex caps](#convex-caps)
- [Triangle complexes](#triangle-complexes)
- [Cuts and layouts](#cuts-and-layouts)
- [Metrics and gluing](#metrics-and-gluing)
- [Paths and geodesics](#paths-and-geodesics)
- [Convex polyhedra](#convex-polyhedra)
- [Cone geometry](#cone-geometry)
- [Euclidean geometry](#euclidean-geometry)
- [Topology and combinatorics](#topology-and-combinatorics)
- [Examples and core imports](#examples-and-core-imports)
- [Build and proof audit](#build-and-proof-audit)
- [Provenance](#provenance)

## Source unfoldings

| Module | Purpose |
| --- | --- |
| [Unfoldings.Source.ActualCut](../Unfoldings/Source/ActualCut.lean) | The actual cut complement, exact cut-locus boundary projection and constructed source-disk properties |
| [Unfoldings.Source.AmbientCoordinates](../Unfoldings/Source/AmbientCoordinates.lean) | Extend retained coordinates for local arguments, with proved agreement on the cut complement |
| [Unfoldings.Source.Bisectors](../Unfoldings/Source/Bisectors.lean) | Distinct shortest paths in a face interior determine distinct virtual-source images |
| [Unfoldings.Source.BoundaryImages](../Unfoldings/Source/BoundaryImages.lean) | Finite rigid representations of all shortest-path vectors in every endpoint face |
| [Unfoldings.Source.BoundaryLines](../Unfoldings/Source/BoundaryLines.lean) | The entire developed boundary lies on finitely many proper affine lines |
| [Unfoldings.Source.BoundaryQuotient](../Unfoldings/Source/BoundaryQuotient.lean) | Actual source-disk boundary-only quotient presentations with exact cut-locus boundary image |
| [Unfoldings.Source.BoundarySegments](../Unfoldings/Source/BoundarySegments.lean) | The entire source boundary is exactly a finite union of face-compatible segments |
| [Unfoldings.Source.ChartTrace](../Unfoldings/Source/ChartTrace.lean) | Construct the next affine chart trace for every nearby shortest path |
| [Unfoldings.Source.CompactPaths](../Unfoldings/Source/CompactPaths.lean) | Compactness of the complete shortest-path space by Arzela--Ascoli |
| [Unfoldings.Source.CompletedPieces](../Unfoldings/Source/CompletedPieces.lean) | Finite compact-graph rigid face cover of the whole completed source disk |
| [Unfoldings.Source.CompletedRadials](../Unfoldings/Source/CompletedRadials.lean) | Completed radial geodesics project to all original shortest paths, preserving source distance |
| [Unfoldings.Source.ConeLeaves](../Unfoldings/Source/ConeLeaves.lean) | All singular endpoints belong to the closure of actual ties; the slit set equals the cut locus |
| [Unfoldings.Source.ContinuousCoordinates](../Unfoldings/Source/ContinuousCoordinates.lean) | Continuous source vectors in the uniform path topology |
| [Unfoldings.Source.ConvexCoordinates](../Unfoldings/Source/ConvexCoordinates.lean) | Planar vectors distinguish all convex-boundary shortest paths |
| [Unfoldings.Source.ConvexCutLocus](../Unfoldings/Source/ConvexCutLocus.lean) | Unique shortest paths off the closed source cut locus |
| [Unfoldings.Source.ConvexDomainInterior](../Unfoldings/Source/ConvexDomainInterior.lean) | Exact characterization of source-domain interior by regular retained endpoints |
| [Unfoldings.Source.ConvexDomain](../Unfoldings/Source/ConvexDomain.lean) | Actual convex-boundary path-space homeomorphisms and surjective projection |
| [Unfoldings.Source.ConvexLocalIsometry](../Unfoldings/Source/ConvexLocalIsometry.lean) | Local source isometries at every regular retained convex-surface point |
| [Unfoldings.Source.ConvexOffCutCoordinates](../Unfoldings/Source/ConvexOffCutCoordinates.lean) | Constructed coordinates from convex-boundary input and a regular source |
| [Unfoldings.Source.Coordinates](../Unfoldings/Source/Coordinates.lean) | Constructed full-length source vectors and exact radial norms |
| [Unfoldings.Source.CutConnected](../Unfoldings/Source/CutConnected.lean) | Exact cut-locus boundary projection and connectedness of the actual closed cut locus |
| [Unfoldings.Source.CutContractible](../Unfoldings/Source/CutContractible.lean) | Contractibility of the cut locus and its constructed embedded graph carrier |
| [Unfoldings.Source.CutGraph](../Unfoldings/Source/CutGraph.lean) | An actual finite connected embedded straight graph with exact cut-locus carrier and original-face containment |
| [Unfoldings.Source.CutIntrinsic](../Unfoldings/Source/CutIntrinsic.lean) | Cut metric equals path distance in the original retained surface |
| [Unfoldings.Source.CutLocus](../Unfoldings/Source/CutLocus.lean) | Closed source cut locus and exclusion of a whole source ball |
| [Unfoldings.Source.CutMetric](../Unfoldings/Source/CutMetric.lean) | Actual source cut metrics, completion, boundary copies and boundary projection |
| [Unfoldings.Source.CutProjection](../Unfoldings/Source/CutProjection.lean) | The whole completed projection does not increase surface distance |
| [Unfoldings.Source.CutRetraction](../Unfoldings/Source/CutRetraction.lean) | Continuous retraction of the punctured original surface onto the actual cut locus |
| [Unfoldings.Source.CutSegments](../Unfoldings/Source/CutSegments.lean) | The actual closed source cut locus is exactly a finite straight network in original faces |
| [Unfoldings.Source.CutSupport](../Unfoldings/Source/CutSupport.lean) | Closed finite supports for all cut points, including cone leaves |
| [Unfoldings.Source.CutTree](../Unfoldings/Source/CutTree.lean) | The actual source cut locus is a finite embedded straight tree at every nonextreme source |
| [Unfoldings.Source.Disk](../Unfoldings/Source/Disk.lean) | Constructed disk and boundary-circle homeomorphisms for the actual source completion |
| [Unfoldings.Source.DomainBoundary](../Unfoldings/Source/DomainBoundary.lean) | Exact boundary projection onto the closed cut union singular points |
| [Unfoldings.Source.DomainDensity](../Unfoldings/Source/DomainDensity.lean) | Every proper radial prefix is interior; its closure is the whole compact domain |
| [Unfoldings.Source.DomainInterior](../Unfoldings/Source/DomainInterior.lean) | Regular unique endpoints give actual interior source vectors |
| [Unfoldings.Source.Domain](../Unfoldings/Source/Domain.lean) | Compact planar path images and continuous endpoint projection |
| [Unfoldings.Source.EndpointChart](../Unfoldings/Source/EndpointChart.lean) | An actual affine endpoint formula for all nearby shortest paths |
| [Unfoldings.Source.EndpointStability](../Unfoldings/Source/EndpointStability.lean) | Singleton fibers control every shortest path to nearby endpoints |
| [Unfoldings.Source.FaceAtlas](../Unfoldings/Source/FaceAtlas.lean) | Actual face motions are locally constant and develop every connected retained face region rigidly |
| [Unfoldings.Source.FaceMotionUniqueness](../Unfoldings/Source/FaceMotionUniqueness.lean) | Any local source-coordinate expression determines the actual selected face motion |
| [Unfoldings.Source.FacePathMotion](../Unfoldings/Source/FacePathMotion.lean) | Actual face motions stay fixed along all retained face paths |
| [Unfoldings.Source.FacePlacement](../Unfoldings/Source/FacePlacement.lean) | Constructed source-face motion agrees with all source vectors in the source ball |
| [Unfoldings.Source.FaceRouteMotion](../Unfoldings/Source/FaceRouteMotion.lean) | Actual source motions stay fixed along retained face-contained route pieces |
| [Unfoldings.Source.FiberWordMotion](../Unfoldings/Source/FiberWordMotion.lean) | Bounded seam words determine the actual motions of all copies of a retained point |
| [Unfoldings.Source.FiniteFibers](../Unfoldings/Source/FiniteFibers.lean) | Every endpoint has finitely many normalized shortest paths and boundary copies |
| [Unfoldings.Source.FiniteMotions](../Unfoldings/Source/FiniteMotions.lean) | A constructed finite global family contains every actual retained face motion |
| [Unfoldings.Source.HingePlacement](../Unfoldings/Source/HingePlacement.lean) | One actual rigid motion expresses source coordinates on both sides of an outward hinge |
| [Unfoldings.Source.Images](../Unfoldings/Source/Images.lean) | Construct finite virtual source images realizing all retained endpoint distances |
| [Unfoldings.Source.InitialTrace](../Unfoldings/Source/InitialTrace.lean) | Construct actual affine source traces on a whole path neighborhood |
| [Unfoldings.Source.InteriorHomeomorph](../Unfoldings/Source/InteriorHomeomorph.lean) | The actual flat retained surface is homeomorphic to the planar domain interior |
| [Unfoldings.Source.LocalFacePlacement](../Unfoldings/Source/LocalFacePlacement.lean) | Constructed rigid face patches at all retained points, including edges and flat vertices |
| [Unfoldings.Source.LocalIsometry](../Unfoldings/Source/LocalIsometry.lean) | Actual local distance preservation from constructed terminal charts |
| [Unfoldings.Source.Net](../Unfoldings/Source/Net.lean) | A finite nonoverlapping layout with exact source-domain footprint and folding maps |
| [Unfoldings.Source.OffCutCoordinates](../Unfoldings/Source/OffCutCoordinates.lean) | Continuous injective source coordinates on the cut-locus complement |
| [Unfoldings.Source.PathNeighborhood](../Unfoldings/Source/PathNeighborhood.lean) | Uniform stability in charts on whole compact time intervals |
| [Unfoldings.Source.PieceFormula](../Unfoldings/Source/PieceFormula.lean) | Finite actual rigid radial formulas through every whole shortest-path face piece |
| [Unfoldings.Source.PolygonalDomain](../Unfoldings/Source/PolygonalDomain.lean) | A finite cover of the source disk by compact convex polygons with disjoint interiors |
| [Unfoldings.Source.PolygonalPieces](../Unfoldings/Source/PolygonalPieces.lean) | Every source polygon folds rigidly into one original triangle, including its boundary |
| [Unfoldings.Source.PrefixCutAvoidance](../Unfoldings/Source/PrefixCutAvoidance.lean) | Every proper shortest-path prefix avoids the closed cut locus |
| [Unfoldings.Source.PrefixUniqueness](../Unfoldings/Source/PrefixUniqueness.lean) | Every proper prefix is unique, by continuation from the unchanged tail |
| [Unfoldings.Source.Prefixes](../Unfoldings/Source/Prefixes.lean) | Actual normalized shortest-path prefixes, including both endpoints |
| [Unfoldings.Source.ProjectionFibers](../Unfoldings/Source/ProjectionFibers.lean) | Exact source-projection interior, boundary, source fiber, and nontrivial boundary fibers |
| [Unfoldings.Source.RadialDomain](../Unfoldings/Source/RadialDomain.lean) | Exact prefix-vector scaling and star-shaped planar source images |
| [Unfoldings.Source.Radial](../Unfoldings/Source/Radial.lean) | Injectivity from uniqueness of radial lifts |
| [Unfoldings.Source.RegularDevelopment](../Unfoldings/Source/RegularDevelopment.lean) | Constructed nonoverlapping local isometries and radial geodesics on the retained interior |
| [Unfoldings.Source.RegularRegion](../Unfoldings/Source/RegularRegion.lean) | The flat retained region and explicit closed singular slit set |
| [Unfoldings.Source.RegularUnique](../Unfoldings/Source/RegularUnique.lean) | Unique paths to regular endpoints avoid the closed source cut locus |
| [Unfoldings.Source.RetainedRadials](../Unfoldings/Source/RetainedRadials.lean) | Construct all retained radial geodesics and prove exact developed straightness |
| [Unfoldings.Source.RoutePropagation](../Unfoldings/Source/RoutePropagation.lean) | Bounded finite-choice propagation of actual motions along complete retained routes |
| [Unfoldings.Source.SampleLine](../Unfoldings/Source/SampleLine.lean) | Exact initial chart straightness of the full-length source vector |
| [Unfoldings.Source.SeamEndpointTransition](../Unfoldings/Source/SeamEndpointTransition.lean) | Actual hinge transitions extend to retained seam endpoints, including flat vertices |
| [Unfoldings.Source.SeamTransition](../Unfoldings/Source/SeamTransition.lean) | Actual face motions use the outward hinge transition at nonvertex seam points |
| [Unfoldings.Source.ShortestPath](../Unfoldings/Source/ShortestPath.lean) | All actual shortest paths, retaining endpoint ties |
| [Unfoldings.Source.SourceBall](../Unfoldings/Source/SourceBall.lean) | The constructed coordinates are isometric on the whole source chart ball |
| [Unfoldings.Source.TaggedMotion](../Unfoldings/Source/TaggedMotion.lean) | Actual source motions for tagged face copies and both seam orientations |
| [Unfoldings.Source.TerminalPiece](../Unfoldings/Source/TerminalPiece.lean) | Actual finite terminal-face formulas, including tied endpoints |
| [Unfoldings.Source.TerminalTrace](../Unfoldings/Source/TerminalTrace.lean) | Finite continuation constructs a terminal affine chart from regularity |
| [Unfoldings.Source.TerminalUniqueness](../Unfoldings/Source/TerminalUniqueness.lean) | A terminal virtual-source image determines the whole original shortest path |
| [Unfoldings.Source.Unfolding](../Unfoldings/Source/Unfolding.lean) | The constructed source-unfolding result at every regular/nonextreme source |
| [Unfoldings.Source.UniqueProjection](../Unfoldings/Source/UniqueProjection.lean) | A homeomorphism selecting the unique shortest path continuously off the cut locus |
## Convex caps

The full nearly flat edge-unfolding theorem remains in progress; see the
[cap proof checklist](CAP_THEOREM.md). These are checked supporting modules.

| Module | Purpose |
| --- | --- |
| [Unfoldings.Cap.ClipSpatialTriangles](../Unfoldings/Cap/ClipSpatialTriangles.lean) | Actual isometric spatial triangles cover each clipped roof and retain original normals and tilt |
| [Unfoldings.Cap.ClipSupportPolygons](../Unfoldings/Cap/ClipSupportPolygons.lean) | Construct compact active-support polygons, exact segment rims, and actual triangle partitions |
| [Unfoldings.Cap.ClipTrianglePartition](../Unfoldings/Cap/ClipTrianglePartition.lean) | Assemble one finite disjoint-interior triangle partition of the entire clipped footprint |
| [Unfoldings.Cap.DistinctSupportCells](../Unfoldings/Cap/DistinctSupportCells.lean) | Remove duplicate support planes and prove pairwise interior separation and exact coverage |
| [Unfoldings.Cap.ClipBoundary](../Unfoldings/Cap/ClipBoundary.lean) | Exact finite segment rims of horizontal clips, with no triangulation premise |
| [Unfoldings.Cap.ClipDisk](../Unfoldings/Cap/ClipDisk.lean) | Actual compact clipped-roof disk homeomorphisms and the flat-or-clips dichotomy |
| [Unfoldings.Cap.RoofClips](../Unfoldings/Cap/RoofClips.lean) | Compact convex lower clips, an explicit homothety bound, and horizontal rim levels |
| [Unfoldings.Cap.RoofFlat](../Unfoldings/Cap/RoofFlat.lean) | Geometric cap input is flat or has a positive roof height |
| [Unfoldings.Cap.RoofLevels](../Unfoldings/Cap/RoofLevels.lean) | The original footprint is exactly the zero superlevel of any nonflat cap roof |
| [Unfoldings.Cap.BranchGapBalance](../Unfoldings/Cap/BranchGapBalance.lean) | Exact conservation of actual positional gaps across immediate child subtrees |
| [Unfoldings.Cap.OriginLeaf](../Unfoldings/Cap/OriginLeaf.lean) | The internal sector origin is a leaf with one shared actual bank start |
| [Unfoldings.Cap.RimTails](../Unfoldings/Cap/RimTails.lean) | Disjoint radial continuations of actual rim roots outside the footprint and onto the roof |
| [Unfoldings.Cap.RoofCellTrace](../Unfoldings/Cap/RoofCellTrace.lean) | Constructed finite polygonal traces through actual support cells outside the original cap |
| [Unfoldings.Cap.RoofExtension](../Unfoldings/Cap/RoofExtension.lean) | The actual unbounded roof, closed convex active cells, and its plane homeomorphism |
| [Unfoldings.Cap.RoofFinalRay](../Unfoldings/Cap/RoofFinalRay.lean) | Every roof ray eventually lies in one original support cell and becomes exactly straight |
| [Unfoldings.Cap.RoofSolid](../Unfoldings/Cap/RoofSolid.lean) | The extended roof is exactly the frontier of the convex original-support-halfspace solid |
| [Unfoldings.Cap.BankPositionOrder](../Unfoldings/Cap/BankPositionOrder.lean) | Actual parent-copy position order from all descendant paired-vector differences |
| [Unfoldings.Cap.BankSegments](../Unfoldings/Cap/BankSegments.lean) | Matched parameters are the actual straight entrance and exit bank segments |
| [Unfoldings.Cap.BranchDisplacements](../Unfoldings/Cap/BranchDisplacements.lean) | Exact actual parent-copy gap as the sum of all descendant bank-vector differences |
| [Unfoldings.Cap.MatchedBankPoints](../Unfoldings/Cap/MatchedBankPoints.lean) | All matched actual parent-bank points are ordered, including extensions past the rim |
| [Unfoldings.Cap.ParentBankDisplacements](../Unfoldings/Cap/ParentBankDisplacements.lean) | Actual named subtree entrances and exits and additive contour gap identity |
| [Unfoldings.Cap.ParentBankNoncrossing](../Unfoldings/Cap/ParentBankNoncrossing.lean) | Actual paired parent-bank interiors are disjoint up to zero-subtree-curvature contact |
| [Unfoldings.Cap.ParentBankVectorOrder](../Unfoldings/Cap/ParentBankVectorOrder.lean) | Signed subtree rotations give actual paired-vector coordinate order |
| [Unfoldings.Cap.SectorQuadrants](../Unfoldings/Cap/SectorQuadrants.lean) | Mesh-independent threshold constructs strict actual sector quadrants with retained calibration |
| [Unfoldings.Cap.UniformBankSeparation](../Unfoldings/Cap/UniformBankSeparation.lean) | Threshold before the complete mesh constructs each actual paired-seam separation |
| [Unfoldings.Cap.AlignedSectionTurn](../Unfoldings/Cap/AlignedSectionTurn.lean) | Actual transverse section turns contract after orientation-preserving rigid bank alignment |
| [Unfoldings.Cap.AnchorTrace](../Unfoldings/Cap/AnchorTrace.lean) | Construct actual section traces from one rim anchor to every original face, avoiding all original vertices |
| [Unfoldings.Cap.CalibratedThreshold](../Unfoldings/Cap/CalibratedThreshold.lean) | One threshold before the whole mesh controls every developed face direction in one global projection frame |
| [Unfoldings.Cap.CrossingPotential](../Unfoldings/Cap/CrossingPotential.lean) | Actual weighted forest-ray potential and telescoped query changes bounded by twice total curvature |
| [Unfoldings.Cap.DevelopmentOrientation](../Unfoldings/Cap/DevelopmentOrientation.lean) | Actual projected-to-developed affine charts have one determinant sign across the retained mesh |
| [Unfoldings.Cap.FaceDirectionAgreement](../Unfoldings/Cap/FaceDirectionAgreement.lean) | Actual one-direction section alignment controls every direction on every original face |
| [Unfoldings.Cap.FaceDirectionAngleError](../Unfoldings/Cap/FaceDirectionAngleError.lean) | Actual local face-angle distortion with a mesh-independent positive tilt threshold |
| [Unfoldings.Cap.FaceDirections](../Unfoldings/Cap/FaceDirections.lean) | Actual spatial and developed face directions over prescribed horizontal vectors, with genuine local angle control |
| [Unfoldings.Cap.GermVectors](../Unfoldings/Cap/GermVectors.lean) | Actual projected and spatial bank vectors use the original parent-child endpoint order |
| [Unfoldings.Cap.ParentBankOpening](../Unfoldings/Cap/ParentBankOpening.lean) | Construct actual oriented parent banks with proved rigid phases and forward and reverse section-turn bounds |
| [Unfoldings.Cap.ParentBankSides](../Unfoldings/Cap/ParentBankSides.lean) | Actual parent-bank entrance and exit faces determine the geometric transverse crossing sign |
| [Unfoldings.Cap.ParentDirectionRotation](../Unfoldings/Cap/ParentDirectionRotation.lean) | Actual outward parent-bank vectors rotate by descendant curvature in a projection-preserving frame |
| [Unfoldings.Cap.ParentRayCounter](../Unfoldings/Cap/ParentRayCounter.lean) | Identify physical parent-segment counters with the bounded actual forest-ray potential |
| [Unfoldings.Cap.ParentSectionPhase](../Unfoldings/Cap/ParentSectionPhase.lean) | Choose actual signed parent-bank curvature phase from the real section determinant |
| [Unfoldings.Cap.ParentSegments](../Unfoldings/Cap/ParentSegments.lean) | Whole projected parent segments are the actual original selected seam edges |
| [Unfoldings.Cap.PhaseSectionTurn](../Unfoldings/Cap/PhaseSectionTurn.lean) | Removing the actual signed subtree phase bounds parent-bank section turns by spatial bending |
| [Unfoldings.Cap.ProjectedContourSides](../Unfoldings/Cap/ProjectedContourSides.lean) | Every positively oriented actual contour bank has its original projected face on the left |
| [Unfoldings.Cap.ProjectedOpening](../Unfoldings/Cap/ProjectedOpening.lean) | Actual projected incident triangles open to strictly opposite sides of each original seam |
| [Unfoldings.Cap.ProjectedSeamUnique](../Unfoldings/Cap/ProjectedSeamUnique.lean) | A nonvertex actual projected seam point determines its unique original seam name |
| [Unfoldings.Cap.ProjectionCalibration](../Unfoldings/Cap/ProjectionCalibration.lean) | Calibrate one common actual developed frame against all original projected directions |
| [Unfoldings.Cap.ProjectionContour](../Unfoldings/Cap/ProjectionContour.lean) | Choose a complete actual boundary contour oriented by horizontal projection |
| [Unfoldings.Cap.ProjectionFrame](../Unfoldings/Cap/ProjectionFrame.lean) | One common developed frame preserves the actual projection orientation on all faces |
| [Unfoldings.Cap.RetainedSectionTurn](../Unfoldings/Cap/RetainedSectionTurn.lean) | Actual retained original-seam opening cannot increase transverse section turning |
| [Unfoldings.Cap.RimAnchor](../Unfoldings/Cap/RimAnchor.lean) | Construct a nonvertex rim midpoint with one original face and a common initial face for all sections |
| [Unfoldings.Cap.SeamDirections](../Unfoldings/Cap/SeamDirections.lean) | Actual spatial and retained developed seam vectors agree; regular sections meet transversely |
| [Unfoldings.Cap.SectionBankSides](../Unfoldings/Cap/SectionBankSides.lean) | Actual original-face containment determines the transverse section exit sign at a bank |
| [Unfoldings.Cap.SectionCounterGeometry](../Unfoldings/Cap/SectionCounterGeometry.lean) | Only the actual transition counter changes; its curvature contribution is the actual signed bank phase |
| [Unfoldings.Cap.SectionCrossingIsolation](../Unfoldings/Cap/SectionCrossingIsolation.lean) | Isolate the unique original seam between adjacent actual interior section samples |
| [Unfoldings.Cap.SectionFrame](../Unfoldings/Cap/SectionFrame.lean) | Positive section coordinates keep all original vertices off-axis and order actual interior samples |
| [Unfoldings.Cap.SectionHeadingBound](../Unfoldings/Cap/SectionHeadingBound.lean) | Actual real section headings change by at most twice tilt plus twice total curvature from one rim face |
| [Unfoldings.Cap.SectionHeadingThreshold](../Unfoldings/Cap/SectionHeadingThreshold.lean) | Choose forest and arbitrarily small actual section-heading budget uniformly before the entire mesh |
| [Unfoldings.Cap.SectionHeadingTransport](../Unfoldings/Cap/SectionHeadingTransport.lean) | Actual section spatial turning bounds real developed heading residuals after prescribed phases |
| [Unfoldings.Cap.SectionInteriors](../Unfoldings/Cap/SectionInteriors.lean) | Whole open regular section pieces are interior and avoid all original projected seams |
| [Unfoldings.Cap.SectionMidpoints](../Unfoldings/Cap/SectionMidpoints.lean) | Construct genuine interior sample points in all regular original-face section pieces |
| [Unfoldings.Cap.SectionPartition](../Unfoldings/Cap/SectionPartition.lean) | Construct strictly ordered finite original-face partitions of every projected cap segment |
| [Unfoldings.Cap.SectionPhases](../Unfoldings/Cap/SectionPhases.lean) | Derive zero retained phases and actual signed curvature phases across every transverse original seam |
| [Unfoldings.Cap.SectionPotentialIdentity](../Unfoldings/Cap/SectionPotentialIdentity.lean) | Actual trace phases telescope as differences of the bounded original forest-crossing potential |
| [Unfoldings.Cap.SectionSeams](../Unfoldings/Cap/SectionSeams.lean) | Construct actual transverse original seams for all nonconstant regular section transitions |
| [Unfoldings.Cap.SectionTrace](../Unfoldings/Cap/SectionTrace.lean) | Actual original-face trace labels and exact spatial secants from their tangent vectors |
| [Unfoldings.Cap.SectionTraceTurns](../Unfoldings/Cap/SectionTraceTurns.lean) | Actual tangent directions along the constructed face sequence turn by at most twice the tilt |
| [Unfoldings.Cap.SectionTransitions](../Unfoldings/Cap/SectionTransitions.lean) | Away from original vertices, adjacent original faces meet through an actual original seam |
| [Unfoldings.Cap.SectorFrameCrossings](../Unfoldings/Cap/SectorFrameCrossings.lean) | Bound actual forest crossing corrections in arbitrary translated orthogonal ray frames |
| [Unfoldings.Cap.RoofSections](../Unfoldings/Cap/RoofSections.lean) | Actual concave roof sections, uniform slope bounds, and telescoping real secant inclinations |
| [Unfoldings.Cap.SectionAngles](../Unfoldings/Cap/SectionAngles.lean) | Actual spatial section turning is at most twice the tilt, uniformly before the entire mesh |
| [Unfoldings.Cap.SectorCrossings](../Unfoldings/Cap/SectorCrossings.lean) | Actual sector root paths have bounded signed ray crossings; weighted subtree corrections are bounded by total curvature |
| [Unfoldings.Cap.SubtreeAngles](../Unfoldings/Cap/SubtreeAngles.lean) | Actual boundary contours, subtree copy counts, exact aggregate turns, and subtree curvature bounds |
| [Unfoldings.Cap.SubtreeOpening](../Unfoldings/Cap/SubtreeOpening.lean) | Actual matched parent banks rotate by all descendant curvatures, with exact small-curvature aperture |
| [Unfoldings.Cap.LeafOpening](../Unfoldings/Cap/LeafOpening.lean) | Actual equal-length developed leaf banks rotate by the actual vertex curvature |
| [Unfoldings.Cap.SingleCutStar](../Unfoldings/Cap/SingleCutStar.lean) | A unique incident cut seam opens exactly one original cyclic-link pair |
| [Unfoldings.Cap.Reframe](../Unfoldings/Cap/Reframe.lean) | Actual cap geometry is preserved under horizontal orthogonal frame changes |
| [Unfoldings.Cap.RegionalAngles](../Unfoldings/Cap/RegionalAngles.lean) | Every original-face union has partial-star excess bounded by total curvature |
| [Unfoldings.Cap.SectorDevelopment](../Unfoldings/Cap/SectorDevelopment.lean) | Source-centered forest cuts give actual flat cut disks and locally isometric developments |
| [Unfoldings.Cap.SectorForest](../Unfoldings/Cap/SectorForest.lean) | Construct source-centered original-edge forests from sector-preserving local progress |
| [Unfoldings.Cap.SectorForestExistence](../Unfoldings/Cap/SectorForestExistence.lean) | Choose an internal source and forest with thresholds before the entire mesh |
| [Unfoldings.Cap.SectorForestGeometry](../Unfoldings/Cap/SectorForestGeometry.lean) | Paths stay in source-centered sectors, reach the rim, and avoid the empty forward gap |
| [Unfoldings.Cap.SectorForestPaths](../Unfoldings/Cap/SectorForestPaths.lean) | Sector labels persist along original-edge root paths, proving radial monotonicity |
| [Unfoldings.Cap.SectorThreshold](../Unfoldings/Cap/SectorThreshold.lean) | Choose source-centered forests and arbitrarily small curvature budgets with one uniform tilt |
| [Unfoldings.Cap.ThreeSectorProgress](../Unfoldings/Cap/ThreeSectorProgress.lean) | Original seams enter each prescribed acute sector, with mesh-uniform projection thresholds |
| [Unfoldings.Cap.TracePhaseTransport](../Unfoldings/Cap/TracePhaseTransport.lean) | Construct actual seam phases and unreduced headings along regular traces, with twice-tilt residual bound |
| [Unfoldings.Cap.VerticalFrame](../Unfoldings/Cap/VerticalFrame.lean) | Lift a planar orthogonal frame to space while preserving height |
| [Unfoldings.Cap.BoundaryGerms](../Unfoldings/Cap/BoundaryGerms.lean) | Actual unpaired germ directions lie on the horizontal convex rim |
| [Unfoldings.Cap.ProjectedInterval](../Unfoldings/Cap/ProjectedInterval.lean) | Actual projected interval rays have genuine disjoint cones and consistent orientation |
| [Unfoldings.Cap.RimAngles](../Unfoldings/Cap/RimAngles.lean) | Nonnegative rim angle excess, exact total-curvature balance, and bounds for every rim portion |
| [Unfoldings.Cap.AngularCurvature](../Unfoldings/Cap/AngularCurvature.lean) | Intrinsic interior angular defect equals the actual outward normal solid angle |
| [Unfoldings.Cap.CurvatureBudget](../Unfoldings/Cap/CurvatureBudget.lean) | Nonnegative intrinsic defects and total-curvature bounds from actual normal-cone packing |
| [Unfoldings.Cap.GermCrossing](../Unfoldings/Cap/GermCrossing.lean) | Sign changes in an actual face meet the supported planar cone boundary |
| [Unfoldings.Cap.GermNormalCone](../Unfoldings/Cap/GermNormalCone.lean) | Incident edge signs detect the complete actual outward normal cone |
| [Unfoldings.Cap.GermSupports](../Unfoldings/Cap/GermSupports.lean) | Actual spatial edge directions obey every incident supporting plane |
| [Unfoldings.Cap.IncidentDirections](../Unfoldings/Cap/IncidentDirections.lean) | Actual projected corner cones cover every direction at an interior cap vertex |
| [Unfoldings.Cap.LinkCrossingBound](../Unfoldings/Cap/LinkCrossingBound.lean) | Supporting planes and disjoint projected faces bound actual cyclic link crossings by two |
| [Unfoldings.Cap.LinkCrossings](../Unfoldings/Cap/LinkCrossings.lean) | Actual convex vertex links have zero or two crossings according to normal-cone membership |
| [Unfoldings.Cap.UniformCurvature](../Unfoldings/Cap/UniformCurvature.lean) | Explicit normal-height curvature budget and a threshold quantified before every input mesh |
| [Unfoldings.Cap.Boundary](../Unfoldings/Cap/Boundary.lean) | Exact identification of the projected rim with actual bank boundaries and boundary vertices |
| [Unfoldings.Cap.ForestDevelopment](../Unfoldings/Cap/ForestDevelopment.lean) | A constructed locally isometric original-edge cap development, with overlap permitted |
| [Unfoldings.Cap.ForestExistence](../Unfoldings/Cap/ForestExistence.lean) | Uniform positive tilt and shear parameters construct actual original-edge rooted forests and cut disks |
| [Unfoldings.Cap.ForestPaths](../Unfoldings/Cap/ForestPaths.lean) | Canonical original-seam paths to the first boundary root are angle-monotone and radially monotone |
| [Unfoldings.Cap.Gnomonic](../Unfoldings/Cap/Gnomonic.lean) | Mutually inverse planar slope and spherical upward-normal coordinates |
| [Unfoldings.Cap.GnomonicArea](../Unfoldings/Cap/GnomonicArea.lean) | Nonexpansive inverse gnomonic projection bounds actual spherical normal area by planar area |
| [Unfoldings.Cap.ConicalArea](../Unfoldings/Cap/ConicalArea.lean) | A conservative Lipschitz cone parametrization bounds solid angle by planar slope area |
| [Unfoldings.Cap.SolidNormalArea](../Unfoldings/Cap/SolidNormalArea.lean) | Arbitrarily small uniform total solid-angle budgets for actual normal cones |
| [Unfoldings.Cap.Tilt](../Unfoldings/Cap/Tilt.lean) | Monotonicity of geometric normal-tilt bounds |
| [Unfoldings.Cap.VerticalProduct](../Unfoldings/Cap/VerticalProduct.lean) | Isometric horizontal/vertical splitting and actual prism volumes |
| [Unfoldings.Cap.NormalCone](../Unfoldings/Cap/NormalCone.lean) | Interior vertex normal polygons are exactly the actual upward supporting normal cones |
| [Unfoldings.Cap.MonotoneForest](../Unfoldings/Cap/MonotoneForest.lean) | Construct actual original-seam parent selections from acute-wedge progress |
| [Unfoldings.Cap.NoInterior](../Unfoldings/Cap/NoInterior.lean) | Caps without interior vertices are flat and have an injective uncut development |
| [Unfoldings.Cap.NormalArea](../Unfoldings/Cap/NormalArea.lean) | A vertex-count-independent Lebesgue area budget for all actual planar normal polygons |
| [Unfoldings.Cap.NormalAreaThreshold](../Unfoldings/Cap/NormalAreaThreshold.lean) | A positive tilt threshold gives arbitrarily small total planar normal-image area |
| [Unfoldings.Cap.NormalImage](../Unfoldings/Cap/NormalImage.lean) | Incident supporting slopes give convex normal polygons with disjoint interiors in one bounded disk |
| [Unfoldings.Cap.AcuteProjection](../Unfoldings/Cap/AcuteProjection.lean) | A uniform positive tilt preserves half an input acute angle margin |
| [Unfoldings.Cap.AngleBalance](../Unfoldings/Cap/AngleBalance.lean) | Relative angle-defect balance from actual original and projected triangle angles |
| [Unfoldings.Cap.Metric](../Unfoldings/Cap/Metric.lean) | Uniform Lipschitz and inverse Lipschitz bounds for actual intrinsic cap distances |
| [Unfoldings.Cap.OpenedBanks](../Unfoldings/Cap/OpenedBanks.lean) | Construct matched banks using cumulative nonnegative opening budgets |
| [Unfoldings.Cap.ProjectedFaces](../Unfoldings/Cap/ProjectedFaces.lean) | The actual affine projected triangles, disjoint interiors, and exact footprint cover |
| [Unfoldings.Cap.ProjectedFlatness](../Unfoldings/Cap/ProjectedFlatness.lean) | Actual projected interior links make one full turn, yielding cap curvature/boundary-excess balance |
| [Unfoldings.Cap.ProjectedLink](../Unfoldings/Cap/ProjectedLink.lean) | Actual cyclic projected germ rays, corner angles, and disjoint incident direction cones |
| [Unfoldings.Cap.RadialBanks](../Unfoldings/Cap/RadialBanks.lean) | Equal-radius bank order in the common-quadrant case, including finite endpoints |
| [Unfoldings.Cap.Roof](../Unfoldings/Cap/Roof.lean) | Concave supporting-plane lower envelope agreeing with every actual cap face |
| [Unfoldings.Cap.VertexProgress](../Unfoldings/Cap/VertexProgress.lean) | Actual original cap edges enter a strict quadrant at interior projected vertices |
| [Unfoldings.Cap.VertexWedge](../Unfoldings/Cap/VertexWedge.lean) | Actual original cap edges enter a sheared acute wedge |
| [Unfoldings.Cap.AngleProjection](../Unfoldings/Cap/AngleProjection.lean) | A positive projection-angle threshold uniform over all tangent directions |
| [Unfoldings.Cap.Basic](../Unfoldings/Cap/Basic.lean) | Geometric convex caps with supporting normals, convex injective projection, and a horizontal rim |
| [Unfoldings.Cap.Flat](../Unfoldings/Cap/Flat.lean) | An actual injective nonoverlapping development of every flat cap without cuts |
| [Unfoldings.Cap.HeadingBanks](../Unfoldings/Cap/HeadingBanks.lean) | Whole-chain bank order from matched lengths and ordered quadrant headings |
| [Unfoldings.Cap.Projection](../Unfoldings/Cap/Projection.lean) | Horizontal projection, tangent-plane metric and vertical-motion estimates |
| [Unfoldings.Cap.Topology](../Unfoldings/Cap/Topology.lean) | Disk topology derived from the actual convex footprint |

## Triangle complexes

| Module | Purpose |
| --- | --- |
| [Unfoldings.Complex.SelectedBankSum](../Unfoldings/Complex/SelectedBankSum.lean) | Sum directed actual contour bank weights as one distinctly named pair per parent seam |
| [Unfoldings.Complex.AngleCutSums](../Unfoldings/Complex/AngleCutSums.lean) | Weighted and regional angle conservation over actual cut copies |
| [Unfoldings.Complex.BoundaryContour](../Unfoldings/Complex/BoundaryContour.lean) | Construct a complete actual boundary contour from connected bank topology |
| [Unfoldings.Complex.BoundaryCycleEnumeration](../Unfoldings/Complex/BoundaryCycleEnumeration.lean) | A covering boundary cycle enumerates each actual bank and vertex copy once |
| [Unfoldings.Complex.BoundaryIncidence](../Unfoldings/Complex/BoundaryIncidence.lean) | Weighted endpoint incidence counts actual boundary copies twice |
| [Unfoldings.Complex.BoundaryLink](../Unfoldings/Complex/BoundaryLink.lean) | The actual corner interval between a specified bank and its boundary mate |
| [Unfoldings.Complex.ParentBankEndpoints](../Unfoldings/Complex/ParentBankEndpoints.lean) | Actual entrance and exit parent banks have the original parent-child endpoint order |
| [Unfoldings.Complex.RegularSeamUnique](../Unfoldings/Complex/RegularSeamUnique.lean) | Related regular points on original seam banks determine the same original seam name |
| [Unfoldings.Complex.RelativeBankEnumeration](../Unfoldings/Complex/RelativeBankEnumeration.lean) | Further cuts retain all old banks and add exactly two banks per opened seam |
| [Unfoldings.Complex.SelectedIncidence](../Unfoldings/Complex/SelectedIncidence.lean) | Actual cut-copy multiplicity equals selected original-edge endpoint multiplicity off the rim |
| [Unfoldings.Complex.SelectedSubtreeAngles](../Unfoldings/Complex/SelectedSubtreeAngles.lean) | Exact boundary-turn sum for arbitrary branching descendant subtrees without Euler assumptions |
| [Unfoldings.Complex.SelectedSubtreeBoundary](../Unfoldings/Complex/SelectedSubtreeBoundary.lean) | Exactly two actual parent-seam banks cross each descendant separator |
| [Unfoldings.Complex.SubtreeContour](../Unfoldings/Complex/SubtreeContour.lean) | The actual boundary contour has one entering and one leaving parent bank per subtree |
| [Unfoldings.Complex.LinkSteps](../Unfoldings/Complex/LinkSteps.lean) | Consecutive ordered link corners cross actual retained original seams |
| [Unfoldings.Complex.RetainedCornerChain](../Unfoldings/Complex/RetainedCornerChain.lean) | A retained spanning corner chain has one actual cut vertex copy and preserves its angle |
| [Unfoldings.Complex.SingleLinkCut](../Unfoldings/Complex/SingleLinkCut.lean) | Opening one original cyclic-link pair preserves the complete star and intrinsic angle |
| [Unfoldings.Complex.SingleLinkCutEndpoints](../Unfoldings/Complex/SingleLinkCutEndpoints.lean) | The two terminal cut germs are exactly the original opened seam pair |
| [Unfoldings.Complex.RegionalCorners](../Unfoldings/Complex/RegionalCorners.lean) | Actual corner sums and complete stars for arbitrary original-face selections |
| [Unfoldings.Complex.Curvature](../Unfoldings/Complex/Curvature.lean) | Interior angular defects grouped by actual retained vertex classes |
| [Unfoldings.Complex.SeamGraph](../Unfoldings/Complex/SeamGraph.lean) | The original internal-seam graph with all original vertices and exact face-edge incidence |
| [Unfoldings.Complex.SelectedCuts](../Unfoldings/Complex/SelectedCuts.lean) | Selected parent edges induce the actual rooted relative cut graph, all-boundary vertex copies, and a cut disk |
| [Unfoldings.Complex.Angles](../Unfoldings/Complex/Angles.lean) | Total angles and conservation across cut vertex copies |
| [Unfoldings.Complex.BoundaryAtlas](../Unfoldings/Complex/BoundaryAtlas.lean) | Actual bank half-plane atlases and inward embeddings of arbitrary cut surfaces |
| [Unfoldings.Complex.BoundaryComponentDescent](../Unfoldings/Complex/BoundaryComponentDescent.lean) | Boundary-component labels descend through actual restored vertex classes |
| [Unfoldings.Complex.BoundaryConnectivity](../Unfoldings/Complex/BoundaryConnectivity.lean) | A connected primal cut forest has connected actual bank boundary |
| [Unfoldings.Complex.BoundaryCycleCarrier](../Unfoldings/Complex/BoundaryCycleCarrier.lean) | The covering bank cycle has exactly the actual boundary carrier |
| [Unfoldings.Complex.BoundaryCycles](../Unfoldings/Complex/BoundaryCycles.lean) | Every actual boundary bank lies on a multigraph cycle and is not a bridge |
| [Unfoldings.Complex.BoundaryGraph](../Unfoldings/Complex/BoundaryGraph.lean) | Actual banks form a finite embedded multigraph with their exact carrier |
| [Unfoldings.Complex.BoundaryJordan](../Unfoldings/Complex/BoundaryJordan.lean) | Actual bank cycles are Jordan curves in planar embeddings |
| [Unfoldings.Complex.BoundaryObstruction](../Unfoldings/Complex/BoundaryObstruction.lean) | Open planar injections cannot hit nonvertex banks; bank points are metrically nonregular |
| [Unfoldings.Complex.BoundaryOrdering](../Unfoldings/Complex/BoundaryOrdering.lean) | Exactly two ends per boundary vertex and finite simple closed bank orders |
| [Unfoldings.Complex.BoundaryQuotient](../Unfoldings/Complex/BoundaryQuotient.lean) | Compact actual bank boundaries and exact boundary-only fibers of seam restoration |
| [Unfoldings.Complex.BoundaryRegular](../Unfoldings/Complex/BoundaryRegular.lean) | Euclidean ball charts at every nonvertex point off the actual cut banks |
| [Unfoldings.Complex.BoundarySingleCycle](../Unfoldings/Complex/BoundarySingleCycle.lean) | A cut tree gives one closed bank cycle covering every boundary end |
| [Unfoldings.Complex.Charts](../Unfoldings/Complex/Charts.lean) | Constructed face-interior Euclidean metric charts |
| [Unfoldings.Complex.Classes](../Unfoldings/Complex/Classes.lean) | Finite corner classes and unique nonvertex seam neighbors |
| [Unfoldings.Complex.ClosedBanks](../Unfoldings/Complex/ClosedBanks.lean) | Closed complexes identify each boundary bank with one side of an actual cut seam |
| [Unfoldings.Complex.CollapsedCutCarrier](../Unfoldings/Complex/CollapsedCutCarrier.lean) | Exact carrier and native graph of the actual new cut arcs after collapsing the old boundary |
| [Unfoldings.Complex.CollapsedCutGraph](../Unfoldings/Complex/CollapsedCutGraph.lean) | Construct the finite embedded collapsed cut multigraph, preserving loops and parallel edges |
| [Unfoldings.Complex.Connectivity](../Unfoldings/Complex/Connectivity.lean) | Finite metrics and geodesics for connected face incidence |
| [Unfoldings.Complex.CutDisk](../Unfoldings/Complex/CutDisk.lean) | Boundary-preserving cut disks imply open-disk complements and tree bank-image graphs |
| [Unfoldings.Complex.CutGraph](../Unfoldings/Complex/CutGraph.lean) | Construct exact finite spatial embedded straight graphs of all unpaired bank images |
| [Unfoldings.Complex.CutSeamGraph](../Unfoldings/Complex/CutSeamGraph.lean) | Canonical primal cut multigraph with actual original endpoints and no unused vertices |
| [Unfoldings.Complex.DiskBoundaryQuotient](../Unfoldings/Complex/DiskBoundaryQuotient.lean) | Restore cuts and collapse the original disk boundary to obtain a sphere; disk cuts have contractible collapsed bank images |
| [Unfoldings.Complex.DiskCuts](../Unfoldings/Complex/DiskCuts.lean) | Further cuts of a disk are disks exactly when the actual bank graph is connected; constructed planar embeddings and disk homeomorphisms |
| [Unfoldings.Complex.DiskSphereFibers](../Unfoldings/Complex/DiskSphereFibers.lean) | Exact original disk-to-sphere projection fibers, including every boundary vertex |
| [Unfoldings.Complex.ElementarySubdivision](../Unfoldings/Complex/ElementarySubdivision.lean) | Construct a two-triangle split and prove its actual seam conformity |
| [Unfoldings.Complex.EmbeddedStars](../Unfoldings/Complex/EmbeddedStars.lean) | Unique per-cell centers supplied by spatial foldings |
| [Unfoldings.Complex.Exact](../Unfoldings/Complex/Exact.lean) | Exact metric identifications and quotient homeomorphism |
| [Unfoldings.Complex.Excision](../Unfoldings/Complex/Excision.lean) | Metric excision and preserved triangle-complex point classes |
| [Unfoldings.Complex.FaceRouteEnd](../Unfoldings/Complex/FaceRouteEnd.lean) | The final positive-length piece of a strictly ordered face route |
| [Unfoldings.Complex.FaceRouteLift](../Unfoldings/Complex/FaceRouteLift.lean) | Continuously lift actual route pieces into their original closed faces |
| [Unfoldings.Complex.FaceRoutes](../Unfoldings/Complex/FaceRoutes.lean) | Bounded finite face partitions with affine pieces and exact chord lengths |
| [Unfoldings.Complex.Folding](../Unfoldings/Complex/Folding.lean) | Spatial rigid placements and embedded surface topology |
| [Unfoldings.Complex.Geodesics](../Unfoldings/Complex/Geodesics.lean) | Straight face traces and closed interval face visits |
| [Unfoldings.Complex.GermEndpoints](../Unfoldings/Complex/GermEndpoints.lean) | Actual far corners and complementary endpoint transport |
| [Unfoldings.Complex.GermSegments](../Unfoldings/Complex/GermSegments.lean) | Local edge endpoints in the actual orientation of each germ |
| [Unfoldings.Complex.Germs](../Unfoldings/Complex/Germs.lean) | The two corner edge germs and their retained seam crossings |
| [Unfoldings.Complex.HalfPlaneBoundary](../Unfoldings/Complex/HalfPlaneBoundary.lean) | Intrinsic bank identification under every open local half-plane homeomorphism |
| [Unfoldings.Complex.HingeCharts](../Unfoldings/Complex/HingeCharts.lean) | Constructed Euclidean metric balls at retained edge interiors |
| [Unfoldings.Complex.HingeCoordinates](../Unfoldings/Complex/HingeCoordinates.lean) | Local hinge frames and exact local distances |
| [Unfoldings.Complex.Hinge](../Unfoldings/Complex/Hinge.lean) | Intrinsic upper bounds from local unfolded hinge chords |
| [Unfoldings.Complex.InteriorTags](../Unfoldings/Complex/InteriorTags.lean) | Original face-interior points have unique tagged representatives |
| [Unfoldings.Complex.IntrinsicBoundary](../Unfoldings/Complex/IntrinsicBoundary.lean) | Every disk homeomorphism preserves the actual bank boundary, including all vertices |
| [Unfoldings.Complex.LinkConnectivity](../Unfoldings/Complex/LinkConnectivity.lean) | Germ components are exactly metric vertex classes |
| [Unfoldings.Complex.LinkOrdering](../Unfoldings/Complex/LinkOrdering.lean) | Constructed link orders and their Euclidean angle sums |
| [Unfoldings.Complex.Links](../Unfoldings/Complex/Links.lean) | Vertex-link involutions and boundary fixed germs |
| [Unfoldings.Complex.Neighborhood](../Unfoldings/Complex/Neighborhood.lean) | Quantitative neighborhoods of two-face seam classes |
| [Unfoldings.Complex.PairedBankComponents](../Unfoldings/Complex/PairedBankComponents.lean) | The two banks of a forest cut lie in one actual boundary component |
| [Unfoldings.Complex.Paths](../Unfoldings/Complex/Paths.lean) | Intrinsic path metric and geodesic existence for cut complexes |
| [Unfoldings.Complex.PointFiber](../Unfoldings/Complex/PointFiber.lean) | Exact point fibers have at most one copy per original face and bounded seam paths |
| [Unfoldings.Complex.PointSeamRoute](../Unfoldings/Complex/PointSeamRoute.lean) | Actual bounded oriented seam routes, including at vertices |
| [Unfoldings.Complex.PolygonalCutGraph](../Unfoldings/Complex/PolygonalCutGraph.lean) | Embed each new polygonal forest arc in the original metric surface with rigid parent coordinates |
| [Unfoldings.Complex.PolygonalCuts](../Unfoldings/Complex/PolygonalCuts.lean) | Certified refined cut presentations, rooted forests, actual disks, and unique flat developments |
| [Unfoldings.Complex.RefinedCuts](../Unfoldings/Complex/RefinedCuts.lean) | Actual refined cut metrics, projections, polygonal boundary support, and the sphere tree criterion |
| [Unfoldings.Complex.RegularEdges](../Unfoldings/Complex/RegularEdges.lean) | Constructed edge charts from either seam bank |
| [Unfoldings.Complex.Regular](../Unfoldings/Complex/Regular.lean) | Constructed regular points and unique intrinsic geodesic continuation |
| [Unfoldings.Complex.RelativeBoundaryConnectivity](../Unfoldings/Complex/RelativeBoundaryConnectivity.lean) | Descend boundary-component labels and prove rooted forest cuts have connected actual banks |
| [Unfoldings.Complex.RelativeCutDisk](../Unfoldings/Complex/RelativeCutDisk.lean) | Construct actual disk homeomorphisms from relative rooted cut forests, with exact bank boundary |
| [Unfoldings.Complex.RelativeCutForest](../Unfoldings/Complex/RelativeCutForest.lean) | Full disk-cut iff rooted-forest criterion; empty cuts and cycle, multiple-root, and missing-root obstructions |
| [Unfoldings.Complex.RelativeCutGraph](../Unfoldings/Complex/RelativeCutGraph.lean) | Canonical new cut seam multigraph and original boundary roots, excluding old bank edges |
| [Unfoldings.Complex.RelativePairedBanks](../Unfoldings/Complex/RelativePairedBanks.lean) | Opposite banks of relative forest cuts share an actual boundary component |
| [Unfoldings.Complex.RelativeSeamGeometry](../Unfoldings/Complex/RelativeSeamGeometry.lean) | Original new cut arcs avoid old banks and vertices; distinct open seam arcs are disjoint |
| [Unfoldings.Complex.SeamFaceRoute](../Unfoldings/Complex/SeamFaceRoute.lean) | Constructed entry/exit points and bounded seam resolutions of all face-route junctions |
| [Unfoldings.Complex.SeamWordMotion](../Unfoldings/Complex/SeamWordMotion.lean) | Exact whole-motion propagation through finite oriented seam words |
| [Unfoldings.Complex.SeamWord](../Unfoldings/Complex/SeamWord.lean) | Finite oriented words construct rigid hinge placements agreeing at actual crossing points |
| [Unfoldings.Complex.Star](../Unfoldings/Complex/Star.lean) | Actual vertex stars, conserved angles and local metric comparisons |
| [Unfoldings.Complex.SubdivisionComposition](../Unfoldings/Complex/SubdivisionComposition.lean) | Identity and iterated conforming refinements with compatible metric equivalences |
| [Unfoldings.Complex.SubdivisionFolding](../Unfoldings/Complex/SubdivisionFolding.lean) | Transport spatial foldings, embedding, surface, convex hull, and convex boundaries |
| [Unfoldings.Complex.SubdivisionInteriors](../Unfoldings/Complex/SubdivisionInteriors.lean) | Child interior disjointness and parent adjacency derived from seam conformity |
| [Unfoldings.Complex.SubdivisionMetric](../Unfoldings/Complex/SubdivisionMetric.lean) | Intrinsic isometry for every conforming finite subdivision, including disconnected surfaces |
| [Unfoldings.Complex.SubdivisionRegular](../Unfoldings/Complex/SubdivisionRegular.lean) | Preserve intrinsic Euclidean ball charts through refinement |
| [Unfoldings.Complex.Subdivision](../Unfoldings/Complex/Subdivision.lean) | Geometric parent placements and exact seam-chain conformity |
| [Unfoldings.Complex.Vertices](../Unfoldings/Complex/Vertices.lean) | Actual cut vertex classes, boundary incidence and copy maps |
| [Unfoldings.Complex](../Unfoldings/Complex.lean) | Finite edge-paired complexes and their cut realizations |

## Cuts and layouts

| Module | Purpose |
| --- | --- |
| [Unfoldings.Development.BoundaryDisplacements](../Unfoldings/Development/BoundaryDisplacements.lean) | Actual boundary positions, bank displacements, and closed-cycle cancellation |
| [Unfoldings.Development.BankLengths](../Unfoldings/Development/BankLengths.lean) | Actual developed lengths agree for both banks and either endpoint of any original seam |
| [Unfoldings.Development.BoundaryFrame](../Unfoldings/Development/BoundaryFrame.lean) | One orthogonal frame orients every actual boundary corner star |
| [Unfoldings.Development.BoundaryOrientation](../Unfoldings/Development/BoundaryOrientation.lean) | Propagate orientation through actual bank and vertex pairings, allowing overlap |
| [Unfoldings.Development.BoundaryRays](../Unfoldings/Development/BoundaryRays.lean) | Actual directed bank vectors and exact reversal at their far endpoints |
| [Unfoldings.Development.BoundaryRotations](../Unfoldings/Development/BoundaryRotations.lean) | Actual boundary corner and exterior-step rotations in one shared frame |
| [Unfoldings.Development.FramedLinkHeadings](../Unfoldings/Development/FramedLinkHeadings.lean) | Exact unreduced link headings and terminal rotation in an explicit prescribed frame |
| [Unfoldings.Development.SubtreeRotation](../Unfoldings/Development/SubtreeRotation.lean) | Cancel internal boundary rotations to obtain the actual rigid whole-subtree bank opening |
| [Unfoldings.Development.BankOpening](../Unfoldings/Development/BankOpening.lean) | Actual terminal bank aperture and rigid equal-length rotation, allowing zero-defect contact |
| [Unfoldings.Development.GermCones](../Unfoldings/Development/GermCones.lean) | Actual developed corner cones separate at every retained hinge |
| [Unfoldings.Development.GermRays](../Unfoldings/Development/GermRays.lean) | Actual developed edge rays, genuine lengths, corner angles, and retained mate agreement |
| [Unfoldings.Development.IntervalRays](../Unfoldings/Development/IntervalRays.lean) | Developed link ray sequences and common orientation from adjacent hinges alone |
| [Unfoldings.Development.LinkHeadings](../Unfoldings/Development/LinkHeadings.lean) | Exact unreduced real headings and terminal bank rotations in actual developments |
| [Unfoldings.Development.SpatialLengths](../Unfoldings/Development/SpatialLengths.lean) | Developed bank lengths match original spatial edges across distinct cut vertex copies |
| [Unfoldings.Boundary.Charts](../Unfoldings/Boundary/Charts.lean) | Constructed half-ball metric charts at boundary edge interiors |
| [Unfoldings.Boundary.Exact](../Unfoldings/Boundary/Exact.lean) | Metric separation of distinct cut-bank interiors |
| [Unfoldings.Boundary](../Unfoldings/Boundary.lean) | Boundary-edge labels, bank maps, and restoration of banks |
| [Unfoldings.Development.FlatDiskInterior](../Unfoldings/Development/FlatDiskInterior.lean) | The open interior of a flat metric disk has a global developing map |
| [Unfoldings.Development.FlatDisk](../Unfoldings/Development/FlatDisk.lean) | Flat interior angles imply a unique normalized outward development with actual local isometry |
| [Unfoldings.Development.Hinge](../Unfoldings/Development/Hinge.lean) | Nonoverlapping developments of arbitrary two-triangle hinges |
| [Unfoldings.Development.Normalization](../Unfoldings/Development/Normalization.lean) | Global rigid postcomposition and arbitrary root-face normalization |
| [Unfoldings.Development.SubdivisionNonoverlap](../Unfoldings/Development/SubdivisionNonoverlap.lean) | Nonoverlap is invariant under subdivision, in both directions |
| [Unfoldings.Development.Subdivision](../Unfoldings/Development/Subdivision.lean) | Restrict arbitrary developments while deriving strict opposite-side opening |
| [Unfoldings.Development.Uniqueness](../Unfoldings/Development/Uniqueness.lean) | An outward development of a connected complex is uniquely determined by one face |
| [Unfoldings.Development](../Unfoldings/Development.lean) | Facewise placements, nonoverlap, multiplicity, and metric descent |
| [Unfoldings.PolygonalLayout](../Unfoldings/PolygonalLayout.lean) | Finite polygon layouts with separate rigid face maps and optional nonoverlap |

## Metrics and gluing

| Module | Purpose |
| --- | --- |
| [Unfoldings.Metric.BallChartTransport](../Unfoldings/Metric/BallChartTransport.lean) | Transport whole open-ball metric charts along intrinsic isometries |
| [Unfoldings.Metric.BallChart](../Unfoldings/Metric/BallChart.lean) | Whole metric-ball charts in a named model space |
| [Unfoldings.Metric.BallIsometry](../Unfoldings/Metric/BallIsometry.lean) | Restrict isometries to balls with specified centers |
| [Unfoldings.Metric.BallParametrization](../Unfoldings/Metric/BallParametrization.lean) | Whole-ball charts from isometric parametrizations with ball coverage |
| [Unfoldings.Metric.Barrier](../Unfoldings/Metric/Barrier.lean) | Capped distance separators and local class transport |
| [Unfoldings.Metric.CenterBounds](../Unfoldings/Metric/CenterBounds.lean) | Local center bounds imply global distance bounds on real intervals |
| [Unfoldings.Metric.ClosedSeams](../Unfoldings/Metric/ClosedSeams.lean) | Exactness for closed isometric seams with finite classes |
| [Unfoldings.Metric.Connected](../Unfoldings/Metric/Connected.lean) | Preconnected extended metric spaces have finite distances |
| [Unfoldings.Metric.ConvexCover](../Unfoldings/Metric/ConvexCover.lean) | Finite closed-cover nonexpansion with extended-metric targets |
| [Unfoldings.Metric.EuclideanAtlas](../Unfoldings/Metric/EuclideanAtlas.lean) | Open Euclidean metric charts and unique locally constant rigid transition germs |
| [Unfoldings.Metric.EuclideanCocycle](../Unfoldings/Metric/EuclideanCocycle.lean) | Exact identity, composition, and inverse laws for rigid chart transitions |
| [Unfoldings.Metric.EuclideanDevelopment](../Unfoldings/Metric/EuclideanDevelopment.lean) | Continue one frame to a global planar local isometry on a simply connected space |
| [Unfoldings.Metric.Excision](../Unfoldings/Metric/Excision.lean) | Whole-ball isometries when cutting distant seams |
| [Unfoldings.Metric.FiniteComponent](../Unfoldings/Metric/FiniteComponent.lean) | Clopen finite-distance components as compact metric spaces |
| [Unfoldings.Metric.Gluing](../Unfoldings/Metric/Gluing.lean) | Metric quotient, descent, and restoration of seams |
| [Unfoldings.Metric.IsometricCells](../Unfoldings/Metric/IsometricCells.lean) | Compatible isometric cell maps exclude intrinsic cell shortcuts |
| [Unfoldings.Metric.Lipschitz](../Unfoldings/Metric/Lipschitz.lean) | Compatible Lipschitz cell maps descend through metric gluing |
| [Unfoldings.Metric.LocalComposition](../Unfoldings/Metric/LocalComposition.lean) | Compose local isometries and obtain local center bounds |
| [Unfoldings.Metric.LocalInverse](../Unfoldings/Metric/LocalInverse.lean) | Constructed isometric inverse neighborhoods |
| [Unfoldings.Metric.LocalMap](../Unfoldings/Metric/LocalMap.lean) | Metric lower bounds from estimates on short local routes |
| [Unfoldings.Metric.LocalRigidMap](../Unfoldings/Metric/LocalRigidMap.lean) | A constructed local isometry has an actual rigid expression in any open Euclidean chart |
| [Unfoldings.Metric.LocalSeams](../Unfoldings/Metric/LocalSeams.lean) | Local estimates from compatibility at incident closed seams |
| [Unfoldings.Metric.Local](../Unfoldings/Metric/Local.lean) | Seam clearance, metric ball images, and local cell isometries |
| [Unfoldings.Metric.OpenChart](../Unfoldings/Metric/OpenChart.lean) | Recenter open isometric charts on whole ambient balls |
| [Unfoldings.Metric.OpenEuclideanAtlas](../Unfoldings/Metric/OpenEuclideanAtlas.lean) | Restrict ambient Euclidean regularity to an open metric subspace |
| [Unfoldings.Metric.Paths](../Unfoldings/Metric/Paths.lean) | Continuous-path/route metric equality and shortest metric paths |
| [Unfoldings.Metric.PolygonalCompletion](../Unfoldings/Metric/PolygonalCompletion.lean) | Isometric dense interior inclusion and complete compact closed-domain model |
| [Unfoldings.Metric.PolygonalLocal](../Unfoldings/Metric/PolygonalLocal.lean) | Isometric neighborhoods for the development and its inverse on open regions |
| [Unfoldings.Metric.PolygonalMap](../Unfoldings/Metric/PolygonalMap.lean) | Local center bounds descend to intrinsic polygonal metrics |
| [Unfoldings.Metric.PolygonalPaths](../Unfoldings/Metric/PolygonalPaths.lean) | Straight-step geodesics and equality of route and continuous-path distance |
| [Unfoldings.Metric.PolygonalStar](../Unfoldings/Metric/PolygonalStar.lean) | Radial contraction identifies intrinsic and ambient topology through the boundary |
| [Unfoldings.Metric.Polygonal](../Unfoldings/Metric/Polygonal.lean) | Constructed intrinsic metrics from allowed straight steps and nonexpanding inclusions |
| [Unfoldings.Metric.Quotient](../Unfoldings/Metric/Quotient.lean) | Declared seam classes, exactness, compactness, and completeness |
| [Unfoldings.Metric.RegularGeodesic](../Unfoldings/Metric/RegularGeodesic.lean) | A whole regular chart supplies a nonconstant geodesic through its center |
| [Unfoldings.Metric.RegularLocus](../Unfoldings/Metric/RegularLocus.lean) | Metric regularity is open and open charts recenter to whole metric balls |
| [Unfoldings.Metric.RigidChartTransition](../Unfoldings/Metric/RigidChartTransition.lean) | Construct rigid affine transitions between actual overlapping metric charts |
| [Unfoldings.Metric.RigidChartUniqueness](../Unfoldings/Metric/RigidChartUniqueness.lean) | Rigid motions agreeing in an open metric chart agree globally |
| [Unfoldings.Metric.RigidFrameBundle](../Unfoldings/Metric/RigidFrameBundle.lean) | The discrete rigid-frame bundle is a genuine covering space |
| [Unfoldings.Metric.Route](../Unfoldings/Metric/Route.lean) | Finite routes and the generated extended pseudometric |
| [Unfoldings.Metric.Unglued](../Unfoldings/Metric/Unglued.lean) | Exact metric formulas and separation with no seams |

## Paths and geodesics

| Module | Purpose |
| --- | --- |
| [Unfoldings.Path.AffineSamples](../Unfoldings/Path/AffineSamples.lean) | Continue geodesic coordinate identities across a whole chart interval |
| [Unfoldings.Path.ChartPartition](../Unfoldings/Path/ChartPartition.lean) | Finite strictly ordered chart partitions of actual regular paths |
| [Unfoldings.Path.Chart](../Unfoldings/Path/Chart.lean) | Straight coordinates and uniqueness in isometric charts |
| [Unfoldings.Path.Continuation](../Unfoldings/Path/Continuation.lean) | Unique geodesic continuation from a common initial interval through charts |
| [Unfoldings.Path.ConvexChart](../Unfoldings/Path/ConvexChart.lean) | Geodesic construction in convex charts and ball confinement |
| [Unfoldings.Path.Distance](../Unfoldings/Path/Distance.lean) | Intrinsic distance as an infimum of continuous-path lengths |
| [Unfoldings.Path.EMetricGeodesic](../Unfoldings/Path/EMetricGeodesic.lean) | Geodesic criterion in extended metric spaces |
| [Unfoldings.Path.EMetricShortest](../Unfoldings/Path/EMetricShortest.lean) | Shortest paths in compact extended metric spaces |
| [Unfoldings.Path.FiniteComponent](../Unfoldings/Path/FiniteComponent.lean) | Length-preserving lifts to finite-distance components |
| [Unfoldings.Path.Geodesic](../Unfoldings/Path/Geodesic.lean) | Metric geodesics and endpoint-saturating speed bounds |
| [Unfoldings.Path.InitialChart](../Unfoldings/Path/InitialChart.lean) | A positive chart sample determines the whole initial interval |
| [Unfoldings.Path.Length](../Unfoldings/Path/Length.lean) | Continuous-path length and its composition laws |
| [Unfoldings.Path.LocalDistance](../Unfoldings/Path/LocalDistance.lean) | Local nonexpansion preserves intrinsic path-distance inequalities |
| [Unfoldings.Path.LocalShortcut](../Unfoldings/Path/LocalShortcut.lean) | Geodesic injectivity and avoidance of centers with local strict shortcuts |
| [Unfoldings.Path.MetricGeodesic](../Unfoldings/Path/MetricGeodesic.lean) | Real distance formulas for actual constant-speed geodesics |
| [Unfoldings.Path.Partition](../Unfoldings/Path/Partition.lean) | Exact additive distances along finite monotone geodesic partitions |
| [Unfoldings.Path.Reparameterization](../Unfoldings/Path/Reparameterization.lean) | Bounded-speed replacements preserving the curve image |
| [Unfoldings.Path.Restriction](../Unfoldings/Path/Restriction.lean) | Codomain restriction preserving length and geodesics |
| [Unfoldings.Path.Segment](../Unfoldings/Path/Segment.lean) | Length and speed of Euclidean straight segments |
| [Unfoldings.Path.Shortest](../Unfoldings/Path/Shortest.lean) | Compact families, lower semicontinuity, and shortest paths |
| [Unfoldings.Path.Splice](../Unfoldings/Path/Splice.lean) | Actual constant-speed geodesics after alternative shortest-prefix replacement |
| [Unfoldings.Path.Straight](../Unfoldings/Path/Straight.lean) | Affine straightness of saturated geodesic images |
| [Unfoldings.Path.SubpathBounds](../Unfoldings/Path/SubpathBounds.lean) | Strict subpath-time bounds and density of proper unit-interval times |
| [Unfoldings.Path.Subpath](../Unfoldings/Path/Subpath.lean) | Affine constant-speed subpaths, including reversed intervals |
## Convex polyhedra

| Module | Purpose |
| --- | --- |
| [Unfoldings.Polyhedron.IntervalLink](../Unfoldings/Polyhedron/IntervalLink.lean) | Actual spatial interval links and their endpoint angular-length bound |
| [Unfoldings.Polyhedron.AngularLink](../Unfoldings/Polyhedron/AngularLink.lean) | Actual spatial cyclic link directions, corner angles, and crossing integrals |
| [Unfoldings.Polyhedron.Chords](../Unfoldings/Polyhedron/Chords.lean) | Exact boundary-chord distances and unique intrinsic geodesics |
| [Unfoldings.Polyhedron.Closedness](../Unfoldings/Polyhedron/Closedness.lean) | Derived seam pairing of every original edge and cyclicity at every vertex |
| [Unfoldings.Polyhedron.ConvexCurvature](../Unfoldings/Polyhedron/ConvexCurvature.lean) | Extremality iff positive curvature and avoidance, with no interior premise |
| [Unfoldings.Polyhedron.Convex](../Unfoldings/Polyhedron/Convex.lean) | Geometric convex-boundary adapter and derived geodesics |
| [Unfoldings.Polyhedron.CutDiskConverse](../Unfoldings/Polyhedron/CutDiskConverse.lean) | Construct actual disk homeomorphisms from primal cut trees on convex spheres |
| [Unfoldings.Polyhedron.CutDiskIff](../Unfoldings/Polyhedron/CutDiskIff.lean) | Canonical primal cut multigraph tree iff actual cut disk on a convex sphere |
| [Unfoldings.Polyhedron.CutJordan](../Unfoldings/Polyhedron/CutJordan.lean) | The entire actual cut boundary is a Jordan curve for a primal cut tree |
| [Unfoldings.Polyhedron.CutPlanar](../Unfoldings/Polyhedron/CutPlanar.lean) | Construct whole-cut planar embeddings and actual boundary Jordan cycles |
| [Unfoldings.Polyhedron.CutTree](../Unfoldings/Polyhedron/CutTree.lean) | Construct the actual edge-cut tree from a boundary-preserving disk on a convex polyhedron |
| [Unfoldings.Polyhedron.EdgeExposure](../Unfoldings/Polyhedron/EdgeExposure.lean) | Other convex-boundary points occur arbitrarily near every triangle edge |
| [Unfoldings.Polyhedron.ExtremeCurvature](../Unfoldings/Polyhedron/ExtremeCurvature.lean) | Interior extremality iff positive curvature; extreme-vertex geodesic avoidance |
| [Unfoldings.Polyhedron.ExtremeVertices](../Unfoldings/Polyhedron/ExtremeVertices.lean) | Positive-curvature vertices are actual spatial extreme points |
| [Unfoldings.Polyhedron.FaceIncidence](../Unfoldings/Polyhedron/FaceIncidence.lean) | Embedded original face interiors meet no other original face |
| [Unfoldings.Polyhedron.FaceSupport](../Unfoldings/Polyhedron/FaceSupport.lean) | Actual original face planes support the convex body |
| [Unfoldings.Polyhedron.FigureAngleSum](../Unfoldings/Polyhedron/FigureAngleSum.lean) | Actual polygon angle sum and strict angle bound at interior extreme vertices |
| [Unfoldings.Polyhedron.FigureBoundary](../Unfoldings/Polyhedron/FigureBoundary.lean) | The figure boundary is exactly the sliced spatial surface |
| [Unfoldings.Polyhedron.FigureCenter](../Unfoldings/Polyhedron/FigureCenter.lean) | Genuine central triangles and their constructed positive-angle fan |
| [Unfoldings.Polyhedron.FigureChain](../Unfoldings/Polyhedron/FigureChain.lean) | Consecutive and closing endpoint agreement; exact boundary coverage |
| [Unfoldings.Polyhedron.FigureEdgeInteriors](../Unfoldings/Polyhedron/FigureEdgeInteriors.lean) | Open sections lie in original face interiors and miss other sections |
| [Unfoldings.Polyhedron.FigureEdges](../Unfoldings/Polyhedron/FigureEdges.lean) | Exact radial section segments of incident faces cover the figure boundary |
| [Unfoldings.Polyhedron.FigureFrames](../Unfoldings/Polyhedron/FigureFrames.lean) | Constructed normalized rigid frames of the actual central triangles |
| [Unfoldings.Polyhedron.FigureFullTurn](../Unfoldings/Polyhedron/FigureFullTurn.lean) | Proved nonoverlap and exactly one turn of the actual central fan |
| [Unfoldings.Polyhedron.FigureGermAngles](../Unfoldings/Polyhedron/FigureGermAngles.lean) | Actual apex angles and nondegenerate figure edges |
| [Unfoldings.Polyhedron.FigureGermIncidence](../Unfoldings/Polyhedron/FigureGermIncidence.lean) | Figure endpoints agree exactly for equal germs or seam mates |
| [Unfoldings.Polyhedron.FigureGerms](../Unfoldings/Polyhedron/FigureGerms.lean) | Constructed planar germ points and their boundary segments |
| [Unfoldings.Polyhedron.FigureGlobalFrame](../Unfoldings/Polyhedron/FigureGlobalFrame.lean) | Positive successive turns in one global normalized complex frame |
| [Unfoldings.Polyhedron.FigureHeadings](../Unfoldings/Polyhedron/FigureHeadings.lean) | Actual cumulative headings and exact outer-ray closure |
| [Unfoldings.Polyhedron.FigureIncidence](../Unfoldings/Polyhedron/FigureIncidence.lean) | Every figure-intersecting original face has a corner at the chosen vertex |
| [Unfoldings.Polyhedron.FigureOrientation](../Unfoldings/Polyhedron/FigureOrientation.lean) | Global consistency of the actual central triangle orientations |
| [Unfoldings.Polyhedron.FigurePolygon](../Unfoldings/Polyhedron/FigurePolygon.lean) | Actual simple Mathlib polygon, exact boundary and genuine strict angle budget |
| [Unfoldings.Polyhedron.FigureRadialCover](../Unfoldings/Polyhedron/FigureRadialCover.lean) | Actual central cones cover the punctured plane and have separated open sectors |
| [Unfoldings.Polyhedron.FigureSimpleChain](../Unfoldings/Polyhedron/FigureSimpleChain.lean) | Distinct initial endpoints in the actual cyclic figure chain |
| [Unfoldings.Polyhedron.GeodesicRegularity](../Unfoldings/Polyhedron/GeodesicRegularity.lean) | Every interior geodesic point is regular, giving unique continuation |
| [Unfoldings.Polyhedron.GermDirections](../Unfoldings/Polyhedron/GermDirections.lean) | Actual radial directions, mate invariance and exact crease intersections |
| [Unfoldings.Polyhedron.GermEdges](../Unfoldings/Polyhedron/GermEdges.lean) | Actual edge incidence determines equal or seam-mate link germs |
| [Unfoldings.Polyhedron.GermRays](../Unfoldings/Polyhedron/GermRays.lean) | Equal spatial unit directions classify equal germs and seam mates |
| [Unfoldings.Polyhedron.GermSpatial](../Unfoldings/Polyhedron/GermSpatial.lean) | Spatial far endpoints preserved by actual seam crossings |
| [Unfoldings.Polyhedron.IncidentCrease](../Unfoldings/Polyhedron/IncidentCrease.lean) | Distinct incident planes force an actual crease in the cyclic link |
| [Unfoldings.Polyhedron.LinkDirections](../Unfoldings/Polyhedron/LinkDirections.lean) | Distinct initial radial directions in an embedded cyclic link |
| [Unfoldings.Polyhedron.LocallyPlanar](../Unfoldings/Polyhedron/LocallyPlanar.lean) | Derived regularity when a vertex's incident planes coincide |
| [Unfoldings.Polyhedron.NonextremeAxis](../Unfoldings/Polyhedron/NonextremeAxis.lean) | All incident planes at a nonextreme vertex share a nonzero direction |
| [Unfoldings.Polyhedron.NonextremeCreaseCount](../Unfoldings/Polyhedron/NonextremeCreaseCount.lean) | At most two genuine creases at a nonextreme vertex |
| [Unfoldings.Polyhedron.NonextremeCreases](../Unfoldings/Polyhedron/NonextremeCreases.lean) | Every genuine crease at a nonextreme vertex lies along one common axis |
| [Unfoldings.Polyhedron.NonextremePlanes](../Unfoldings/Polyhedron/NonextremePlanes.lean) | At most two actual incident face planes at a nonextreme vertex |
| [Unfoldings.Polyhedron.NonextremeRegular](../Unfoldings/Polyhedron/NonextremeRegular.lean) | Euclidean ball charts at every nonextreme subdivision vertex |
| [Unfoldings.Polyhedron.PlanarPatch](../Unfoldings/Polyhedron/PlanarPatch.lean) | Whole intrinsic charts from actual planar spatial patches |
| [Unfoldings.Polyhedron.PrescribedHinge](../Unfoldings/Polyhedron/PrescribedHinge.lean) | Construct support hinges with prescribed actual incident planes |
| [Unfoldings.Polyhedron.RegularClassification](../Unfoldings/Polyhedron/RegularClassification.lean) | Regular points are exactly the complement of true extreme vertex points |
| [Unfoldings.Polyhedron.RegularPoints](../Unfoldings/Polyhedron/RegularPoints.lean) | Every actual nonvertex convex-boundary point is regular |
| [Unfoldings.Polyhedron.TangentHinge](../Unfoldings/Polyhedron/TangentHinge.lean) | The whole actual tangent image equals the constructed spatial support hinge |
| [Unfoldings.Polyhedron.VertexFigure](../Unfoldings/Polyhedron/VertexFigure.lean) | Compact convex planar vertex figures, finite hulls, interior centers and circular boundaries |
| [Unfoldings.Polyhedron.VertexHinge](../Unfoldings/Polyhedron/VertexHinge.lean) | Constructed local support hinges at nonextreme vertices, allowing coincident planes |
| [Unfoldings.Polyhedron.VertexNeighborhood](../Unfoldings/Polyhedron/VertexNeighborhood.lean) | Small spatial vertex stars and two-plane neighborhoods |
| [Unfoldings.Polyhedron.VertexSliceInterior](../Unfoldings/Polyhedron/VertexSliceInterior.lean) | Actual vertex sections with a spatial interior center |
| [Unfoldings.Polyhedron.VertexSlice](../Unfoldings/Polyhedron/VertexSlice.lean) | Constructed nonempty transverse sections at spatial extreme vertices |
## Cone geometry

| Module | Purpose |
| --- | --- |
| [Unfoldings.Cone.AngularBoundary](../Unfoldings/Cone/AngularBoundary.lean) | Outer fan banks correspond exactly to the boundary line with preserved radii |
| [Unfoldings.Cone.AngularChord](../Unfoldings/Cone/AngularChord.lean) | Exact intrinsic lengths of covered chords in reentrant fans |
| [Unfoldings.Cone.AngularCoordinates](../Unfoldings/Cone/AngularCoordinates.lean) | Closed headings, bank coordinates and full-plane coverage |
| [Unfoldings.Cone.AngularFan](../Unfoldings/Cone/AngularFan.lean) | Slit sector fans, cumulative real headings and planar developments |
| [Unfoldings.Cone.AngularFibers](../Unfoldings/Cone/AngularFibers.lean) | All closed-bank fibers at one full turn |
| [Unfoldings.Cone.AngularHeadingShortcut](../Unfoldings/Cone/AngularHeadingShortcut.lean) | Strict shortcuts across multiple angular pieces |
| [Unfoldings.Cone.AngularHomeomorph](../Unfoldings/Cone/AngularHomeomorph.lean) | Seam-compatible angle changes and half-plane topology at arbitrary total angles |
| [Unfoldings.Cone.AngularImages](../Unfoldings/Cone/AngularImages.lean) | Genuine rigid piece images and their open heading intervals |
| [Unfoldings.Cone.AngularInjective](../Unfoldings/Cone/AngularInjective.lean) | Boundary-inclusive development injectivity below a full turn |
| [Unfoldings.Cone.AngularMetric](../Unfoldings/Cone/AngularMetric.lean) | Common fan apex, exact radial distances and ordinary metric |
| [Unfoldings.Cone.AngularOverlap](../Unfoldings/Cone/AngularOverlap.lean) | Exact nonoverlap criterion and arbitrary-radius interior overlaps |
| [Unfoldings.Cone.AngularSector](../Unfoldings/Cone/AngularSector.lean) | Exact Euclidean sector metric when total angle is less than pi |
| [Unfoldings.Cone.AngularShortcut](../Unfoldings/Cone/AngularShortcut.lean) | Strict intrinsic shortcuts and apex avoidance in convex angular fans |
| [Unfoldings.Cone.Apex](../Unfoldings/Cone/Apex.lean) | Common tangent apex derived from vertex-link connectivity |
| [Unfoldings.Cone.AppendFirst](../Unfoldings/Cone/AppendFirst.lean) | A repeated first sector with exact continued real headings |
| [Unfoldings.Cone.AppendMap](../Unfoldings/Cone/AppendMap.lean) | Nonexpanding cyclic maps continued across their closing bank |
| [Unfoldings.Cone.BoundaryTopology](../Unfoldings/Cone/BoundaryTopology.lean) | Actual boundary tangent half-planes and whole intrinsic boundary-vertex charts |
| [Unfoldings.Cone.CellShortcut](../Unfoldings/Cone/CellShortcut.lean) | Strict shortcuts between specified cell representatives on the selected sheet |
| [Unfoldings.Cone.Charts](../Unfoldings/Cone/Charts.lean) | Constructed whole-ball cone charts for spatial foldings |
| [Unfoldings.Cone.ConsecutiveCompatibility](../Unfoldings/Cone/ConsecutiveCompatibility.lean) | Consecutive actual seams agree in angular coordinates |
| [Unfoldings.Cone.CornerDirection](../Unfoldings/Cone/CornerDirection.lean) | Actual corner frames oriented by the chosen initial germ |
| [Unfoldings.Cone.CornerSector](../Unfoldings/Cone/CornerSector.lean) | Actual triangle wedges isometric to their angular sectors |
| [Unfoldings.Cone.CyclicDevelopment](../Unfoldings/Cone/CyclicDevelopment.lean) | Constructed surjective planar map of full-turn actual fans |
| [Unfoldings.Cone.CyclicIsometry](../Unfoldings/Cone/CyclicIsometry.lean) | Full-turn cyclic tangent fans isometric to the Euclidean plane |
| [Unfoldings.Cone.CyclicSeams](../Unfoldings/Cone/CyclicSeams.lean) | Actual closing seams and identification of the outer radial banks |
| [Unfoldings.Cone.CyclicShortcut](../Unfoldings/Cone/CyclicShortcut.lean) | Shortcuts on either side of a cyclic fan, including across its slit |
| [Unfoldings.Cone.Dilation](../Unfoldings/Cone/Dilation.lean) | Exact radial similarities and reciprocal homeomorphisms |
| [Unfoldings.Cone.FlatCharts](../Unfoldings/Cone/FlatCharts.lean) | Whole intrinsic Euclidean charts at actual flat interior vertices |
| [Unfoldings.Cone.FlatGeodesics](../Unfoldings/Cone/FlatGeodesics.lean) | Constructed shortest paths, straight coordinates and local ambient uniqueness |
| [Unfoldings.Cone.GermFrames](../Unfoldings/Cone/GermFrames.lean) | Exact initial/terminal coordinates on the actual radial banks |
| [Unfoldings.Cone.HeadingEquality](../Unfoldings/Cone/HeadingEquality.lean) | Real heading uniqueness across overlapping pointed intervals |
| [Unfoldings.Cone.HeadingInterval](../Unfoldings/Cone/HeadingInterval.lean) | Positive pointed intervals enclosing nearby headings, including equality |
| [Unfoldings.Cone.HeadingLift](../Unfoldings/Cone/HeadingLift.lean) | Isometric lifts of selected heading sectors in arbitrary overlapping fans |
| [Unfoldings.Cone.HeadingSector](../Unfoldings/Cone/HeadingSector.lean) | Convex rotated sectors with closed real heading bounds |
| [Unfoldings.Cone.HeadingShortcut](../Unfoldings/Cone/HeadingShortcut.lean) | Strict shortcuts on selected sheets, preserved by radial nonexpansion |
| [Unfoldings.Cone.IntervalCompatibility](../Unfoldings/Cone/IntervalCompatibility.lean) | Actual seams respect the inverse interval comparison |
| [Unfoldings.Cone.IntervalIsometry](../Unfoldings/Cone/IntervalIsometry.lean) | Boundary tangent fans isometric to their actual angular models |
| [Unfoldings.Cone.IntervalSeams](../Unfoldings/Cone/IntervalSeams.lean) | Every interval-link radial seam is consecutive |
| [Unfoldings.Cone.LinkAngles](../Unfoldings/Cone/LinkAngles.lean) | Genuine angle lists from the constructed retained-link order |
| [Unfoldings.Cone.LinkComparison](../Unfoldings/Cone/LinkComparison.lean) | Surjective nonexpanding angular-to-tangent comparison |
| [Unfoldings.Cone.LinkSeams](../Unfoldings/Cone/LinkSeams.lean) | Actual retained radial seams along ordered corner chains |
| [Unfoldings.Cone.LinkShortcut](../Unfoldings/Cone/LinkShortcut.lean) | Strict angular shortcuts transferred to actual tangent metrics |
| [Unfoldings.Cone.Neighborhood](../Unfoldings/Cone/Neighborhood.lean) | Exact local cone metrics and whole-neighborhood coverage |
| [Unfoldings.Cone.ParametrizedChart](../Unfoldings/Cone/ParametrizedChart.lean) | Whole vertex charts from constructed planar tangent parametrizations |
| [Unfoldings.Cone.Paths](../Unfoldings/Cone/Paths.lean) | Intrinsic path metric and explicit radial geodesics |
| [Unfoldings.Cone.PolarEquality](../Unfoldings/Cone/PolarEquality.lean) | Equality of closed full-turn polar coordinates, including outer banks |
| [Unfoldings.Cone.Polar](../Unfoldings/Cone/Polar.lean) | Real-heading polar maps, exact injectivity criterion and overlap witnesses |
| [Unfoldings.Cone.Proper](../Unfoldings/Cone/Proper.lean) | Compact closed tangent balls, properness and completeness |
| [Unfoldings.Cone.Radial](../Unfoldings/Cone/Radial.lean) | Exact radial distance and finite ordinary tangent metric |
| [Unfoldings.Cone.SeamBoundary](../Unfoldings/Cone/SeamBoundary.lean) | Actual radial banks of retained seams |
| [Unfoldings.Cone.SeamCoordinates](../Unfoldings/Cone/SeamCoordinates.lean) | Directed angular coordinates of every actual radial seam point |
| [Unfoldings.Cone.SeamRadius](../Unfoldings/Cone/SeamRadius.lean) | Actual radial seam witnesses at every nonnegative radius |
| [Unfoldings.Cone.SectorChange](../Unfoldings/Cone/SectorChange.lean) | Bounded linear sector changes preserving both boundary-ray coordinates |
| [Unfoldings.Cone.SectorClosed](../Unfoldings/Cone/SectorClosed.lean) | Closed polar coordinates for sectors and the whole plane |
| [Unfoldings.Cone.SectorCoordinates](../Unfoldings/Cone/SectorCoordinates.lean) | Positive-span sectors, ambient coordinates and interiors |
| [Unfoldings.Cone.SectorInterior](../Unfoldings/Cone/SectorInterior.lean) | Positive-radius open-heading coordinates for actual sector interiors |
| [Unfoldings.Cone.SectorReflection](../Unfoldings/Cone/SectorReflection.lean) | Isometric bank exchange by angular-bisector reflection |
| [Unfoldings.Cone.SectorShortcut](../Unfoldings/Cone/SectorShortcut.lean) | Strict chord shortcuts for nonzero points of pointed sectors |
| [Unfoldings.Cone.Sector](../Unfoldings/Cone/Sector.lean) | Real-angle sectors as positive spans of their boundary rays |
| [Unfoldings.Cone.SmallDilation](../Unfoldings/Cone/SmallDilation.lean) | One positive scale places any two tangent points in an apex ball |
| [Unfoldings.Cone.SpatialConvexLift](../Unfoldings/Cone/SpatialConvexLift.lean) | Isometric inverse tangent folding on every convex spatial subset |
| [Unfoldings.Cone.SpatialEmbedding](../Unfoldings/Cone/SpatialEmbedding.lean) | Proper tangent folding and closed spatial embeddings of actual uncut fans |
| [Unfoldings.Cone.SpatialHinge](../Unfoldings/Cone/SpatialHinge.lean) | Transfer entire spatial hinge parametrizations to intrinsic metric charts |
| [Unfoldings.Cone.SpatialParametrization](../Unfoldings/Cone/SpatialParametrization.lean) | Finite piecewise rigid spatial parametrizations give intrinsic tangent isometries |
| [Unfoldings.Cone.SpatialRange](../Unfoldings/Cone/SpatialRange.lean) | Exact radial homogeneity of the actual tangent image |
| [Unfoldings.Cone.Spatial](../Unfoldings/Cone/Spatial.lean) | Extended spatial foldings and tangent-cell isometries |
| [Unfoldings.Cone.SurfaceComparison](../Unfoldings/Cone/SurfaceComparison.lean) | Local metric comparison from tangent fans to original surfaces |
| [Unfoldings.Cone.SurfaceTags](../Unfoldings/Cone/SurfaceTags.lean) | Local maps from tangent wedges into original triangle cells |
| [Unfoldings.Cone.TangentAngularCells](../Unfoldings/Cone/TangentAngularCells.lean) | Directed angular coordinates on every actual tangent cell |
| [Unfoldings.Cone.TangentComparison](../Unfoldings/Cone/TangentComparison.lean) | Local metric comparison from original surfaces to tangent fans |
| [Unfoldings.Cone.TangentShortcut](../Unfoldings/Cone/TangentShortcut.lean) | Strict apex shortcuts for all actual positive-curvature tangent pairs |
| [Unfoldings.Cone.Tangent](../Unfoldings/Cone/Tangent.lean) | Actual wedge cells and radially extended seam gluings |
| [Unfoldings.Cone.TriangleInclusion](../Unfoldings/Cone/TriangleInclusion.lean) | Original triangles included in their actual tangent wedges |
| [Unfoldings.Cone.VertexAvoidance](../Unfoldings/Cone/VertexAvoidance.lean) | Original intrinsic geodesics avoid positive-curvature interior vertices |
## Euclidean geometry

| Module | Purpose |
| --- | --- |
| [Unfoldings.Geometry.CompactHalfplanes](../Unfoldings/Geometry/CompactHalfplanes.lean) | Compact proper finite affine-halfplane intersections have exact finite segment boundaries |
| [Unfoldings.Geometry.ConvexPolygonCover](../Unfoldings/Geometry/ConvexPolygonCover.lean) | Exact finite center-triangle coverage of compact convex polygons, discarding degenerate rim cells |
| [Unfoldings.Geometry.ConvexPolygonFan](../Unfoldings/Geometry/ConvexPolygonFan.lean) | Actual center triangles and interior separation from distinct boundary rays |
| [Unfoldings.Geometry.ConvexPolygonPartition](../Unfoldings/Geometry/ConvexPolygonPartition.lean) | Subdivide boundary overlaps to construct genuine disjoint-interior finite triangle partitions |
| [Unfoldings.Geometry.ConvexRayBoundary](../Unfoldings/Geometry/ConvexRayBoundary.lean) | Actual frontier points on all nonzero rays from arbitrary convex-body interior centers |
| [Unfoldings.Geometry.ConvexSegmentExit](../Unfoldings/Geometry/ConvexSegmentExit.lean) | Strict frontier crossings and slight endpoint extensions of straight segments |
| [Unfoldings.Geometry.TriangleRadial](../Unfoldings/Geometry/TriangleRadial.lean) | Interior triangle points lie strictly on rays to the opposite open edge |
| [Unfoldings.Geometry.ConvexRadialTails](../Unfoldings/Geometry/ConvexRadialTails.lean) | Outward frontier rays leave a convex closure and preserve distinct endpoint labels |
| [Unfoldings.Geometry.FiniteAffineTail](../Unfoldings/Geometry/FiniteAffineTail.lean) | A fixed affine minimizer beyond a threshold for any finite real affine family |
| [Unfoldings.Geometry.FiniteConvexTrace](../Unfoldings/Geometry/FiniteConvexTrace.lean) | Finite labeled segment partitions for arbitrary finite closed convex covers |
| [Unfoldings.Geometry.AcuteWedgeFrame](../Unfoldings/Geometry/AcuteWedgeFrame.lean) | Construct an orthogonal complex frame with strict margins around an acute direction wedge |
| [Unfoldings.Geometry.AngleConeBound](../Unfoldings/Geometry/AngleConeBound.lean) | Convex direction wedges inherit angular caps and robust positive inner products |
| [Unfoldings.Geometry.ComplexRotationFrame](../Unfoldings/Geometry/ComplexRotationFrame.lean) | Positive complex isometries commute with rigid phase rotations |
| [Unfoldings.Geometry.CyclicDisplacements](../Unfoldings/Geometry/CyclicDisplacements.lean) | Additive displacement cancellation around a region with one entrance and exit |
| [Unfoldings.Geometry.QuadrantRotationOrder](../Unfoldings/Geometry/QuadrantRotationOrder.lean) | A nonnegative small quadrant rotation orders actual vector coordinates |
| [Unfoldings.Geometry.RobustQuadrant](../Unfoldings/Geometry/RobustQuadrant.lean) | Small angular perturbations of a closed acute wedge stay inside its open quadrant |
| [Unfoldings.Geometry.StrictQuadrantRotation](../Unfoldings/Geometry/StrictQuadrantRotation.lean) | Positive small rotations inside an open quadrant strictly order both coordinates |
| [Unfoldings.Geometry.ThreeSectorFrames](../Unfoldings/Geometry/ThreeSectorFrames.lean) | Numerical positive quadrant margins for all three acute sectors |
| [Unfoldings.Geometry.WedgeRotationFrame](../Unfoldings/Geometry/WedgeRotationFrame.lean) | Positive acute-wedge frames preserve actual signed complex rotations |
| [Unfoldings.Geometry.ComplexHeadingTransport](../Unfoldings/Geometry/ComplexHeadingTransport.lean) | Compose genuine complex directions with signed real phase corrections before taking absolute errors |
| [Unfoldings.Geometry.ComplexHingeTurn](../Unfoldings/Geometry/ComplexHingeTurn.lean) | Halfplane hinge estimates and signed area preservation in a common complex frame |
| [Unfoldings.Geometry.DirectionFrame](../Unfoldings/Geometry/DirectionFrame.lean) | Orthogonal planar coordinates put any actual section direction on the positive horizontal axis |
| [Unfoldings.Geometry.HingeTurnBound](../Unfoldings/Geometry/HingeTurnBound.lean) | Same-halfplane planar turns are bounded by spatial bend when seam angles match |
| [Unfoldings.Geometry.AngleMonotoneCoordinates](../Unfoldings/Geometry/AngleMonotoneCoordinates.lean) | An acute direction wedge supplies a monotone coordinate in every orthogonal frame |
| [Unfoldings.Geometry.AngleMonotoneCrossings](../Unfoldings/Geometry/AngleMonotoneCrossings.lean) | Acute angle-monotone paths have signed ray-crossing counts of magnitude at most one in every frame |
| [Unfoldings.Geometry.LineCrossingSides](../Unfoldings/Geometry/LineCrossingSides.lean) | Actual determinants determine directed side changes at affine line crossings |
| [Unfoldings.Geometry.LineTransverse](../Unfoldings/Geometry/LineTransverse.lean) | An endpoint-avoiding line meets an edge only transversely |
| [Unfoldings.Geometry.PolarAngleBound](../Unfoldings/Geometry/PolarAngleBound.lean) | Genuine angular distance is bounded by any real unreduced heading difference |
| [Unfoldings.Geometry.PositiveDirectionFrame](../Unfoldings/Geometry/PositiveDirectionFrame.lean) | Positive orthogonal coordinates align a prescribed direction and identify transverse determinant signs |
| [Unfoldings.Geometry.RayAvoidance](../Unfoldings/Geometry/RayAvoidance.lean) | Choose endpoints in any open set so lines from a fixed origin avoid finitely many exceptional points |
| [Unfoldings.Geometry.ConcaveSecants](../Unfoldings/Geometry/ConcaveSecants.lean) | Concave secant inclinations telescope independently of partition size |
| [Unfoldings.Geometry.LevelCrossings](../Unfoldings/Geometry/LevelCrossings.lean) | Actual affine level intersections and signed horizontal-ray counts for coordinate-monotone chains |
| [Unfoldings.Geometry.RayCounterChanges](../Unfoldings/Geometry/RayCounterChanges.lean) | Nonzero ray-counter changes are actual original-segment level intersections with exact signed jumps |
| [Unfoldings.Geometry.RelativeAngleBound](../Unfoldings/Geometry/RelativeAngleBound.lean) | Transfer an oriented planar reference-ray alignment to all directions with angular distortion budgets |
| [Unfoldings.Geometry.SectionRayCounter](../Unfoldings/Geometry/SectionRayCounter.lean) | Physical segment counter changes along a section have the actual oriented crossing sign |
| [Unfoldings.Geometry.SharedEdgeOpening](../Unfoldings/Geometry/SharedEdgeOpening.lean) | A shared geometric edge and disjoint triangle interiors force opposite-side opening |
| [Unfoldings.Geometry.SlopeAngles](../Unfoldings/Geometry/SlopeAngles.lean) | Genuine angles of slope vectors equal absolute real arctangent differences |
| [Unfoldings.Geometry.ThreeSectorCoordinates](../Unfoldings/Geometry/ThreeSectorCoordinates.lean) | Each near-quadrant supplies an upward, leftward, or downward monotone ambient coordinate |
| [Unfoldings.Geometry.CyclicRotations](../Unfoldings/Geometry/CyclicRotations.lean) | Cancel rotations across a finite region with one entrance and one exit |
| [Unfoldings.Geometry.IntervalConeOrientation](../Unfoldings/Geometry/IntervalConeOrientation.lean) | Adjacent hinge separation gives a common orientation while allowing distant overlap |
| [Unfoldings.Geometry.MeshLinearProgress](../Unfoldings/Geometry/MeshLinearProgress.lean) | Original outgoing quadrant edges after invertible planar coordinate changes |
| [Unfoldings.Geometry.ThreeSectorAcute](../Unfoldings/Geometry/ThreeSectorAcute.lean) | One positive numerical parameter preserves every supplied acute angle margin |
| [Unfoldings.Geometry.ThreeSectorMesh](../Unfoldings/Geometry/ThreeSectorMesh.lean) | Mesh-independent acuteness preservation and original-edge progress in all three sectors |
| [Unfoldings.Geometry.ThreeSectorRays](../Unfoldings/Geometry/ThreeSectorRays.lean) | Actual sector banks, inverse coordinates, and strict acute width bounds |
| [Unfoldings.Geometry.ThreeSectors](../Unfoldings/Geometry/ThreeSectors.lean) | Three disjoint near-quadrants cover a backward halfplane and preserve position labels |
| [Unfoldings.Geometry.HalfplaneFan](../Unfoldings/Geometry/HalfplaneFan.lean) | A consistently oriented halfplane fan has exact endpoint angle without wraparound |
| [Unfoldings.Geometry.PlanarAngleAddition](../Unfoldings/Geometry/PlanarAngleAddition.lean) | Exact angular addition inside an oriented planar halfplane |
| [Unfoldings.Geometry.PlanarConeOrientation](../Unfoldings/Geometry/PlanarConeOrientation.lean) | Disjoint genuine planar cones force consistent interval orientation |
| [Unfoldings.Geometry.PlanarConjugation](../Unfoldings/Geometry/PlanarConjugation.lean) | A planar reflection reverses signed orientation and preserves actual angles |
| [Unfoldings.Geometry.AngularCrofton](../Unfoldings/Geometry/AngularCrofton.lean) | Discrete spherical crossing integrals and the measure-theoretic Gauss reduction |
| [Unfoldings.Geometry.ConeBoundaryRays](../Unfoldings/Geometry/ConeBoundaryRays.lean) | A planar supported convex cone has at most two boundary ray directions |
| [Unfoldings.Geometry.CyclicSignChanges](../Unfoldings/Geometry/CyclicSignChanges.lean) | Even strict sign-change counts and exact counts for nonconstant bounded cyclic sequences |
| [Unfoldings.Geometry.SolidAngleHemisphere](../Unfoldings/Geometry/SolidAngleHemisphere.lean) | Antipodal symmetry halves sign-change measures within every genuine hemisphere |
| [Unfoldings.Geometry.SpatialLune](../Unfoldings/Geometry/SpatialLune.lean) | Exact solid-angle measures for arbitrary spatial lunes and scalar-product sign changes |
| [Unfoldings.Geometry.SpatialPairFrame](../Unfoldings/Geometry/SpatialPairFrame.lean) | Orthogonal frames put any nonzero spatial pair into its actual angular normal form |
| [Unfoldings.Geometry.TwoVectorFrame](../Unfoldings/Geometry/TwoVectorFrame.lean) | Complete a spatial orthonormal pair and decompose arbitrary vector pairs |
| [Unfoldings.Geometry.ConvexPacking](../Unfoldings/Geometry/ConvexPacking.lean) | Haar measure bounds for finite convex packings with disjoint interiors and boundary contacts |
| [Unfoldings.Geometry.ConeOrientation](../Unfoldings/Geometry/ConeOrientation.lean) | Disjoint consecutive ray cones have consistent orientation; cyclic fans make one full turn in either orientation |
| [Unfoldings.Geometry.CornerDirections](../Unfoldings/Geometry/CornerDirections.lean) | Disjoint triangle interiors force disjoint direction cones at a common corner |
| [Unfoldings.Geometry.CyclicRays](../Unfoldings/Geometry/CyclicRays.lean) | Genuine disjoint cyclic ray fans make exactly one full turn, with exact cumulative headings |
| [Unfoldings.Geometry.EuclideanArea](../Unfoldings/Geometry/EuclideanArea.lean) | Nonexpansive maps decrease normalized Euclidean Hausdorff measure |
| [Unfoldings.Geometry.AngleMeasure](../Unfoldings/Geometry/AngleMeasure.lean) | Canonical angular length on Real.Angle and exact angular ball measures |
| [Unfoldings.Geometry.AngularLune](../Unfoldings/Geometry/AngularLune.lean) | Angular balls identify the actual strict half-plane signs of a lune |
| [Unfoldings.Geometry.Azimuth](../Unfoldings/Geometry/Azimuth.lean) | Orthogonal equivariance and Haar uniqueness give the uniform spatial azimuth law |
| [Unfoldings.Geometry.EquivariantMeasure](../Unfoldings/Geometry/EquivariantMeasure.lean) | Almost-equivariant observables of measure-preserving shifts have invariant laws |
| [Unfoldings.Geometry.EuclideanMeasure](../Unfoldings/Geometry/EuclideanMeasure.lean) | Quantitative Lipschitz estimates for normalized Euclidean Hausdorff measure |
| [Unfoldings.Geometry.LuneMeasure](../Unfoldings/Geometry/LuneMeasure.lean) | A spherical lune of aperture theta has solid angle twice theta |
| [Unfoldings.Geometry.SolidAngle](../Unfoldings/Geometry/SolidAngle.lean) | Solid angle induced by spatial volume, with conical formula and full-sphere normalization |
| [Unfoldings.Geometry.SolidAngleSymmetry](../Unfoldings/Geometry/SolidAngleSymmetry.lean) | Orthogonal invariance and zero solid angle of great circles and linear hyperplanes |
| [Unfoldings.Geometry.Normalize](../Unfoldings/Geometry/Normalize.lean) | Exact radial-angular distance decomposition and contraction outside the unit ball |
| [Unfoldings.Geometry.SupportingSlopes](../Unfoldings/Geometry/SupportingSlopes.lean) | Concave-function supporting slopes have disjoint interior regions at distinct contact points |
| [Unfoldings.Geometry.AcuteProgress](../Unfoldings/Geometry/AcuteProgress.lean) | An acute corner containing a forward point has an original forward incident edge |
| [Unfoldings.Geometry.BankRadialOrder](../Unfoldings/Geometry/BankRadialOrder.lean) | Matched coordinate increments imply equal-radius order in a quadrant |
| [Unfoldings.Geometry.ChainConstruction](../Unfoldings/Geometry/ChainConstruction.lean) | Construct chains from vectors or headings and bound nonnegative prefix sums |
| [Unfoldings.Geometry.EmptyWedge](../Unfoldings/Geometry/EmptyWedge.lean) | Empty positive cone gaps at finite-set linear-functional maxima |
| [Unfoldings.Geometry.MeshProgress](../Unfoldings/Geometry/MeshProgress.lean) | Original outgoing quadrant edges from finite closed triangle covers |
| [Unfoldings.Geometry.MeshWedge](../Unfoldings/Geometry/MeshWedge.lean) | Uniform small shears turn mesh quadrant progress into acute-wedge progress |
| [Unfoldings.Geometry.Shear](../Unfoldings/Geometry/Shear.lean) | Uniform acuteness preservation under small invertible shears |
| [Unfoldings.Geometry.ShearWedge](../Unfoldings/Geometry/ShearWedge.lean) | Sheared quadrants are acute direction wedges and give radial monotonicity |
| [Unfoldings.Geometry.TriangleAffine](../Unfoldings/Geometry/TriangleAffine.lean) | Actual nondegenerate triangles and full carriers under injective affine maps |
| [Unfoldings.Geometry.AngleMonotone](../Unfoldings/Geometry/AngleMonotone.lean) | Direction wedges of width at most pi/2 imply whole-edge radial monotonicity |
| [Unfoldings.Geometry.ChainLinear](../Unfoldings/Geometry/ChainLinear.lean) | Linear coordinate order and strict-coordinate uniqueness on polygonal chains |
| [Unfoldings.Geometry.ChainOrder](../Unfoldings/Geometry/ChainOrder.lean) | Radial distance inequalities across different chain edges |
| [Unfoldings.Geometry.PairedChains](../Unfoldings/Geometry/PairedChains.lean) | Matched coordinate-increment inequalities imply whole-chain vertical order |
| [Unfoldings.Geometry.PolygonalChain](../Unfoldings/Geometry/PolygonalChain.lean) | Finite polygonal chains, edge positions, and outward scalar-product criteria |
| [Unfoldings.Geometry.RadialChain](../Unfoldings/Geometry/RadialChain.lean) | Strict radial distances and uniqueness of actual circle intersections |
| [Unfoldings.Geometry.RadialChainPoints](../Unfoldings/Geometry/RadialChainPoints.lean) | Radial monotonicity from arbitrary points inside edges |
| [Unfoldings.Geometry.RadialSegment](../Unfoldings/Geometry/RadialSegment.lean) | Whole-segment radial monotonicity iff an outward scalar product |
| [Unfoldings.Geometry.UniformAngles](../Unfoldings/Geometry/UniformAngles.lean) | Uniform angle continuity on a compact annulus |

| Module | Purpose |
| --- | --- |
| [Unfoldings.Geometry.AdjacentBoundaryEdges](../Unfoldings/Geometry/AdjacentBoundaryEdges.lean) | Simple convex boundary edges keep the same radial orientation |
| [Unfoldings.Geometry.AffineArrangement](../Unfoldings/Geometry/AffineArrangement.lean) | General finite affine chamber covers of regular closed sets |
| [Unfoldings.Geometry.AffineEnd](../Unfoldings/Geometry/AffineEnd.lean) | Finite-dimensional rigid self-embeddings are surjective and open |
| [Unfoldings.Geometry.AffineMaximum](../Unfoldings/Geometry/AffineMaximum.lean) | Local maxima force affine functionals to be constant |
| [Unfoldings.Geometry.AffineOrientation](../Unfoldings/Geometry/AffineOrientation.lean) | Affine signed-area scaling and rigid preservation of relative signs |
| [Unfoldings.Geometry.AffinePlaneRange](../Unfoldings/Geometry/AffinePlaneRange.lean) | Common-point affine planes agree when their linear directions agree |
| [Unfoldings.Geometry.AffineSupport](../Unfoldings/Geometry/AffineSupport.lean) | Nonzero affine equations for genuine bisectors and triangle edge lines |
| [Unfoldings.Geometry.Affine](../Unfoldings/Geometry/Affine.lean) | Rigid edge extensions and line reflection |
| [Unfoldings.Geometry.AngleSeparation](../Unfoldings/Geometry/AngleSeparation.lean) | Strict angular inequality through a direction outside a level plane |
| [Unfoldings.Geometry.Angles](../Unfoldings/Geometry/Angles.lean) | Positive Euclidean corner angles and triangle angle sums |
| [Unfoldings.Geometry.ArrangementBoundary](../Unfoldings/Geometry/ArrangementBoundary.lean) | Exact finite inside/outside chamber boundary decompositions |
| [Unfoldings.Geometry.BallRigidity](../Unfoldings/Geometry/BallRigidity.lean) | Actual isometric open-ball maps extend to whole affine isometries |
| [Unfoldings.Geometry.Barycentric](../Unfoldings/Geometry/Barycentric.lean) | Affine coordinates and local edge half-planes |
| [Unfoldings.Geometry.BoundaryChord](../Unfoldings/Geometry/BoundaryChord.lean) | A chord through an interior boundary point stays on the convex frontier |
| [Unfoldings.Geometry.BoundaryCornerAngle](../Unfoldings/Geometry/BoundaryCornerAngle.lean) | Exact splitting of convex boundary corner angles by an interior center |
| [Unfoldings.Geometry.BoundaryHalfplanes](../Unfoldings/Geometry/BoundaryHalfplanes.lean) | Every convex boundary edge supports its whole planar body |
| [Unfoldings.Geometry.CompactCollinear](../Unfoldings/Geometry/CompactCollinear.lean) | Compact convex sets on proper planar affine lines are segments |
| [Unfoldings.Geometry.ComplexArea](../Unfoldings/Geometry/ComplexArea.lean) | Signed area in standard complex orthonormal coordinates |
| [Unfoldings.Geometry.ComplexTurn](../Unfoldings/Geometry/ComplexTurn.lean) | Exact positive angular successor formula with unreduced headings |
| [Unfoldings.Geometry.ConvexBoundaryEdges](../Unfoldings/Geometry/ConvexBoundaryEdges.lean) | Supporting functionals of boundary segments and noncollinear interior centers |
| [Unfoldings.Geometry.ConvexBoundaryRays](../Unfoldings/Geometry/ConvexBoundaryRays.lean) | Unique convex-frontier point on a positive ray from an interior origin |
| [Unfoldings.Geometry.ConvexCover](../Unfoldings/Geometry/ConvexCover.lean) | Common Lipschitz bounds across finite closed covers |
| [Unfoldings.Geometry.ConvexLocalBounds](../Unfoldings/Geometry/ConvexLocalBounds.lean) | Convex subtype center bounds imply global nonexpansion |
| [Unfoldings.Geometry.ConvexLocalRigidity](../Unfoldings/Geometry/ConvexLocalRigidity.lean) | Local isometries determine one rigid motion on a full-dimensional convex cell |
| [Unfoldings.Geometry.ConvexPatchRigidity](../Unfoldings/Geometry/ConvexPatchRigidity.lean) | Overlapping convex face patches force equality of their whole rigid motions |
| [Unfoldings.Geometry.ConvexRigidity](../Unfoldings/Geometry/ConvexRigidity.lean) | Actual isometries on convex sets with interior extend rigidly through the boundary |
| [Unfoldings.Geometry.CornerEdges](../Unfoldings/Geometry/CornerEdges.lean) | Radial edge lines inside a triangle remain on the actual edge |
| [Unfoldings.Geometry.CornerFrame](../Unfoldings/Geometry/CornerFrame.lean) | Constructed rigid apex/first-ray/upper-side normalization |
| [Unfoldings.Geometry.CornerSpan](../Unfoldings/Geometry/CornerSpan.lean) | Unique boundary-ray coordinates and actual wedge interiors |
| [Unfoldings.Geometry.Corner](../Unfoldings/Geometry/Corner.lean) | Supporting wedges and actual corner wedge-ball geometry |
| [Unfoldings.Geometry.EdgeChordInterior](../Unfoldings/Geometry/EdgeChordInterior.lean) | Chords between different edge interiors enter a triangle interior |
| [Unfoldings.Geometry.EdgeCoordinates](../Unfoldings/Geometry/EdgeCoordinates.lean) | Centered affine half-plane coordinates on actual triangle edge neighborhoods |
| [Unfoldings.Geometry.EdgeExt](../Unfoldings/Geometry/EdgeExt.lean) | Continuous full-edge maps agree if they agree away from their corner points |
| [Unfoldings.Geometry.EdgeIdentification](../Unfoldings/Geometry/EdgeIdentification.lean) | Construct full-edge isometries from matching endpoint lengths and orientation labels |
| [Unfoldings.Geometry.EdgeLine](../Unfoldings/Geometry/EdgeLine.lean) | Affine edge agreement extends to the entire supporting line |
| [Unfoldings.Geometry.EdgeParameters](../Unfoldings/Geometry/EdgeParameters.lean) | Strict edge interpolation avoids all original triangle vertices |
| [Unfoldings.Geometry.EdgePerfect](../Unfoldings/Geometry/EdgePerfect.lean) | Every neighborhood in a genuine closed edge contains a nonvertex point |
| [Unfoldings.Geometry.EdgeSides](../Unfoldings/Geometry/EdgeSides.lean) | Edge membership and proportional supporting coordinates |
| [Unfoldings.Geometry.Edge](../Unfoldings/Geometry/Edge.lean) | Edge intersections and endpoint preservation by isometries |
| [Unfoldings.Geometry.Endpoints](../Unfoldings/Geometry/Endpoints.lean) | Endpoint permutations induced by full-edge isometries |
| [Unfoldings.Geometry.ExtremeSeparation](../Unfoldings/Geometry/ExtremeSeparation.lean) | Strict finite-hull supporting functionals with a uniform margin |
| [Unfoldings.Geometry.FiniteAffineSelection](../Unfoldings/Geometry/FiniteAffineSelection.lean) | Proper affine supports for coincidences and constancy of finite continuous affine selections |
| [Unfoldings.Geometry.FiniteAngles](../Unfoldings/Geometry/FiniteAngles.lean) | Every nonempty finite point list has a nonstraight chosen corner |
| [Unfoldings.Geometry.FrontierProjection](../Unfoldings/Geometry/FrontierProjection.lean) | Continuous gauge projection from an actual body interior point |
| [Unfoldings.Geometry.FrontierRays](../Unfoldings/Geometry/FrontierRays.lean) | Gauge-normalized frontier rays and disjoint positive radial hulls |
| [Unfoldings.Geometry.FunctionalHomothety](../Unfoldings/Geometry/FunctionalHomothety.lean) | Positive homotheties preserve support levels and half-spaces |
| [Unfoldings.Geometry.FunctionalPlane](../Unfoldings/Geometry/FunctionalPlane.lean) | Constructed affine Euclidean coordinates on nonzero functional level planes |
| [Unfoldings.Geometry.Halfplane](../Unfoldings/Geometry/Halfplane.lean) | Supporting heights and finite corner bounds |
| [Unfoldings.Geometry.HingeConverse](../Unfoldings/Geometry/HingeConverse.lean) | Recover strict opposite-side opening from joined disjoint interiors |
| [Unfoldings.Geometry.HingePatch](../Unfoldings/Geometry/HingePatch.lean) | Exact hinge intersections and local planar coverage |
| [Unfoldings.Geometry.HingeRigidity](../Unfoldings/Geometry/HingeRigidity.lean) | Two-circle side rigidity and uniqueness of joined outward face motions |
| [Unfoldings.Geometry.Hinge](../Unfoldings/Geometry/Hinge.lean) | Opposite sides imply adjacent-cell nonoverlap |
| [Unfoldings.Geometry.Interior](../Unfoldings/Geometry/Interior.lean) | Interior clearance and Euclidean cell balls |
| [Unfoldings.Geometry.IsometryOnConvex](../Unfoldings/Geometry/IsometryOnConvex.lean) | Isometric maps to strictly convex spaces preserve affine segment parameters |
| [Unfoldings.Geometry.LineCoordinate](../Unfoldings/Geometry/LineCoordinate.lean) | Real affine coordinates and exact segment membership on a genuine line |
| [Unfoldings.Geometry.LocalHingeBoundary](../Unfoldings/Geometry/LocalHingeBoundary.lean) | A locally two-plane convex frontier equals the actual supporting hinge |
| [Unfoldings.Geometry.Paths](../Unfoldings/Geometry/Paths.lean) | Straight paths in triangle cells with exact Euclidean length |
| [Unfoldings.Geometry.Placement](../Unfoldings/Geometry/Placement.lean) | Constructed strict outward hinge placements |
| [Unfoldings.Geometry.PlanarCollinearity](../Unfoldings/Geometry/PlanarCollinearity.lean) | Signed-area zero is equivalent to affine collinearity |
| [Unfoldings.Geometry.PlaneIntersection](../Unfoldings/Geometry/PlaneIntersection.lean) | Distinct spatial planes intersect in their shared nonzero direction line |
| [Unfoldings.Geometry.PlaneSphere](../Unfoldings/Geometry/PlaneSphere.lean) | The planar circle is connected, nontrivial and perfect |
| [Unfoldings.Geometry.PolygonEdges](../Unfoldings/Geometry/PolygonEdges.lean) | Open-edge separation allowing collinear subdivisions; at least three vertices |
| [Unfoldings.Geometry.PolyhedralSelection](../Unfoldings/Geometry/PolyhedralSelection.lean) | Finite polygonal partitions with one compatible affine map on each whole closed piece |
| [Unfoldings.Geometry.PyramidAngles](../Unfoldings/Geometry/PyramidAngles.lean) | Lateral pyramid angle budgets, including strictness for transverse apices |
| [Unfoldings.Geometry.RadialBody](../Unfoldings/Geometry/RadialBody.lean) | Each ray meets the boundary once, and normalization gives a sphere homeomorphism |
| [Unfoldings.Geometry.RadialCone](../Unfoldings/Geometry/RadialCone.lean) | A nonconvex radial body is a closed ball, with exactly matching boundaries |
| [Unfoldings.Geometry.RadialInterior](../Unfoldings/Geometry/RadialInterior.lean) | Interior points extend slightly outward along their radial lines |
| [Unfoldings.Geometry.RadialLocality](../Unfoldings/Geometry/RadialLocality.lean) | Local equality of positive radial cones implies global equality |
| [Unfoldings.Geometry.RadialRetraction](../Unfoldings/Geometry/RadialRetraction.lean) | Continuous radial retraction onto the boundary of a compact strictly radial body |
| [Unfoldings.Geometry.RadialSliceAngles](../Unfoldings/Geometry/RadialSliceAngles.lean) | Positive radial slicing preserves affine apex angles |
| [Unfoldings.Geometry.RadialSlice](../Unfoldings/Geometry/RadialSlice.lean) | Actual compact convex level sections and radial generator projections |
| [Unfoldings.Geometry.RaySection](../Unfoldings/Geometry/RaySection.lean) | Exact wedge sections and preservation of their genuine apex angles |
| [Unfoldings.Geometry.RealAffine](../Unfoldings/Geometry/RealAffine.lean) | Two distinct real samples determine an affine map |
| [Unfoldings.Geometry.SegmentCells](../Unfoldings/Geometry/SegmentCells.lean) | Intersecting unmarked open subsegments have equal closed carriers |
| [Unfoldings.Geometry.SegmentGraph](../Unfoldings/Geometry/SegmentGraph.lean) | Construct a finite embedded straight graph from any finite segment network |
| [Unfoldings.Geometry.SegmentSubdivision](../Unfoldings/Geometry/SegmentSubdivision.lean) | Exact segment coverage by consecutive marked subsegments |
| [Unfoldings.Geometry.SegmentVertices](../Unfoldings/Geometry/SegmentVertices.lean) | Finite marked endpoints of all original segments and their pairwise intersections |
| [Unfoldings.Geometry.Separation](../Unfoldings/Geometry/Separation.lean) | Corner certificates for whole-cell separation |
| [Unfoldings.Geometry.SliceHull](../Unfoldings/Geometry/SliceHull.lean) | The whole transverse section is the finite hull of projected generators |
| [Unfoldings.Geometry.SliceInterior](../Unfoldings/Geometry/SliceInterior.lean) | Transverse sections meet the ambient interior of the convex body |
| [Unfoldings.Geometry.SpatialHinge](../Unfoldings/Geometry/SpatialHinge.lean) | Injective piecewise rigid parametrizations of entire support hinges |
| [Unfoldings.Geometry.SpatialPlane](../Unfoldings/Geometry/SpatialPlane.lean) | A rigid spatial plane equals its containing nonzero functional level |
| [Unfoldings.Geometry.StraightGraph](../Unfoldings/Geometry/StraightGraph.lean) | Affine edge formulas imply an embedded graph has no loops or parallel edges |
| [Unfoldings.Geometry.StrictHingeSupport](../Unfoldings/Geometry/StrictHingeSupport.lean) | Distinct support planes strictly separate their opposite corners |
| [Unfoldings.Geometry.SupportingChord](../Unfoldings/Geometry/SupportingChord.lean) | Support levels extend from an interior chord point to both endpoints |
| [Unfoldings.Geometry.TransversePyramid](../Unfoldings/Geometry/TransversePyramid.lean) | Strict transverse pyramid budget without an extra corner assumption |
| [Unfoldings.Geometry.TriangleBoundary](../Unfoldings/Geometry/TriangleBoundary.lean) | Every noninterior closed triangle point lies on an actual edge |
| [Unfoldings.Geometry.TriangleMotion](../Unfoldings/Geometry/TriangleMotion.lean) | Rigidly move triangles, edges, and barycentric coordinates |
| [Unfoldings.Geometry.TriangleSplitSides](../Unfoldings/Geometry/TriangleSplitSides.lean) | Exact common edge and disjoint interiors of the two split children |
| [Unfoldings.Geometry.TriangleSplit](../Unfoldings/Geometry/TriangleSplit.lean) | Construct nondegenerate edge splits and prove their exact cover |
| [Unfoldings.Geometry.Triangle](../Unfoldings/Geometry/Triangle.lean) | Nondegenerate cells and full edge subspaces |
| [Unfoldings.Geometry.UnitLine](../Unfoldings/Geometry/UnitLine.lean) | A nonzero real line has two opposite unit directions |

## Topology and combinatorics

| Module | Purpose |
| --- | --- |
| [Unfoldings.Topology.ChildSubtrees](../Unfoldings/Topology/ChildSubtrees.lean) | Immediate-child subtrees partition all proper descendants with arbitrary additive weights |
| [Unfoldings.Topology.OrderedChanges](../Unfoldings/Topology/OrderedChanges.lean) | An ordered tail or head of bounded signal changes telescopes, ignoring zero increments |
| [Unfoldings.Topology.ParentOrbitEnumeration](../Unfoldings/Topology/ParentOrbitEnumeration.lean) | The first-root orbit enumerates every original nonroot ancestor exactly once |
| [Unfoldings.Topology.SubtreeWeights](../Unfoldings/Topology/SubtreeWeights.lean) | Regroup nested subtree weights over root paths before applying signed-cancellation bounds |
| [Unfoldings.Topology.CyclicRegion](../Unfoldings/Topology/CyclicRegion.lean) | Conservation of membership orients exactly two exits of a finite permutation region |
| [Unfoldings.Topology.SelectedSubtree](../Unfoldings/Topology/SelectedSubtree.lean) | Descendants have one selected original-edge exit and exact endpoint incidence count |
| [Unfoldings.Topology.SelectedLeaves](../Unfoldings/Topology/SelectedLeaves.lean) | Minimum-potential nonroot leaves and their unique selected incident original edge |
| [Unfoldings.Topology.ParentPaths](../Unfoldings/Topology/ParentPaths.lean) | Finite parent orbits stop at the first root and have strictly increasing potentials |
| [Unfoldings.Topology.AscendingForest](../Unfoldings/Topology/AscendingForest.lean) | Strictly increasing parent choices construct an acyclic graph with unique component roots |
| [Unfoldings.Topology.SelectedForest](../Unfoldings/Topology/SelectedForest.lean) | Selected original edges keep their names and form an actual rooted forest |
| [Unfoldings.Topology.ProgressForest](../Unfoldings/Topology/ProgressForest.lean) | Construct original-edge forest selections from local labeled progress |
| [Unfoldings.Combinatorics.FiniteReach](../Unfoldings/Combinatorics/FiniteReach.lean) | Bounded rounds of finite choices give a finite set of reachable states |
| [Unfoldings.Topology.BallBoundaryQuotient](../Unfoldings/Topology/BallBoundaryQuotient.lean) | Disk quotients have open-disk complements; spherical targets force boundary graphs to be trees |
| [Unfoldings.Topology.BallExtension](../Unfoldings/Topology/BallExtension.lean) | Radius-preserving closed-ball extensions of arbitrary sphere homeomorphisms |
| [Unfoldings.Topology.BoundaryAtlas](../Unfoldings/Topology/BoundaryAtlas.lean) | Compact boundary atlases yield inward embeddings and separate boundary-quotient fibers |
| [Unfoldings.Topology.BoundaryCollapse](../Unfoldings/Topology/BoundaryCollapse.lean) | Collapse a closed boundary to infinity in its complement, with continuity, surjectivity, and exact fibers |
| [Unfoldings.Topology.BoundaryInvariance](../Unfoldings/Topology/BoundaryInvariance.lean) | Actual half-plane atlases identify the frontier of any planar embedding |
| [Unfoldings.Topology.BoundaryPush](../Unfoldings/Topology/BoundaryPush.lean) | Finite compositions of local pushes move a compact boundary into its complement |
| [Unfoldings.Topology.BoundaryQuotientTransport](../Unfoldings/Topology/BoundaryQuotientTransport.lean) | Postcompose boundary quotients and compose them when the new collapsed locus is absorbed |
| [Unfoldings.Topology.BoundaryQuotient](../Unfoldings/Topology/BoundaryQuotient.lean) | Boundary-only quotient maps, complement homeomorphisms, and descended boundary retractions |
| [Unfoldings.Topology.ChainPairings](../Unfoldings/Topology/ChainPairings.lean) | Every link pairing is consecutive or closes the outer banks |
| [Unfoldings.Topology.CircleObstruction](../Unfoldings/Topology/CircleObstruction.lean) | Covering-space proof that a circle is not contractible and a disk cannot retract onto it |
| [Unfoldings.Topology.CommonFibers](../Unfoldings/Topology/CommonFibers.lean) | Compact quotient maps with the same fibers identify their targets |
| [Unfoldings.Topology.CompactJordanDisk](../Unfoldings/Topology/CompactJordanDisk.lean) | Compact planar sets with nonempty interior and Jordan frontier are disks |
| [Unfoldings.Topology.ContractibleLift](../Unfoldings/Topology/ContractibleLift.lean) | Covering-space lifts from contractible domains, without local path-connectedness assumptions |
| [Unfoldings.Topology.ConvexBoundary](../Unfoldings/Topology/ConvexBoundary.lean) | Sphere topology and connectedness of bounded convex boundaries |
| [Unfoldings.Topology.CyclicLabels](../Unfoldings/Topology/CyclicLabels.lean) | Nonconstant cyclic lists have no more labels than changes |
| [Unfoldings.Topology.DiskDegree](../Unfoldings/Topology/DiskDegree.lean) | Boundary-fixing injective disk maps cover exactly the open disk on their interiors |
| [Unfoldings.Topology.DiskFromBoundary](../Unfoldings/Topology/DiskFromBoundary.lean) | Construct disk topology from a boundary atlas and one actual Jordan boundary |
| [Unfoldings.Topology.DiskSphereQuotient](../Unfoldings/Topology/DiskSphereQuotient.lean) | Construct the sphere quotient of a closed disk by collapsing its exact boundary circle |
| [Unfoldings.Topology.DiskSubsetChart](../Unfoldings/Topology/DiskSubsetChart.lean) | Open Euclidean embeddings for complements of closed sets containing the original disk boundary |
| [Unfoldings.Topology.FiberGraph](../Unfoldings/Topology/FiberGraph.lean) | Equivalence chains in finite fibers yield short simple graph paths |
| [Unfoldings.Topology.FiniteClasses](../Unfoldings/Topology/FiniteClasses.lean) | Finite equivalence classes from finitely many branching points |
| [Unfoldings.Topology.FiniteEmbeddedGraph](../Unfoldings/Topology/FiniteEmbeddedGraph.lean) | Finite embedded multigraphs, compact carriers, and topological-to-graph connectedness |
| [Unfoldings.Topology.FiniteIntervalCover](../Unfoldings/Topology/FiniteIntervalCover.lean) | Bounded subdivisions subordinate to finite closed interval covers |
| [Unfoldings.Topology.FiniteSubdivision](../Unfoldings/Topology/FiniteSubdivision.lean) | Existence and uniqueness of consecutive marked real intervals |
| [Unfoldings.Topology.GraphAcyclic](../Unfoldings/Topology/GraphAcyclic.lean) | Contractible finite embedded graphs are simple and their adjacency graphs are trees |
| [Unfoldings.Topology.GraphDrawing](../Unfoldings/Topology/GraphDrawing.lean) | Bridge actual embedded graphs to the pinned plane-drawing and Jordan-cycle APIs |
| [Unfoldings.Topology.GraphEmbedding](../Unfoldings/Topology/GraphEmbedding.lean) | Transport actual embedded graphs through continuous injective maps |
| [Unfoldings.Topology.GraphExtension](../Unfoldings/Topology/GraphExtension.lean) | Continuous extension of compatible vertex and edge maps to the actual graph carrier |
| [Unfoldings.Topology.GraphFinitePath](../Unfoldings/Topology/GraphFinitePath.lean) | Construct multigraph paths and cycles from finite injective sequences |
| [Unfoldings.Topology.GraphForestMap](../Unfoldings/Topology/GraphForestMap.lean) | A cycle mapped to a forest repeats the image of each distinguished edge |
| [Unfoldings.Topology.GraphPoints](../Unfoldings/Topology/GraphPoints.lean) | Vertex points and continuous edge inclusions into the embedded graph carrier |
| [Unfoldings.Topology.GraphPotential](../Unfoldings/Topology/GraphPotential.lean) | Selected-edge circle winding maps and real vertex potentials from contractibility |
| [Unfoldings.Topology.GraphReachability](../Unfoldings/Topology/GraphReachability.lean) | Multigraph walk reachability, invariant labels, and propagation through links |
| [Unfoldings.Topology.GraphRootExtension](../Unfoldings/Topology/GraphRootExtension.lean) | Multigraph rooted forest iff outside extension tree; all loops and parallel edges remain named |
| [Unfoldings.Topology.GraphRootQuotient](../Unfoldings/Topology/GraphRootQuotient.lean) | A tree quotient identifying exactly the marked roots forces a rooted forest |
| [Unfoldings.Topology.GraphVertexMap](../Unfoldings/Topology/GraphVertexMap.lean) | Injective vertex relabeling preserves multigraph walks, paths, and cycles |
| [Unfoldings.Topology.HalfPlanePush](../Unfoldings/Topology/HalfPlanePush.lean) | Explicit injective inward pushes with compact rectangular support |
| [Unfoldings.Topology.LocalPush](../Unfoldings/Topology/LocalPush.lean) | Extend local injective chart maps and boundary pushes by the identity |
| [Unfoldings.Topology.PairedInvolutions](../Unfoldings/Topology/PairedInvolutions.lean) | Generic finite interval/cycle order from two involutions |
| [Unfoldings.Topology.PerfectProjection](../Unfoldings/Topology/PerfectProjection.lean) | A perfect boundary cannot project injectively to finite exceptions outside a closed set |
| [Unfoldings.Topology.PlanarHalfPlane](../Unfoldings/Topology/PlanarHalfPlane.lean) | Planar openness in product coordinates and the half-plane boundary obstruction |
| [Unfoldings.Topology.PlanarOpenMapping](../Unfoldings/Topology/PlanarOpenMapping.lean) | Planar invariance of domain from the pinned Jordan–Schönflies theorem and circle obstruction |
| [Unfoldings.Topology.PuncturedSphere](../Unfoldings/Topology/PuncturedSphere.lean) | Contractibility of a unit sphere punctured at any specified point |
| [Unfoldings.Topology.Quadrant](../Unfoldings/Topology/Quadrant.lean) | Explicit piecewise linear quadrant-to-half-plane homeomorphism |
| [Unfoldings.Topology.QuotientRetraction](../Unfoldings/Topology/QuotientRetraction.lean) | Continuous quotient descent and contractibility of retracts |
| [Unfoldings.Topology.RootedForest](../Unfoldings/Topology/RootedForest.lean) | Outside-vertex tree equivalence for forests with exactly one root per connected component |
| [Unfoldings.Topology.SmallHalfPlanePush](../Unfoldings/Topology/SmallHalfPlanePush.lean) | Construct inward pushes in arbitrarily small half-plane neighborhoods |
| [Unfoldings.Topology.SphereChart](../Unfoldings/Topology/SphereChart.lean) | Explicit Euclidean homeomorphisms for punctured unit spheres |
| [Unfoldings.Topology.SphereSubsetChart](../Unfoldings/Topology/SphereSubsetChart.lean) | Closed-set complements in spheres have open Euclidean embeddings |
## Examples and core imports

[Examples.Chains](../Unfoldings/Examples/Chains.lean) checks a monotone staircase
and a counterexample to testing radial monotonicity only at endpoints.

| Module | Purpose |
| --- | --- |
| [Audit](../Audit.lean) | Transitive axiom check for all imported library declarations |
| [Unfoldings](../Unfoldings.lean) | Public umbrella import for the library |
| [Unfoldings.Basic](../Unfoldings/Basic.lean) | Common Euclidean plane and spatial coordinate types |
| [Unfoldings.Examples.BoundaryFans](../Unfoldings/Examples/BoundaryFans.lean) | A fan with overlapping developed interiors still has half-plane topology |
| [Unfoldings.Examples.CutForests](../Unfoldings/Examples/CutForests.lean) | Empty forest, one rooted edge, and counterexamples with missing or multiple roots |
| [Unfoldings.Examples.Hinge](../Unfoldings/Examples/Hinge.lean) | Joined hinges, boundary contact, and a layout with interior overlap |
| [Unfoldings.Examples.Metric](../Unfoldings/Examples/Metric.lean) | Metric recovery, disconnectedness, and shortcuts |
| [Unfoldings.Examples.Subdivision](../Unfoldings/Examples/Subdivision.lean) | Canonical cell isometry and outward nonoverlapping development for every elementary split |
| [Unfoldings.Examples.Tetrahedron.Body](../Unfoldings/Examples/Tetrahedron/Body.lean) | The actual tetrahedral convex hull, its supporting coordinates and four exact facets |
| [Unfoldings.Examples.Tetrahedron.Boundary](../Unfoldings/Examples/Tetrahedron/Boundary.lean) | Prove spatial injectivity and certify a full-dimensional convex boundary |
| [Unfoldings.Examples.Tetrahedron.Complex](../Unfoldings/Examples/Tetrahedron/Complex.lean) | Six checked paired edges and compatible rigid spatial face maps |
| [Unfoldings.Examples.Tetrahedron.Coordinates](../Unfoldings/Examples/Tetrahedron/Coordinates.lean) | Four rigid planar face placements of an explicit coordinate tetrahedron |
| [Unfoldings.Examples.Tetrahedron.Cuts](../Unfoldings/Examples/Tetrahedron/Cuts.lean) | A specific three-spoke cut tree gives a disk; no cuts and all edges cut fail |
| [Unfoldings.Examples.Tetrahedron.Faces](../Unfoldings/Examples/Tetrahedron/Faces.lean) | Relate spatial supporting coordinates to intrinsic face barycentric coordinates |
| [Unfoldings.Examples.Tetrahedron.Source](../Unfoldings/Examples/Tetrahedron/Source.lean) | Instantiate the complete source unfolding at an actual crease midpoint |
| [Unfoldings.Examples.Tetrahedron.Vertices](../Unfoldings/Examples/Tetrahedron/Vertices.lean) | Identify the actual metric vertex quotient with the four declared tetrahedron vertices |
| [Unfoldings.Examples.Tetrahedron](../Unfoldings/Examples/Tetrahedron.lean) | Complete concrete convex tetrahedron, source unfolding, and valid and invalid cut patterns |
| [Unfoldings.Cap.RefinedClipTriangles](../Unfoldings/Cap/RefinedClipTriangles.lean) | Common boundary refinement preserves actual clip coverage, supporting planes, and normals |
| [Unfoldings.Cap.ClipPairings](../Unfoldings/Cap/ClipPairings.lean) | Actual spatial isometric whole-edge pairings and a folding onto the clipped roof |
| [Unfoldings.Complex.GeometricPairings](../Unfoldings/Complex/GeometricPairings.lean) | Canonical complete whole-edge seams, unique partners, and the identity planar development |
| [Unfoldings.Geometry.ClosedTriangleRadial](../Unfoldings/Geometry/ClosedTriangleRadial.lean) | Closed triangle radial coordinates with the apex treated separately |
| [Unfoldings.Geometry.CommonBoundarySubdivision](../Unfoldings/Geometry/CommonBoundarySubdivision.lean) | One embedded straight graph subdivides every boundary of a finite triangle family |
| [Unfoldings.Geometry.CommonTriangleRefinement](../Unfoldings/Geometry/CommonTriangleRefinement.lean) | Exact disjoint-interior center-fan refinement with global shared base labels |
| [Unfoldings.Geometry.ConformingTriangles](../Unfoldings/Geometry/ConformingTriangles.lean) | Face-to-face conformity and exact empty, common-vertex, or shared-edge intersections |
| [Unfoldings.Geometry.RefinedConformity](../Unfoldings/Geometry/RefinedConformity.lean) | The common boundary refinement eliminates all partial-edge triangle contacts |
| [Unfoldings.Geometry.RefinedFanIntersections](../Unfoldings/Geometry/RefinedFanIntersections.lean) | Triangles in one refined fan meet along shared radial edges or their center |
| [Unfoldings.Geometry.RefinedParentIntersections](../Unfoldings/Geometry/RefinedParentIntersections.lean) | Different parent fans meet only on globally shared bases or their endpoints |
| [Unfoldings.Geometry.SharedEdgeMultiplicity](../Unfoldings/Geometry/SharedEdgeMultiplicity.lean) | At most two triangles with disjoint interiors can share one whole geometric edge |
| [Unfoldings.Geometry.SubdividedBoundaryFan](../Unfoldings/Geometry/SubdividedBoundaryFan.lean) | Exact center-fan partitions using prescribed global boundary edges |
| [Unfoldings.Geometry.TriangleFanBoundary](../Unfoldings/Geometry/TriangleFanBoundary.lean) | Straight frontier segments lie in one old edge and fan contacts lie on their bases |
| [Unfoldings.Geometry.TriangleFrontier](../Unfoldings/Geometry/TriangleFrontier.lean) | The actual frontier of a triangle is the union of its three whole edges |
| [Unfoldings.Topology.EmbeddedEdgeIntersections](../Unfoldings/Topology/EmbeddedEdgeIntersections.lean) | Distinct embedded graph edges intersect only at their common named endpoints |

| [Unfoldings.Cap.ClipEmbedding](../Unfoldings/Cap/ClipEmbedding.lean) | Whole-edge compatibility propagates through every vertex and proves actual roof embedding |
| [Unfoldings.Cap.ClipRealization](../Unfoldings/Cap/ClipRealization.lean) | The intrinsic glued physical roof clip is homeomorphic to the actual spatial disk |
| [Unfoldings.Cap.ClipMetric](../Unfoldings/Cap/ClipMetric.lean) | Finite actual route distances and uniform intrinsic projection bounds for roof clips |
| [Unfoldings.Geometry.ConformingStar](../Unfoldings/Geometry/ConformingStar.lean) | Edge-compatible labels agree around every vertex of a conforming convex triangle partition |
| [Unfoldings.Geometry.PuncturedConvex](../Unfoldings/Geometry/PuncturedConvex.lean) | Full-dimensional convex planar regions remain path connected after removing one point |
| [Unfoldings.Geometry.TriangleNeighborhood](../Unfoldings/Geometry/TriangleNeighborhood.lean) | Interior points distinct from the center occur arbitrarily close to every triangle point |
| [Unfoldings.Topology.ClosedCoverValues](../Unfoldings/Topology/ClosedCoverValues.lean) | Compatible constant labels on finite closed covers of preconnected spaces agree |

| [Unfoldings.Cap.ClipEdgeLift](../Unfoldings/Cap/ClipEdgeLift.lean) | Every original spatial edge and cut is exactly a union of whole actual roof triangle edges |
| [Unfoldings.Cap.ConstrainedClipTriangles](../Unfoldings/Cap/ConstrainedClipTriangles.lean) | Conforming physical clip triangulations respect prescribed lines and preserve all original edges |
| [Unfoldings.Geometry.ChamberTriangulation](../Unfoldings/Geometry/ChamberTriangulation.lean) | Exact finite disjoint-interior triangle partitions aligned to all prescribed affine lines |
| [Unfoldings.Geometry.ConstrainedEdgeSubdivision](../Unfoldings/Geometry/ConstrainedEdgeSubdivision.lean) | Supporting-line sign constraints force full subedges at regular old-edge contacts |
| [Unfoldings.Geometry.ConstrainedTriangleRefinement](../Unfoldings/Geometry/ConstrainedTriangleRefinement.lean) | Finite line-constrained triangle refinements subordinate to actual old parents |
| [Unfoldings.Geometry.TriangleSupportingFace](../Unfoldings/Geometry/TriangleSupportingFace.lean) | Contacts with proper affine supporting lines occur on actual whole edges or vertices |
| [Unfoldings.Geometry.WholeEdgeSubdivision](../Unfoldings/Geometry/WholeEdgeSubdivision.lean) | Exact coverage of old edges by finite whole fine edges with no exceptional gaps |

| [Unfoldings.Cap.PrescribedClipSegments](../Unfoldings/Cap/PrescribedClipSegments.lean) | Exact whole-edge meshing of arbitrary prescribed segments and all original cap edges |
| [Unfoldings.Cap.SkirtRadialCuts](../Unfoldings/Cap/SkirtRadialCuts.lean) | Disjoint outward skirt components cover supplied seeds and mesh into actual physical roof edges |
| [Unfoldings.Geometry.ClippedRadialTails](../Unfoldings/Geometry/ClippedRadialTails.lean) | Outward radial continuations to a convex rim are disjoint or nested and avoid an inner region |
| [Unfoldings.Geometry.RadialTailFamily](../Unfoldings/Geometry/RadialTailFamily.lean) | Finite radial tails reduce to disjoint rim-labeled whole segment components with exact coverage |
| [Unfoldings.Geometry.TriangleWithEdge](../Unfoldings/Geometry/TriangleWithEdge.lean) | Auxiliary genuine triangles containing any supplied nondegenerate segment as a whole edge |

| [Unfoldings.Cap.ClipIntrinsicBoundary](../Unfoldings/Cap/ClipIntrinsicBoundary.lean) | Actual intrinsic boundary banks are precisely the horizontal outer rim of the conforming clip |
| [Unfoldings.Cap.ClippedCap](../Unfoldings/Cap/ClippedCap.lean) | Translate the constructed clip into a full geometric convex cap with original supporting normals |
| [Unfoldings.Cap.ClipCurvature](../Unfoldings/Cap/ClipCurvature.lean) | One numerical threshold controls every clip and refinement including all new intrinsic vertices |
| [Unfoldings.Cap.DegenerateNormalCurvature](../Unfoldings/Cap/DegenerateNormalCurvature.lean) | Collinear incident normal slopes and two-plane crease subdivisions have zero intrinsic curvature |
| [Unfoldings.Geometry.CollinearNull](../Unfoldings/Geometry/CollinearNull.lean) | Collinear planar convex hulls have zero actual Lebesgue area |

| [Unfoldings.Cap.ClippedCapCoordinates](../Unfoldings/Cap/ClippedCapCoordinates.lean) | Normalized clip projections and normal slopes retain their exact original coordinate formulas |
| [Unfoldings.Cap.ConstrainedClipParents](../Unfoldings/Cap/ConstrainedClipParents.lean) | Actual whole-face parent containment and support labels survive line meshing |
| [Unfoldings.Cap.LineRefinementCurvature](../Unfoldings/Cap/LineRefinementCurvature.lean) | Actual line meshing creates no positive curvature away from preceding roof corners |
| [Unfoldings.Cap.RefinementCurvatureSupport](../Unfoldings/Cap/RefinementCurvatureSupport.lean) | Subordinate support refinements concentrate positive curvature on old corners |
| [Unfoldings.Geometry.ConformingPointMultiplicity](../Unfoldings/Geometry/ConformingPointMultiplicity.lean) | A regular point of a conforming planar triangle partition belongs to at most two faces |

| [Unfoldings.Cap.ProjectedConformity](../Unfoldings/Cap/ProjectedConformity.lean) | The supplied cap triangles are geometrically conforming by injective projection and actual seam classes |
| [Unfoldings.Cap.RoofInteriorHeight](../Unfoldings/Cap/RoofInteriorHeight.lean) | Every interior source has positive roof height in the nonflat case |

## Build and proof audit

Lean and Mathlib are pinned to **4.35.0** in
[lean-toolchain](../lean-toolchain) and [lakefile.toml](../lakefile.toml).
With elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

The default build checks the library, its examples, and [Audit](../Audit.lean).
The audit follows transitive proof dependencies and permits only
`propext`, `Classical.choice`, and `Quot.sound`.
It rejects unfinished proofs and native-decision axioms. Imported modules of
the pinned Jordan–Schönflies library are audited in full as well, with separate
counts for unfolding and planar-topology declarations.

### Cache options

If disk space is limited, fetch selected Mathlib modules and their import
closures instead of the full cache. For example:

```sh
lake exe cache get Mathlib.Geometry.Euclidean.PerpBisector Mathlib.Topology.Baire.Lemmas
```

This example fetches only those closures, not every dependency of this library.
Add the Mathlib modules needed by the files you are building.

To skip Mathlib's automatic full-cache hook during a dependency update:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

Then fetch the required cache and build. Update the pinned versions only as
part of an intentional toolchain upgrade.

## Provenance

The earlier scaffold is preserved in Git history. Its classification target and
assumed global gluing metric were replaced by the constructed route metric.
The design also uses ideas from
[slef/EdgeUnfoldings](https://github.com/slef/EdgeUnfoldings/tree/56caca8cdc44dbc2f839e93808088d56ea3f0780/lean_statement),
particularly whole-face separation certificates and transitive axiom auditing.
No six-vertex classification theorem is a dependency of this library.
The generic path-length extension and concatenation proofs adapt its variation
arguments in `ArcLength`, `SurfacePathJoining`, and `SurfacePathReversal`.
The generic interval center-bound proof adapts `Geometry/IntervalCenterBound`;
the finite closed-cover theorem extends that approach to actual piece domains.

The planar openness and intrinsic boundary proofs use Álvaro Begué's
[Jordan–Schönflies formalization](https://github.com/alonamaloh/schoenflies-lean)
at revision `05a43d29cde026618777db3d4e4316204ccca237`, under Apache 2.0.
The [vendored source record](../vendor/schoenflies/UPSTREAM.md) documents the
Lean 4.35 module-system and proof-script compatibility changes; theorem
statements are unchanged. The separate [license](../vendor/schoenflies/LICENSE)
is retained. Comparator challenge files and upstream build caches are excluded.
