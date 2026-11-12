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
| [Unfoldings.Cap.GeometricComponentNetwork](../Unfoldings/Cap/GeometricComponentNetwork.lean) | Whole original and radial cut pieces belong to their actual component sector network |
| [Unfoldings.Cap.GeometricChainNetwork](../Unfoldings/Cap/GeometricChainNetwork.lean) | Physical fine cut chains inherit network coverage and strictly positive sector coordinates |
| [Unfoldings.Cap.GeometricFineTailTracking](../Unfoldings/Cap/GeometricFineTailTracking.lean) | Actual geometric tail points lie on whole edges of every compatible outward fine cut chain |
| [Unfoldings.Cap.CompletedGeometricTailTracking](../Unfoldings/Cap/CompletedGeometricTailTracking.lean) | Actual completed cut paths supply support, genuine outward edges, and a far endpoint for tail tracking |
| [Unfoldings.Cap.GeometricVertexCutPiece](../Unfoldings/Cap/GeometricVertexCutPiece.lean) | Every nonterminal geometric cut vertex has an actual containing piece with its own component label |
| [Unfoldings.Cap.LeafCompletedTailTracking](../Unfoldings/Cap/LeafCompletedTailTracking.lean) | Constructed leaf tails track the actual completed forest without a path-matching certificate |
| [Unfoldings.Cap.GeometricSeparatorPrefix](../Unfoldings/Cap/GeometricSeparatorPrefix.lean) | Actual shared separator prefixes are cut-free or coherent, including exterior-ray contacts |
| [Unfoldings.Cap.SharedSeparatorCirclePrefix](../Unfoldings/Cap/SharedSeparatorCirclePrefix.lean) | Actual neighboring circle endpoints coincide before their shared leaf or both lie beyond it |
| [Unfoldings.Cap.SharedSeparatorCircleSeparation](../Unfoldings/Cap/SharedSeparatorCircleSeparation.lean) | Actual adjacent strip-circle images are disjoint across the coherent prefix and common leaf tail |
| [Unfoldings.Cap.ExtendedAdjacentCircleSeparation](../Unfoldings/Cap/ExtendedAdjacentCircleSeparation.lean) | One tilt before both meshes constructs a single trace family with disjoint neighboring source-circle slices |
| [Unfoldings.Cap.EmptyCircleTerminalPinch](../Unfoldings/Cap/EmptyCircleTerminalPinch.lean) | An absent controlled circle supplies a permanent terminal pinch with an actual visible trace inside |
| [Unfoldings.Cap.EmptyCircleStripBounds](../Unfoldings/Cap/EmptyCircleStripBounds.lean) | An empty nonexceptional circle slice places the entire approached strip closure strictly inside the circle |
| [Unfoldings.Cap.GeometricTailVertices](../Unfoldings/Cap/GeometricTailVertices.lean) | A geometric vertex reached by an actual tail is an ancestor in the same cut component |
| [Unfoldings.Cap.GeometricFreshWaterfallLeaf](../Unfoldings/Cap/GeometricFreshWaterfallLeaf.lean) | Fresh actual leaves enter positive-width cells, including tied insertion heights and source insertions |
| [Unfoldings.Cap.WaterfallCircleExceptions](../Unfoldings/Cap/WaterfallCircleExceptions.lean) | One finite radius set covers all vertex-copy and disappearing-strip exceptions |
| [Unfoldings.Cap.WaterfallCircleNonoverlap](../Unfoldings/Cap/WaterfallCircleNonoverlap.lean) | Global strip-circle separation implies separation of actual developed face interiors |
| [Unfoldings.Cap.RadialStripPhysicalMap](../Unfoldings/Cap/RadialStripPhysicalMap.lean) | Actual strip maps and source-circle slices in one common developed plane |
| [Unfoldings.Cap.ProjectedDenseSeparation](../Unfoldings/Cap/ProjectedDenseSeparation.lean) | Regular projected-map injectivity separates actual developed face interiors |
| [Unfoldings.Cap.SectorWaterfallRegular](../Unfoldings/Cap/SectorWaterfallRegular.lean) | Avoiding all physical waterfall walls is open and dense and supplies an actual open strip |
| [Unfoldings.Cap.ExtendedEmptyCircleContinuations](../Unfoldings/Cap/ExtendedEmptyCircleContinuations.lean) | Construct actual disappearing-strip continuations from the roof geometry in the same calibration |
| [Unfoldings.Cap.EmptyCircleContinuation](../Unfoldings/Cap/EmptyCircleContinuation.lean) | A disappearing strip retains its actual terminal copy and ordered proper comparison arcs |
| [Unfoldings.Cap.ExtendedCalibratedComparisonArcs](../Unfoldings/Cap/ExtendedCalibratedComparisonArcs.lean) | Actual roof-face bounds construct proper comparison arcs in a specified bank calibration |
| [Unfoldings.Cap.ExtendedAdjacentCircleGeometry](../Unfoldings/Cap/ExtendedAdjacentCircleGeometry.lean) | One uniform calibration gives neighboring circle separation and actual disappearing-strip continuations |
| [Unfoldings.Cap.RadialWaterfallBankControl](../Unfoldings/Cap/RadialWaterfallBankControl.lean) | The actual radial trace family supplies all-face error estimates in the same calibration |
| [Unfoldings.Cap.EmptyCircleTerminalCopy](../Unfoldings/Cap/EmptyCircleTerminalCopy.lean) | A disappearing actual strip supplies its own cut-vertex contour copy inside the source circle |
| [Unfoldings.Cap.GeometricTailAffine](../Unfoldings/Cap/GeometricTailAffine.lean) | Actual tail graphs and exterior rays are locally affine away from geometric vertices |
| [Unfoldings.Cap.GeometricChainSectors](../Unfoldings/Cap/GeometricChainSectors.lean) | Actual completed parent edges and curved descendants retain their specified geometric leaf sector |
| [Unfoldings.Cap.CompletedChartComparisonPoints](../Unfoldings/Cap/CompletedChartComparisonPoints.lean) | Centered parent-bank chart values equal the corresponding complete comparison-chain points |
| [Unfoldings.Cap.RadialStripCircleComparison](../Unfoldings/Cap/RadialStripCircleComparison.lean) | Actual regular strip-circle endpoints are points of the named entrance and exit comparison banks |
| [Unfoldings.Cap.ParentPathCircleBankOrder](../Unfoldings/Cap/ParentPathCircleBankOrder.lean) | Derive facing endpoint order and disjoint circle slices on one actual outward parent path |
| [Unfoldings.Cap.CircleStripSeparation](../Unfoldings/Cap/CircleStripSeparation.lean) | Weak gap order separates open strip-circle intervals while allowing boundary contact |
| [Unfoldings.Cap.RegularCircleRadius](../Unfoldings/Cap/RegularCircleRadius.lean) | One finite set excludes vertex values of every actual closed strip trace in all sectors |
| [Unfoldings.Cap.LeafTailCircleSeparation](../Unfoldings/Cap/LeafTailCircleSeparation.lean) | Actual facing strip-circle slices are disjoint after their common constructed leaf, off finitely many radii |
| [Unfoldings.Cap.ExtendedWaterfallProvenance](../Unfoldings/Cap/ExtendedWaterfallProvenance.lean) | Retain actual leaf/separator provenance and strict walls with coherent cut-avoiding waterfall domains |
| [Unfoldings.Cap.ExtendedRadialWaterfallData](../Unfoldings/Cap/ExtendedRadialWaterfallData.lean) | One uniform calibration retains leaf provenance and the complete radial developed data for the same subdivision |
| [Unfoldings.Cap.ExtendedLeafTailTracking](../Unfoldings/Cap/ExtendedLeafTailTracking.lean) | Every constructed roof leaf tail has an actual fine parent-path point at every controlled height |
| [Unfoldings.Cap.SharedBankCirclePrefix](../Unfoldings/Cap/SharedBankCirclePrefix.lean) | Adjacent equal-radius bank endpoints coincide on a coherent prefix or both lie beyond it |
| [Unfoldings.Cap.RadialStripCircleWidth](../Unfoldings/Cap/RadialStripCircleWidth.lean) | Nonempty controlled circle slices have positive-width bank points strictly between source and cutoff |
| [Unfoldings.Cap.MatchedBankAtHeight](../Unfoldings/Cap/MatchedBankAtHeight.lean) | Positive physical width supplies active-height witnesses for actual named parent-bank matching |
| [Unfoldings.Cap.RadialStripCircleMatching](../Unfoldings/Cap/RadialStripCircleMatching.lean) | Regular actual circle endpoints select their named entrance and exit parent-bank charts |
| [Unfoldings.Cap.RadialStripPointOrder](../Unfoldings/Cap/RadialStripPointOrder.lean) | Closed actual strip points preserve strict radial progress and signed mixed-coordinate order |
| [Unfoldings.Cap.RadialStripBankOrder](../Unfoldings/Cap/RadialStripBankOrder.lean) | Actual lower and upper banks have strict source-circle order, including pinches |
| [Unfoldings.Cap.ExtendedOrientedStripCircleIntervals](../Unfoldings/Cap/ExtendedOrientedStripCircleIntervals.lean) | Uniform actual strips have oriented bank-bounded source-circle intervals before either mesh |
| [Unfoldings.Cap.StripCircleBanks](../Unfoldings/Cap/StripCircleBanks.lean) | Nonempty strip-circle intervals have distinct endpoints at actual approached heights on both banks |
| [Unfoldings.Cap.RadialStripTraceVisibility](../Unfoldings/Cap/RadialStripTraceVisibility.lean) | Every point of the actual closed trace retains a face approached from this strip, including terminal pinches |
| [Unfoldings.Cap.RadialStripCircleBanks](../Unfoldings/Cap/RadialStripCircleBanks.lean) | Construct actual bank heights and distinct endpoint values for every nonempty controlled circle slice |
| [Unfoldings.Cap.RadialStripTraceData](../Unfoldings/Cap/RadialStripTraceData.lean) | The same constructed radial trace retains source normalization, coherent pinches, and visible bank values |
| [Unfoldings.Cap.RadialStripTraceBounds](../Unfoldings/Cap/RadialStripTraceBounds.lean) | Actual trace data give closed source-distance bounds, source values, and strict quadrant margins |
| [Unfoldings.Cap.ExtendedRadialStripData](../Unfoldings/Cap/ExtendedRadialStripData.lean) | Uniform actual strip data retain closed injectivity, radial matching, and coherent source geometry together |
| [Unfoldings.Cap.RadialStripCircleInterval](../Unfoldings/Cap/RadialStripCircleInterval.lean) | Actual strip data discharge every source-circle interval hypothesis, including collapsed terminal tails |
| [Unfoldings.Cap.ExtendedStripCircleIntervals](../Unfoldings/Cap/ExtendedStripCircleIntervals.lean) | Every constructed waterfall strip has at most one bank-bounded source-circle interval at a uniform tilt |
| [Unfoldings.Cap.StripCircleInterval](../Unfoldings/Cap/StripCircleInterval.lean) | Developed strip-circle intersections are empty or one interval with actual bank endpoints |
| [Unfoldings.Cap.ClosedRadialBankTrace](../Unfoldings/Cap/ClosedRadialBankTrace.lean) | Strict radial bank progress and circle uniqueness include approached terminal pinches |
| [Unfoldings.Cap.ExtendedClosedRadialBankTraces](../Unfoldings/Cap/ExtendedClosedRadialBankTraces.lean) | One uniform calibration gives full closed-trace injectivity and radial matched banks |
| [Unfoldings.Cap.RadialBankTraceProperty](../Unfoldings/Cap/RadialBankTraceProperty.lean) | Strict radial progress of each visible bank trace before every active height |
| [Unfoldings.Cap.CenteredClosedBankTrace](../Unfoldings/Cap/CenteredClosedBankTrace.lean) | Construct visible actual bank traces and full closed-trace injectivity together |
| [Unfoldings.Cap.CenteredTraceInjectivity](../Unfoldings/Cap/CenteredTraceInjectivity.lean) | Actual continuous strip traces are injective on their whole approached boundary |
| [Unfoldings.Cap.ExtendedProperComparisonArcs](../Unfoldings/Cap/ExtendedProperComparisonArcs.lean) | Uniform construction of proper comparison arcs in the actual radial matched-bank calibration |
| [Unfoldings.Cap.ProperComparisonData](../Unfoldings/Cap/ProperComparisonData.lean) | Proper comparison arcs retaining actual contour copies, bounded physical prefixes, and circle order |
| [Unfoldings.Cap.ProperComparisonArcs](../Unfoldings/Cap/ProperComparisonArcs.lean) | Constructed simple comparison subarcs ending on one source circle in derived bank order |
| [Unfoldings.Cap.SimpleComparisonPaths](../Unfoldings/Cap/SimpleComparisonPaths.lean) | Simple parametrizations with exactly the actual finite comparison-bank images |
| [Unfoldings.Cap.CompletedPrefixGraphs](../Unfoldings/Cap/CompletedPrefixGraphs.lean) | Actual finite comparison-bank graph homeomorphisms and visible-trace start values |
| [Unfoldings.Cap.CompletedTraceVertexCopy](../Unfoldings/Cap/CompletedTraceVertexCopy.lean) | Represent each actual one-sided branch trace value by its own contour copy |
| [Unfoldings.Cap.ExtendedBankGeometryBudget](../Unfoldings/Cap/ExtendedBankGeometryBudget.lean) | One uniform choice retains strict roof curvature, radial matched banks, and face bounds |
| [Unfoldings.Cap.CompletedPrefixCircleOrder](../Unfoldings/Cap/CompletedPrefixCircleOrder.lean) | Derived circle order and endpoint margins for actual bounded comparison prefixes |
| [Unfoldings.Cap.CompletedComparisonPrefixes](../Unfoldings/Cap/CompletedComparisonPrefixes.lean) | All points of finite comparison prefixes lie in the same developed source quadrant |
| [Unfoldings.Cap.CompletedComparisonQuadrants](../Unfoldings/Cap/CompletedComparisonQuadrants.lean) | Quantitative common-source quadrant bounds on actual comparison edges and branch gaps |
| [Unfoldings.Cap.CompletedComparisonValues](../Unfoldings/Cap/CompletedComparisonValues.lean) | Actual comparison-bank face values and branch chords between copies of one vertex |
| [Unfoldings.Cap.ExtendedRadiusPrefix](../Unfoldings/Cap/ExtendedRadiusPrefix.lean) | Constructed bounded fine-seam prefixes with common position and opening sectors |
| [Unfoldings.Cap.SectorSweepBall](../Unfoldings/Cap/SectorSweepBall.lean) | Physical source balls lie strictly inside every sector sweep below the cutoff |
| [Unfoldings.Cap.CompletedRadiusPrefix](../Unfoldings/Cap/CompletedRadiusPrefix.lean) | Actual completed cut paths reach a controlled source radius before the boundary |
| [Unfoldings.Cap.ExtendedBankChainPositions](../Unfoldings/Cap/ExtendedBankChainPositions.lean) | Derived common position and direction sectors for actual roof-meshed cut paths |
| [Unfoldings.Cap.GeometricComponentPieces](../Unfoldings/Cap/GeometricComponentPieces.lean) | Whole cut-piece positions and directions in the chosen geometric component sector |
| [Unfoldings.Cap.CompletedBankChainPositions](../Unfoldings/Cap/CompletedBankChainPositions.lean) | One sector for every fine path position, direction, and curved subtree |
| [Unfoldings.Cap.ExtendedWaterfallBankTraces](../Unfoldings/Cap/ExtendedWaterfallBankTraces.lean) | Construct complete actual bank traces from the common source through active heights |
| [Unfoldings.Cap.ExtendedFacePositionControl](../Unfoldings/Cap/ExtendedFacePositionControl.lean) | Uniform common-source position bounds for every actual roof face and bank copy |
| [Unfoldings.Cap.ProjectedSeamFaces](../Unfoldings/Cap/ProjectedSeamFaces.lean) | Regular projected seam points have exactly their two actual incident-face labels |
| [Unfoldings.Cap.CompletedBankPhysicalSides](../Unfoldings/Cap/CompletedBankPhysicalSides.lean) | Named entrance and exit incident faces have their actual physical side signs |
| [Unfoldings.Cap.CompletedBankGraphSides](../Unfoldings/Cap/CompletedBankGraphSides.lean) | Construct actual parent cut graphs and derive named face-side and strip-avoidance tests |
| [Unfoldings.Cap.CompletedBankTraceMatching](../Unfoldings/Cap/CompletedBankTraceMatching.lean) | Regular positive-width lower/upper strip traces select actual entrance/exit charts |
| [Unfoldings.Cap.RegularWaterfallWidth](../Unfoldings/Cap/RegularWaterfallWidth.lean) | Regular actual bank points avoid the pinch set and have positive width before active heights |
| [Unfoldings.Cap.ClosedSectorStrip](../Unfoldings/Cap/ClosedSectorStrip.lean) | Both closed sector-strip banks stay within their diagonal sweep-height ball |
| [Unfoldings.Cap.RegularWaterfallBankWidth](../Unfoldings/Cap/RegularWaterfallBankWidth.lean) | Deep clipping and subdivision bounds derive actual regular bank width without an interior-location hypothesis |
| [Unfoldings.Cap.MatchedBankTrace](../Unfoldings/Cap/MatchedBankTrace.lean) | Complete one-sided traces match every regular named parent-bank piece before active heights |
| [Unfoldings.Cap.ExtendedMatchedBankTraces](../Unfoldings/Cap/ExtendedMatchedBankTraces.lean) | Construct actual waterfall traces with derived width, cut avoidance, and named regular-bank matching |
| [Unfoldings.Cap.CenteredTraceSourceError](../Unfoldings/Cap/CenteredTraceSourceError.lean) | Extend actual source-position error to every visible one-sided trace point |
| [Unfoldings.Cap.CenteredBankTraceRadial](../Unfoldings/Cap/CenteredBankTraceRadial.lean) | Actual visible bank traces progress strictly radially from quantitative chart and sector margins |
| [Unfoldings.Cap.ExtendedRadialBankTraces](../Unfoldings/Cap/ExtendedRadialBankTraces.lean) | Uniform actual bank calibration with radial matched traces, whole-strip injectivity, and arbitrary position error |
| [Unfoldings.Cap.CompletedFaceCopyOrder](../Unfoldings/Cap/CompletedFaceCopyOrder.lean) | Every actual branch and visible trace copy lies between its named entrance and exit banks |
| [Unfoldings.Cap.CompletedComparisonChains](../Unfoldings/Cap/CompletedComparisonChains.lean) | Actual outward parent banks completed by explicit straight branch-copy gaps |
| [Unfoldings.Cap.CompletedComparisonProgress](../Unfoldings/Cap/CompletedComparisonProgress.lean) | Whole comparison-bank coordinate injectivity and opposite-bank circle order |
| [Unfoldings.Cap.CompletedExcursionStrictOrder](../Unfoldings/Cap/CompletedExcursionStrictOrder.lean) | Actual branch excursions and endpoint-copy gaps vanish if a controlling coordinate does |
| [Unfoldings.Cap.WaterfallBankControl](../Unfoldings/Cap/WaterfallBankControl.lean) | One calibration retains radial matched banks, all-face distance bounds, and branch-gap quadrant margins |
| [Unfoldings.Cap.ExtendedBankGeometry](../Unfoldings/Cap/ExtendedBankGeometry.lean) | Uniform all-copy source quadrants and radial matched bank control in the same actual calibration |
| [Unfoldings.Cap.ExtendedWaterfallRegular](../Unfoldings/Cap/ExtendedWaterfallRegular.lean) | One constructed waterfall retains geometric cut avoidance, pinch control, and all-development coherence |
| [Unfoldings.Cap.ExtendedRegularBankTraces](../Unfoldings/Cap/ExtendedRegularBankTraces.lean) | Preserve actual geometric regularity and pinch control for the same complete bank traces |
| [Unfoldings.Cap.GeometricTailLocalEdge](../Unfoldings/Cap/GeometricTailLocalEdge.lean) | Actual regular meshed tail points retain locally matching physical edge graphs |
| [Unfoldings.Cap.TraceFacingFace](../Unfoldings/Cap/TraceFacingFace.lean) | One-sided strip traces select the facing seam chart from local wall and half-plane data |
| [Unfoldings.Cap.CompletedBankFaceValues](../Unfoldings/Cap/CompletedBankFaceValues.lean) | Complete actual bank points equal their own incident-face placements |
| [Unfoldings.Cap.CompletedBankPositionMargins](../Unfoldings/Cap/CompletedBankPositionMargins.lean) | Transfer common-source position and quadrant bounds to named complete banks |
| [Unfoldings.Cap.CompletedBankCircleOrder](../Unfoldings/Cap/CompletedBankCircleOrder.lean) | Opposite branching banks in a common quadrant have the correct equal-radius order |
| [Unfoldings.Cap.ExtendedFaceQuadrants](../Unfoldings/Cap/ExtendedFaceQuadrants.lean) | Uniform positive sector-quadrant margins for every actual face and branch copy |
| [Unfoldings.Cap.FacePositionMargins](../Unfoldings/Cap/FacePositionMargins.lean) | Frame-independent actual face error and norm-relative quadrant coordinate margins |
| [Unfoldings.Cap.WaterfallFaceError](../Unfoldings/Cap/WaterfallFaceError.lean) | Extend strict-strip estimates to all containing-face values without identifying cut copies |
| [Unfoldings.Cap.CenteredFrameError](../Unfoldings/Cap/CenteredFrameError.lean) | Frame independence of actual common-source position error |
| [Unfoldings.Cap.ProjectedInteriorCoherence](../Unfoldings/Cap/ProjectedInteriorCoherence.lean) | Unique containing faces and actual map values at projected face interiors |
| [Unfoldings.Cap.SectorWaterfallDensity](../Unfoldings/Cap/SectorWaterfallDensity.lean) | Strict sector cells are dense within each projected face in the open sweep region |
| [Unfoldings.Cap.CenteredTraceValues](../Unfoldings/Cap/CenteredTraceValues.lean) | Trace values are approached through their own faces and match coherent copies |
| [Unfoldings.Cap.CenteredBankTrace](../Unfoldings/Cap/CenteredBankTrace.lean) | Complete source-based bank traces with actual one-sided containing-face visibility |
| [Unfoldings.Cap.ExtendedWaterfallTraces](../Unfoldings/Cap/ExtendedWaterfallTraces.lean) | Actual whole-strip maps are uniformly Lipschitz and have containing-face boundary traces |
| [Unfoldings.Cap.ExtendedWaterfallCoherent](../Unfoldings/Cap/ExtendedWaterfallCoherent.lean) | One constructed waterfall has coherent domains for every minimal development |
| [Unfoldings.Cap.CenteredMapTrace](../Unfoldings/Cap/CenteredMapTrace.lean) | Construct unique one-sided actual strip traces retaining containing-face placements |
| [Unfoldings.Cap.SectorPositionMargins](../Unfoldings/Cap/SectorPositionMargins.lean) | Uniform positive coordinate margins for enclosing sector strips |
| [Unfoldings.Cap.ProjectedLinearError](../Unfoldings/Cap/ProjectedLinearError.lean) | Derive linear chart proximity to identity from angular and normal control |
| [Unfoldings.Cap.ExtendedWaterfallQuadrants](../Unfoldings/Cap/ExtendedWaterfallQuadrants.lean) | Actual whole-strip images stay in their sector quadrants relative to the common source |
| [Unfoldings.Cap.ExtendedWaterfallControl](../Unfoldings/Cap/ExtendedWaterfallControl.lean) | Uniform actual strip injectivity and requested common-source position control |
| [Unfoldings.Cap.DevelopedDirectionNorm](../Unfoldings/Cap/DevelopedDirectionNorm.lean) | Actual developed-vector lengths and exact normal-dependent metric bounds |
| [Unfoldings.Cap.CompletedLinearError](../Unfoldings/Cap/CompletedLinearError.lean) | Uniform bank quadrants and arbitrarily small linear chart error in one calibration |
| [Unfoldings.Cap.CenteredMapSourceError](../Unfoldings/Cap/CenteredMapSourceError.lean) | Actual developed source-position error through coherent reopening pinches |
| [Unfoldings.Cap.ExtendedBankChainClosedSeparation](../Unfoldings/Cap/ExtendedBankChainClosedSeparation.lean) | Uniform actual closed bank contacts identify the same projected surface point |
| [Unfoldings.Cap.CompletedBankClosedContact](../Unfoldings/Cap/CompletedBankClosedContact.lean) | Classify all closed opposite-bank contacts, including flat branch contacts |
| [Unfoldings.Cap.ExtendedWaterfallFullInjective](../Unfoldings/Cap/ExtendedWaterfallFullInjective.lean) | Uniform actual-map injectivity on each entire strip across all reopening pinches |
| [Unfoldings.Cap.GeometricWaterfallRegular](../Unfoldings/Cap/GeometricWaterfallRegular.lean) | Derive regular strip interiors from retained actual leaf tails |
| [Unfoldings.Cap.GeometricTailBankContacts](../Unfoldings/Cap/GeometricTailBankContacts.lean) | Beyond the starting leaf every sector-bank contact is on the radial skirt |
| [Unfoldings.Cap.GeometricSectorBankPoints](../Unfoldings/Cap/GeometricSectorBankPoints.lean) | Actual enclosing bank rays fail the strict sector-coordinate test |
| [Unfoldings.Cap.GeometricRecoverableWaterfall](../Unfoldings/Cap/GeometricRecoverableWaterfall.lean) | Construct actual waterfall strips whose reopening pinches are sources or leaves |
| [Unfoldings.Cap.GeometricRadialGraphs](../Unfoldings/Cap/GeometricRadialGraphs.lean) | Exact radial height graphs covered by the actual sector cut network |
| [Unfoldings.Cap.GeometricRadialEdges](../Unfoldings/Cap/GeometricRadialEdges.lean) | Construct the genuine seed-to-tip geometric edge in every active component |
| [Unfoldings.Cap.GeometricBankPersistence](../Unfoldings/Cap/GeometricBankPersistence.lean) | Derive permanent exterior-bank contact after the actual starting leaf |
| [Unfoldings.Cap.StrictGeometricTailGraphs](../Unfoldings/Cap/StrictGeometricTailGraphs.lean) | Derive strict coordinate progress from actual whole cut paths and sector walls |
| [Unfoldings.Cap.GeometricSectorBoundaryLeaves](../Unfoldings/Cap/GeometricSectorBoundaryLeaves.lean) | A nonterminal geometric node on a sector bank is childless |
| [Unfoldings.Cap.CenteredCoherentMap](../Unfoldings/Cap/CenteredCoherentMap.lean) | Actual source-centered map continuity and strip injectivity across coherent reopening pinches |
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
| [Unfoldings.Geometry.QuadrantCircleInterval](../Unfoldings/Geometry/QuadrantCircleInterval.lean) | Two possible bank values force a single angular interval within a source quadrant |
| [Unfoldings.Geometry.QuadrantCircle](../Unfoldings/Geometry/QuadrantCircle.lean) | Continuous horizontal parametrization of source circles in a positive quadrant |
| [Unfoldings.Geometry.MonotoneStripImageFrontier](../Unfoldings/Geometry/MonotoneStripImageFrontier.lean) | Whole developed strip-image frontiers consist of actual bank and end-level values |
| [Unfoldings.Geometry.MonotoneStripTopology](../Unfoldings/Geometry/MonotoneStripTopology.lean) | Compact bounded strip closures and exact physical bank/end frontier alternatives |
| [Unfoldings.Geometry.RecoverableStripLowerBound](../Unfoldings/Geometry/RecoverableStripLowerBound.lean) | Uniform lower separation through coherent reopening pinches and trace closure |
| [Unfoldings.Geometry.MonotoneStripLowerBound](../Unfoldings/Geometry/MonotoneStripLowerBound.lean) | Quantitative distance separation for continuous finite affine selections on bounded strips |
| [Unfoldings.Geometry.ChainGraphArc](../Unfoldings/Geometry/ChainGraphArc.lean) | Simple-arc parametrizations retaining the entire geometric chain image |
| [Unfoldings.Geometry.ChainTruncationLinear](../Unfoldings/Geometry/ChainTruncationLinear.lean) | Weak coordinate progress and flat zero steps persist under exact truncation |
| [Unfoldings.Geometry.ChainLinearGraph](../Unfoldings/Geometry/ChainLinearGraph.lean) | The entire chain image is homeomorphic to its controlling-coordinate interval |
| [Unfoldings.Geometry.ChainPaths](../Unfoldings/Geometry/ChainPaths.lean) | Continuous concatenated chain paths with exactly the original closed-edge image |
| [Unfoldings.Geometry.QuadrantSegments](../Unfoldings/Geometry/QuadrantSegments.lean) | Linear quadrant margins and source-centered direction wedges on entire chords |
| [Unfoldings.Geometry.ChainTruncation](../Unfoldings/Geometry/ChainTruncation.lean) | Exact finite polygonal-chain prefixes ending partway through an actual edge |
| [Unfoldings.Geometry.ChainRadiusCrossing](../Unfoldings/Geometry/ChainRadiusCrossing.lean) | An outward chain reaches a prescribed sphere with its preceding path inside the ball |
| [Unfoldings.Geometry.HeightNetworkChainTracking](../Unfoldings/Geometry/HeightNetworkChainTracking.lean) | A monotone fine chain and a tail with the same start follow the same forward-deterministic network |
| [Unfoldings.Geometry.ChainPointCoverLabels](../Unfoldings/Geometry/ChainPointCoverLabels.lean) | Every whole-edge point of a covered fine chain retains its starting component label |
| [Unfoldings.Geometry.SubdivisionWallContacts](../Unfoldings/Geometry/SubdivisionWallContacts.lean) | Recorded walls that meet and later separate have a contact in the coherent pinch set |
| [Unfoldings.Geometry.RecoverableStripRadiusCrossing](../Unfoldings/Geometry/RecoverableStripRadiusCrossing.lean) | Source-to-strip core paths cross every intermediate circle outside the pinch radii |
| [Unfoldings.Geometry.MonotoneStripTerminalPinch](../Unfoldings/Geometry/MonotoneStripTerminalPinch.lean) | A bounded nonempty strip that stops before the cutoff has an approached permanent terminal pinch |
| [Unfoldings.Geometry.SubdivisionFreshTargets](../Unfoldings/Geometry/SubdivisionFreshTargets.lean) | Targets avoiding existing separators belong to positive-width subdivision cells |
| [Unfoldings.Geometry.StripInsertionTerminalTail](../Unfoldings/Geometry/StripInsertionTerminalTail.lean) | Permanently merged child strips follow the actual inserted tail after its leaf |
| [Unfoldings.Geometry.RayStripWidth](../Unfoldings/Geometry/RayStripWidth.lean) | Distinct positive rays enclose positive strip width at every positive height |
| [Unfoldings.Geometry.VertexPinchWaterfall](../Unfoldings/Geometry/VertexPinchWaterfall.lean) | Construct recoverable waterfall subdivisions with all approached pinches confined to specified vertices |
| [Unfoldings.Geometry.ApproachedStripInsertion](../Unfoldings/Geometry/ApproachedStripInsertion.lean) | Strict source prefixes and locally affine tails preserve the approached-pinch invariant |
| [Unfoldings.Geometry.AffineGraphPinches](../Unfoldings/Geometry/AffineGraphPinches.lean) | Ordered locally affine banks cannot have an approached zero-width pinch |
| [Unfoldings.Geometry.RecoverableStripInitialClosure](../Unfoldings/Geometry/RecoverableStripInitialClosure.lean) | Every earlier carrier point lies in the approached closure of a finitely pinched strip |
| [Unfoldings.Geometry.RecoverableStripClosure](../Unfoldings/Geometry/RecoverableStripClosure.lean) | Finite reopening pinches leave both source-to-active banks in the strict-strip closure |
| [Unfoldings.Geometry.MonotoneStripDensity](../Unfoldings/Geometry/MonotoneStripDensity.lean) | Finite waterfall walls are closed nowhere dense; off-wall points lie in strict cells |
| [Unfoldings.Geometry.HeightNetworkLocalGraph](../Unfoldings/Geometry/HeightNetworkLocalGraph.lean) | Covered tails agree locally with their actual affine edge graphs away from network vertices |
| [Unfoldings.Geometry.HeightGraphSegments](../Unfoldings/Geometry/HeightGraphSegments.lean) | Exact whole-segment graphs, directed-side formulas, and transported cut avoidance |
| [Unfoldings.Geometry.NearIdentityRadial](../Unfoldings/Geometry/NearIdentityRadial.lean) | Derive positive radial tests from linear chart error and source-position margins |
| [Unfoldings.Geometry.HeightGraphRadial](../Unfoldings/Geometry/HeightGraphRadial.lean) | Monotone height graphs give strict radial progress through continuous finite face selections |
| [Unfoldings.Geometry.MixedBankOrder](../Unfoldings/Geometry/MixedBankOrder.lean) | Paired-bank circle order needs rightward right-bank and upward left-bank progress, allowing branch-gap steps |
| [Unfoldings.Geometry.InterleavedSegments](../Unfoldings/Geometry/InterleavedSegments.lean) | Explicit alternating original and gap segments, retaining repeated endpoints |
| [Unfoldings.Geometry.StrictQuadrantSums](../Unfoldings/Geometry/StrictQuadrantSums.lean) | A sum of zero or strictly up-left vectors vanishes whenever either coordinate does |
| [Unfoldings.Geometry.WeakChainLinear](../Unfoldings/Geometry/WeakChainLinear.lean) | A monotone controlling coordinate distinguishes all actual chain points when zero steps are flat |
| [Unfoldings.Geometry.RecoverableStripRegularWidth](../Unfoldings/Geometry/RecoverableStripRegularWidth.lean) | Derive positive strip width from a later active height and avoidance of reopening pinches |
| [Unfoldings.Geometry.WedgeFrameSides](../Unfoldings/Geometry/WedgeFrameSides.lean) | Positive acute-wedge frames preserve every actual directed-edge side, including centered coordinates |
| [Unfoldings.Geometry.StripCutSides](../Unfoldings/Geometry/StripCutSides.lean) | Positive strip width and cut avoidance force the local side even at a mere wall contact |
| [Unfoldings.Geometry.MonotoneStripLipschitz](../Unfoldings/Geometry/MonotoneStripLipschitz.lean) | Uniform Lipschitz bounds for affine selections on bounded monotone strips |
| [Unfoldings.Geometry.MonotoneStripCoreLipschitz](../Unfoldings/Geometry/MonotoneStripCoreLipschitz.lean) | Uniform strict-strip Lipschitz bounds across coherent reopening pinches |
| [Unfoldings.Geometry.FiniteSelectionNormBounds](../Unfoldings/Geometry/FiniteSelectionNormBounds.lean) | Upper norm bounds across arbitrary continuous affine chart switches |
| [Unfoldings.Geometry.FiniteSelectionRadial](../Unfoldings/Geometry/FiniteSelectionRadial.lean) | Linear tests and radial progress through arbitrary continuous affine chart switches |
| [Unfoldings.Geometry.NearIdentityMargins](../Unfoldings/Geometry/NearIdentityMargins.lean) | Small linear error supplies the four strict axis tests for strip injectivity |
| [Unfoldings.Geometry.MonotoneStripSourceError](../Unfoldings/Geometry/MonotoneStripSourceError.lean) | Whole-strip source-position estimates across coherent reopening pinches |
| [Unfoldings.Geometry.FiniteSelectionError](../Unfoldings/Geometry/FiniteSelectionError.lean) | Quantitative affine error survives arbitrary continuous face-chart switches |
| [Unfoldings.Geometry.AngleNormError](../Unfoldings/Geometry/AngleNormError.lean) | Small relative length and angular errors give uniform vector error |
| [Unfoldings.Geometry.StripSubdivisionInvariant](../Unfoldings/Geometry/StripSubdivisionInvariant.lean) | Preserve cell invariants while constructing and retaining finite separators |
| [Unfoldings.Geometry.RecoverableWaterfall](../Unfoldings/Geometry/RecoverableWaterfall.lean) | Construct finite waterfalls with strict walls and controlled reopening pinches |
| [Unfoldings.Geometry.RecoverableStripInsertion](../Unfoldings/Geometry/RecoverableStripInsertion.lean) | Connector-and-tail insertions preserve the reopening-pinch invariant |
| [Unfoldings.Geometry.RayStripPinches](../Unfoldings/Geometry/RayStripPinches.lean) | Source-ray banks are homogeneous and reopen only at their common source |
| [Unfoldings.Geometry.RayHeightSegments](../Unfoldings/Geometry/RayHeightSegments.lean) | Exact ray graph points cover all intermediate heights of radial network edges |
| [Unfoldings.Geometry.HeightGraphLatticePoints](../Unfoldings/Geometry/HeightGraphLatticePoints.lean) | An envelope point is on one of its actual defining graphs |
| [Unfoldings.Geometry.RecoverableStripInjective](../Unfoldings/Geometry/RecoverableStripInjective.lean) | Compare separate positive-width strip components through coherent reopening pinches |
| [Unfoldings.Geometry.RecoverableStripPinches](../Unfoldings/Geometry/RecoverableStripPinches.lean) | Track and preserve reopening pinches under insertion, excluding permanent mergers |
| [Unfoldings.Geometry.ChainStrictHeightGraph](../Unfoldings/Geometry/ChainStrictHeightGraph.lean) | Exact whole-edge height representations inherit strict coordinate progress |
| [Unfoldings.Geometry.StrictStripInsertion](../Unfoldings/Geometry/StrictStripInsertion.lean) | Strict waterfall connectors and insertion walls, including exterior-bank targets |
| [Unfoldings.Geometry.StrictHeightGraphs](../Unfoldings/Geometry/StrictHeightGraphs.lean) | Strict coordinate progress under envelopes, rays, and splicing |
| [Unfoldings.Geometry.MonotoneStripCore](../Unfoldings/Geometry/MonotoneStripCore.lean) | Inset comparison through coherent zero-width strip pinches |
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
| [Unfoldings.Topology.FiniteRadiusAvoidance](../Unfoldings/Topology/FiniteRadiusAvoidance.lean) | Open overlap is detected on source circles outside any finite exceptional radius set |
| [Unfoldings.Topology.DenseChartSeparation](../Unfoldings/Topology/DenseChartSeparation.lean) | Injectivity on an open dense set separates open images of actual homeomorphic charts |
| [Unfoldings.Topology.IntervalFrontier](../Unfoldings/Topology/IntervalFrontier.lean) | A bounded nonempty open real set with two possible frontier points is their interval |
| [Unfoldings.Topology.CompactImageFrontier](../Unfoldings/Topology/CompactImageFrontier.lean) | Exact frontier transport for continuous planar maps injective on compact closures |
| [Unfoldings.Topology.ClosureLowerBound](../Unfoldings/Topology/ClosureLowerBound.lean) | Continuous lower distance bounds and injectivity extend to the whole domain closure |
| [Unfoldings.Topology.SphereArc](../Unfoldings/Topology/SphereArc.lean) | Simple arcs first reaching a prescribed source sphere only at their final point |
| [Unfoldings.Topology.IntervalArc](../Unfoldings/Topology/IntervalArc.lean) | Injective continuous paths for sets homeomorphic to nondegenerate real intervals |
| [Unfoldings.Topology.PathRadiusExit](../Unfoldings/Topology/PathRadiusExit.lean) | First source-sphere crossings with strictly interior preceding paths and preserved simplicity |
| [Unfoldings.Topology.FiniteSelectionVisibility](../Unfoldings/Topology/FiniteSelectionVisibility.lean) | Trace branches are approached through their own actual closed pieces |
| [Unfoldings.Topology.FiniteSelectionClosure](../Unfoldings/Topology/FiniteSelectionClosure.lean) | Finite closed-piece selections retain actual branch values at closure points |
| [Unfoldings.Topology.ComplexLipschitzExtension](../Unfoldings/Topology/ComplexLipschitzExtension.lean) | Continuous planar extensions and uniqueness of their closure traces |
| [Unfoldings.Topology.FiniteSelectionBounds](../Unfoldings/Topology/FiniteSelectionBounds.lean) | Two-sided increment bounds for arbitrary continuous finite selections |
| [Unfoldings.Topology.FiniteStrictPieces](../Unfoldings/Topology/FiniteStrictPieces.lean) | Ordered strict pieces can contact only at a common endpoint of adjacent pieces |
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

| [Unfoldings.Cap.ActiveNormalSlopes](../Unfoldings/Cap/ActiveNormalSlopes.lean) | All original support slopes active at a regular cap point are collinear |
| [Unfoldings.Cap.OriginalCurvatureSupport](../Unfoldings/Cap/OriginalCurvatureSupport.lean) | Actual roof curvature inside the original cap occurs only at original cap vertices |
| [Unfoldings.Cap.SkirtCurvatureSeeds](../Unfoldings/Cap/SkirtCurvatureSeeds.lean) | Finite skirt seeds selected before meshing cover all new positive curvature up to original vertices |
| [Unfoldings.Cap.ExtendedCutCurvature](../Unfoldings/Cap/ExtendedCutCurvature.lean) | Constructed original forest edges and skirt continuations cover every actual positive-curvature vertex |
| [Unfoldings.Geometry.AffineSupportingChord](../Unfoldings/Geometry/AffineSupportingChord.lean) | A nonnegative affine function vanishing inside a chord vanishes at both endpoints |
| [Unfoldings.Geometry.NonvertexChord](../Unfoldings/Geometry/NonvertexChord.lean) | Every nonvertex triangle point lies strictly inside a nondegenerate chord |

| [Unfoldings.Cap.ClipInteriorSeams](../Unfoldings/Cap/ClipInteriorSeams.lean) | Interior geometric cut edges have actual physical seam partners and select removed seams |
| [Unfoldings.Cap.CurvatureCutDevelopment](../Unfoldings/Cap/CurvatureCutDevelopment.lean) | Cutting positive-curvature endpoints suffices for flat interior and local disk development |
| [Unfoldings.Cap.ExtendedCutFlat](../Unfoldings/Cap/ExtendedCutFlat.lean) | The actual constructed extended retained-seam set has flat interior vertex copies |
| [Unfoldings.Cap.ExtendedCutMesh](../Unfoldings/Cap/ExtendedCutMesh.lean) | Whole fine edges and actual removed seams realize the extended geometric cuts |
| [Unfoldings.Cap.ExtendedCutDevelopment](../Unfoldings/Cap/ExtendedCutDevelopment.lean) | Constructed extended forest cuts give a disk and a locally isometric development |
| [Unfoldings.Cap.ExtendedCutForest](../Unfoldings/Cap/ExtendedCutForest.lean) | Select actual outward fine seams in the original cuts and meshed skirt components |
| [Unfoldings.Cap.ExtendedCutGrowth](../Unfoldings/Cap/ExtendedCutGrowth.lean) | Local radial progress on the constructed geometric extended cuts, including junctions |
| [Unfoldings.Cap.ParentRadialGrowth](../Unfoldings/Cap/ParentRadialGrowth.lean) | Strict radial distance increase along every original selected parent edge |
| [Unfoldings.Cap.RadialCutForest](../Unfoldings/Cap/RadialCutForest.lean) | Source-distance parent choices give actual boundary-rooted cut forests and cut disks |
| [Unfoldings.Cap.RadialCutNeighbor](../Unfoldings/Cap/RadialCutNeighbor.lean) | Local radial progress chooses actual seams with strictly farther intrinsic endpoints |
| [Unfoldings.Cap.RadialForestDevelopment](../Unfoldings/Cap/RadialForestDevelopment.lean) | Curvature coverage makes the constructed radial forest disk develop locally isometrically |
| [Unfoldings.Complex.SelectedCutRootSupport](../Unfoldings/Complex/SelectedCutRootSupport.lean) | Allow unused isolated parent roots outside the actual cut graph |
| [Unfoldings.Geometry.LocalRadialGrowth](../Unfoldings/Geometry/LocalRadialGrowth.lean) | Arbitrarily near outward progress on whole original and radial continuation segments |
| [Unfoldings.Geometry.LocalRadialPieces](../Unfoldings/Geometry/LocalRadialPieces.lean) | A fixed piece witnesses local outward progress in a finite cover |
| [Unfoldings.Geometry.OutwardSegmentNeighbor](../Unfoldings/Geometry/OutwardSegmentNeighbor.lean) | A finite segment cover turns local radial progress into an outward incident segment |
| [Unfoldings.Cap.ProjectedSeamEndpoints](../Unfoldings/Cap/ProjectedSeamEndpoints.lean) | Projected seam-edge vertices are actual intrinsic endpoints of that seam |
| [Unfoldings.Complex.CutEndpointBoundary](../Unfoldings/Complex/CutEndpointBoundary.lean) | Every cut copy of a removed seam endpoint lies on the actual bank boundary |
| [Unfoldings.Complex.InteriorCopyAngles](../Unfoldings/Complex/InteriorCopyAngles.lean) | A vertex copy still in the cut interior retains the entire original corner angle |

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
| [Unfoldings.Cap.CompletedCrossingPotential](../Unfoldings/Cap/CompletedCrossingPotential.lean) | Mesh-independent signed crossing potentials require acute paths only for positive curvature |
| [Unfoldings.Cap.CompletedForestBanks](../Unfoldings/Cap/CompletedForestBanks.lean) | Actual subtree bank rotations and zero apertures for added flat branches |
| [Unfoldings.Cap.CompletedParentDirections](../Unfoldings/Cap/CompletedParentDirections.lean) | Completed forest bank rotations in one projection-preserving frame |
| [Unfoldings.Cap.ExtendedOutwardForest](../Unfoldings/Cap/ExtendedOutwardForest.lean) | Constructed extended fine-seam forests with whole-edge radial control |
| [Unfoldings.Cap.ExtendedRootPaths](../Unfoldings/Cap/ExtendedRootPaths.lean) | Original root paths and complete radial continuations retain one acute wedge |
| [Unfoldings.Cap.OutwardCutNeighbor](../Unfoldings/Cap/OutwardCutNeighbor.lean) | Local radial progress selects whole-edge outward incident seams |
| [Unfoldings.Cap.OutwardRadialForest](../Unfoldings/Cap/OutwardRadialForest.lean) | Outward forest construction and uniqueness of root-path points at each radius |
| [Unfoldings.Cap.RadialForestCompletion](../Unfoldings/Cap/RadialForestCompletion.lean) | Connect unused flat vertices without changing existing cuts or curvature-carrying paths |
| [Unfoldings.Cap.UnrestrictedRadialProgress](../Unfoldings/Cap/UnrestrictedRadialProgress.lean) | Source-distance ascent in arbitrary cap triangulations without acuteness |
| [Unfoldings.Development.AdditionalCuts](../Unfoldings/Development/AdditionalCuts.lean) | Additional cuts preserve rigid face placements and nonoverlap |
| [Unfoldings.Geometry.ChainAppend](../Unfoldings/Geometry/ChainAppend.lean) | Append a final chain edge while retaining all wedge directions |
| [Unfoldings.Geometry.LocalRadialSegment](../Unfoldings/Geometry/LocalRadialSegment.lean) | Local radial progress at a segment start characterizes its outward scalar product |
| [Unfoldings.Geometry.MeshHalfplaneProgress](../Unfoldings/Geometry/MeshHalfplaneProgress.lean) | Any open halfplane contains an outgoing edge at an interior mesh vertex |
| [Unfoldings.Topology.SelectedRootCompletion](../Unfoldings/Topology/SelectedRootCompletion.lean) | Connect unused parent roots while preserving selected edges and the potential |
| [Unfoldings.Topology.SupportedSubtreeWeights](../Unfoldings/Topology/SupportedSubtreeWeights.lean) | Only positive-weight root paths need signed crossing bounds |
| [Unfoldings.Geometry.SegmentCoverDirections](../Unfoldings/Geometry/SegmentCoverDirections.lean) | Whole outward meshed edges inherit positive directions and common wedges from a finite segment cover |
| [Unfoldings.Geometry.SegmentCoverLabels](../Unfoldings/Geometry/SegmentCoverLabels.lean) | Consistent component labels are constant on a whole meshed segment |
| [Unfoldings.Geometry.ChainCoverWedges](../Unfoldings/Geometry/ChainCoverWedges.lean) | Whole meshed paths inherit a common acute wedge from their labeled component |
| [Unfoldings.Geometry.RadialTailLabels](../Unfoldings/Geometry/RadialTailLabels.lean) | A radial component meets an inner convex rim in at most one point |
| [Unfoldings.Cap.SkirtRimComponents](../Unfoldings/Cap/SkirtRimComponents.lean) | Original rim roots attach to unique radial components without merging distinct roots |
| [Unfoldings.Cap.OriginalCutLabels](../Unfoldings/Cap/OriginalCutLabels.lean) | Every geometric contact of original cut segments preserves its selected-tree root |
| [Unfoldings.Cap.ExtendedCutLabels](../Unfoldings/Cap/ExtendedCutLabels.lean) | Consistent component labels for all original cuts and skirt continuations |
| [Unfoldings.Cap.ExtendedComponentWedges](../Unfoldings/Cap/ExtendedComponentWedges.lean) | Derive a common acute wedge for each actual extended geometric cut component |
| [Unfoldings.Cap.CompletedRootPathSupport](../Unfoldings/Cap/CompletedRootPathSupport.lean) | Curvature-carrying completed paths stay on the original geometric cuts and inherit their wedges |
| [Unfoldings.Cap.ExtendedPathWedges](../Unfoldings/Cap/ExtendedPathWedges.lean) | Constructed extended fine-seam paths have proved acute wedges and uniform curvature crossing bounds |
| [Unfoldings.Cap.CompletedParentBankOpening](../Unfoldings/Cap/CompletedParentBankOpening.lean) | Construct actual parent-bank openings for completed roof cuts |
| [Unfoldings.Cap.CompletedParentBankSides](../Unfoldings/Cap/CompletedParentBankSides.lean) | Geometric crossing signs for actual completed parent banks |
| [Unfoldings.Cap.CompletedParentSectionPhase](../Unfoldings/Cap/CompletedParentSectionPhase.lean) | Signed descendant-curvature phases at completed parent-seam crossings |
| [Unfoldings.Cap.CompletedPhaseSectionTurn](../Unfoldings/Cap/CompletedPhaseSectionTurn.lean) | Curvature-corrected section turns in the common completed-forest frame |
| [Unfoldings.Cap.CompletedSectionPhases](../Unfoldings/Cap/CompletedSectionPhases.lean) | Local signed phases and spatial residual turns at actual completed seams |
| [Unfoldings.Cap.CompletedTracePhaseTransport](../Unfoldings/Cap/CompletedTracePhaseTransport.lean) | Construct real unreduced headings from actual completed-bank phases |
| [Unfoldings.Cap.CompletedParentRayCounter](../Unfoldings/Cap/CompletedParentRayCounter.lean) | Actual section counters equal the bounded completed-forest ray counters |
| [Unfoldings.Cap.CompletedSectionCounterGeometry](../Unfoldings/Cap/CompletedSectionCounterGeometry.lean) | Identify completed-parent counter changes with the actual transition seam |
| [Unfoldings.Cap.CompletedSectionPotentialIdentity](../Unfoldings/Cap/CompletedSectionPotentialIdentity.lean) | Actual completed-bank phases telescope to the bounded curvature potential |
| [Unfoldings.Cap.CompletedSectionHeadingBound](../Unfoldings/Cap/CompletedSectionHeadingBound.lean) | Uniform real section headings and face alignment for completed roof forests |
| [Unfoldings.Cap.CompletedFaceDirectionAgreement](../Unfoldings/Cap/CompletedFaceDirectionAgreement.lean) | All directions of all actual faces agree with one common rim face |
| [Unfoldings.Cap.CompletedProjectionCalibration](../Unfoldings/Cap/CompletedProjectionCalibration.lean) | One globally projection-calibrated frame for completed-forest developments |
| [Unfoldings.Cap.CompletedCalibratedThreshold](../Unfoldings/Cap/CompletedCalibratedThreshold.lean) | A tilt threshold before the whole mesh bounds every actual developed direction |
| [Unfoldings.Cap.ExtendedDirectionControl](../Unfoldings/Cap/ExtendedDirectionControl.lean) | Uniform direction control for the constructed roof extension without auxiliary acuteness or path certificates |
| [Unfoldings.Geometry.SubsegmentEndpoints](../Unfoldings/Geometry/SubsegmentEndpoints.lean) | A fine subsegment containing an old endpoint has that same endpoint |
| [Unfoldings.Cap.ClipEndpointVertices](../Unfoldings/Cap/ClipEndpointVertices.lean) | Whole-edge meshing preserves original intrinsic cap vertices |
| [Unfoldings.Cap.RadialSourceLeaf](../Unfoldings/Cap/RadialSourceLeaf.lean) | The source is an interior leaf even after completing unused flat vertices |
| [Unfoldings.Cap.ExtendedSourceLeaf](../Unfoldings/Cap/ExtendedSourceLeaf.lean) | Construct the surviving original source vertex and prove it is an actual extended-forest leaf |
| [Unfoldings.Cap.RadialSourceCopy](../Unfoldings/Cap/RadialSourceCopy.lean) | There is exactly one intrinsic cut copy of the interior source leaf |
| [Unfoldings.Cap.CompletedSourceGap](../Unfoldings/Cap/CompletedSourceGap.lean) | The two source-bank ends are the same actual intrinsic and developed point |
| [Unfoldings.Geometry.FiveSectors](../Unfoldings/Geometry/FiveSectors.lean) | Five acute direction sectors cover the whole extended roof, including the old forward gap |
| [Unfoldings.Geometry.FiveSectorFrames](../Unfoldings/Geometry/FiveSectorFrames.lean) | Five robust numerical quadrant frames with one positive common tolerance |
| [Unfoldings.Cap.CompletedSectorQuadrants](../Unfoldings/Cap/CompletedSectorQuadrants.lean) | One uniform threshold constructs actual calibrated five-sector quadrant data |
| [Unfoldings.Cap.CompletedBankVectorOrder](../Unfoldings/Cap/CompletedBankVectorOrder.lean) | Actual parent-bank curvature rotations order vectors in any common sector |
| [Unfoldings.Cap.ExtendedSectorControl](../Unfoldings/Cap/ExtendedSectorControl.lean) | Construct five common developed quadrant frames on the actual roof extension |
| [Unfoldings.Cap.CompletedParentBankDisplacements](../Unfoldings/Cap/CompletedParentBankDisplacements.lean) | Actual completed-parent contour displacements |
| [Unfoldings.Cap.CompletedBranchDisplacements](../Unfoldings/Cap/CompletedBranchDisplacements.lean) | Sum descendant vector openings into actual completed-parent position gaps |
| [Unfoldings.Cap.CompletedMatchedBankPoints](../Unfoldings/Cap/CompletedMatchedBankPoints.lean) | Exact matched-parameter bank gaps for the completed forest |
| [Unfoldings.Cap.CompletedBranchGapBalance](../Unfoldings/Cap/CompletedBranchGapBalance.lean) | Conserve endpoint gaps across immediate completed child branches |
| [Unfoldings.Cap.CompletedSubtreeDirections](../Unfoldings/Cap/CompletedSubtreeDirections.lean) | Propagate geometric component directions to nonzero descendant openings |
| [Unfoldings.Cap.CompletedBankPositionOrder](../Unfoldings/Cap/CompletedBankPositionOrder.lean) | Order complete branching position gaps while allowing arbitrary flat branches |
| [Unfoldings.Cap.CompletedSubtreeSectors](../Unfoldings/Cap/CompletedSubtreeSectors.lean) | Transfer component sectors to curvature-carrying completed subtrees |
| [Unfoldings.Cap.ExtendedComponentSectors](../Unfoldings/Cap/ExtendedComponentSectors.lean) | Place every actual geometric cut component in one of five fixed sectors |
| [Unfoldings.Cap.ExtendedSubtreeSectors](../Unfoldings/Cap/ExtendedSubtreeSectors.lean) | Derive common sectors for the actual roof parent subtrees |
| [Unfoldings.Cap.CompletedParentBankNoncrossing](../Unfoldings/Cap/CompletedParentBankNoncrossing.lean) | Strict separation and flat-contact tests for completed paired parent banks |
| [Unfoldings.Cap.CompletedFlatBanks](../Unfoldings/Cap/CompletedFlatBanks.lean) | Prove coincident positions and vectors for redundant flat subtree slits |
| [Unfoldings.Cap.ExtendedBankSeparation](../Unfoldings/Cap/ExtendedBankSeparation.lean) | Uniform paired-bank separation for the constructed actual roof forest |
| [Unfoldings.Geometry.MonotoneHeightGraph](../Unfoldings/Geometry/MonotoneHeightGraph.lean) | Coordinate-monotone height graphs, continuity, envelopes, and clamping |
| [Unfoldings.Geometry.MonotoneStrip](../Unfoldings/Geometry/MonotoneStrip.lean) | Closed monotone strips, internal connectors, and mixed-coordinate rectangles |
| [Unfoldings.Geometry.MonotoneStripPaths](../Unfoldings/Geometry/MonotoneStripPaths.lean) | Continuous coordinate-monotone paths within a strip |
| [Unfoldings.Topology.IntervalLocalOrder](../Unfoldings/Topology/IntervalLocalOrder.lean) | Telescope local forward relations and coordinate bounds along an interval |
| [Unfoldings.Geometry.MonotoneStripInjective](../Unfoldings/Geometry/MonotoneStripInjective.lean) | Derive global strip injectivity from local quantitative cone bounds |
| [Unfoldings.Topology.FiniteMonotoneSelection](../Unfoldings/Topology/FiniteMonotoneSelection.lean) | Continuous finite selections preserve monotonicity and coordinate bounds |
| [Unfoldings.Geometry.MonotoneStripSelection](../Unfoldings/Geometry/MonotoneStripSelection.lean) | Injectivity of continuous finite cone-controlled selections on strips |
| [Unfoldings.Geometry.AffineConeBounds](../Unfoldings/Geometry/AffineConeBounds.lean) | Four affine axis tests give common cone bounds and strip injectivity |
| [Unfoldings.Geometry.AngleAxisMargins](../Unfoldings/Geometry/AngleAxisMargins.lean) | One numerical angular tolerance gives all four affine axis tests |
| [Unfoldings.Cap.ProjectedStripMaps](../Unfoldings/Cap/ProjectedStripMaps.lean) | Actual calibrated face maps and axis margins in arbitrary strip coordinates |
| [Unfoldings.Cap.CompletedStripInjective](../Unfoldings/Cap/CompletedStripInjective.lean) | Uniform injectivity of coherent monotone strips for completed cap developments |
| [Unfoldings.Cap.ExtendedStripInjective](../Unfoldings/Cap/ExtendedStripInjective.lean) | Uniform coherent-strip injectivity on the actual constructed roof extension |
| [Unfoldings.Geometry.HeightGraphSplice](../Unfoldings/Geometry/HeightGraphSplice.lean) | Splice monotone height graphs and represent genuine monotone segments exactly |
| [Unfoldings.Geometry.ChainHeightGraph](../Unfoldings/Geometry/ChainHeightGraph.lean) | Represent every whole edge of a monotone polygonal chain by one height graph |
| [Unfoldings.Geometry.MonotoneStripInterior](../Unfoldings/Geometry/MonotoneStripInterior.lean) | Construct strictly internal monotone connectors through a target point |
| [Unfoldings.Geometry.MonotoneStripInsertion](../Unfoldings/Geometry/MonotoneStripInsertion.lean) | Insert a connector and tail; split a strip with exact coverage and intersection |
| [Unfoldings.Topology.DescendantLeaves](../Unfoldings/Topology/DescendantLeaves.lean) | Every nonroot lies above a childless descendant in any ascending sweep coordinate |
| [Unfoldings.Geometry.MonotoneStripSlab](../Unfoldings/Geometry/MonotoneStripSlab.lean) | Bounded-height strips preserve the constructed connecting paths |
| [Unfoldings.Geometry.MonotoneStripBoundedInjective](../Unfoldings/Geometry/MonotoneStripBoundedInjective.lean) | Finite affine selections are injective on bounded-height strips |
| [Unfoldings.Cap.CompletedBoundedStripInjective](../Unfoldings/Cap/CompletedBoundedStripInjective.lean) | Uniform actual-face strip injectivity using only a bounded domain |
| [Unfoldings.Cap.ExtendedBoundedStripInjective](../Unfoldings/Cap/ExtendedBoundedStripInjective.lean) | Uniform coherent bounded-strip injectivity on the constructed roof extension |
| [Unfoldings.Geometry.RadialTailAttachment](../Unfoldings/Geometry/RadialTailAttachment.lean) | An outer radial tail meets the inner convex rim exactly at its seed |
| [Unfoldings.Cap.SkirtAttachments](../Unfoldings/Cap/SkirtAttachments.lean) | Bijection between original rim vertices and attached skirt components |
| [Unfoldings.Cap.ExtendedCutParents](../Unfoldings/Cap/ExtendedCutParents.lean) | Explicit finite parent forest for the complete original-and-skirt geometric cuts |
| [Unfoldings.Cap.ExtendedCutCarrier](../Unfoldings/Cap/ExtendedCutCarrier.lean) | Identify the entire geometric cut set with the explicit forest edges and outer tips |
| [Unfoldings.Cap.ExtendedCutEmbedding](../Unfoldings/Cap/ExtendedCutEmbedding.lean) | Distinct actual positions for all original vertices, independent leaves, and tips |
| [Unfoldings.Cap.GeometricCutLabels](../Unfoldings/Cap/GeometricCutLabels.lean) | Preserve component labels and fixed direction sectors along geometric parents |
| [Unfoldings.Cap.GeometricCutPaths](../Unfoldings/Cap/GeometricCutPaths.lean) | Represent every complete geometric cut path by an exact monotone height graph |
| [Unfoldings.Cap.GeometricCutIncidence](../Unfoldings/Cap/GeometricCutIncidence.lean) | A geometric vertex on a cut edge is one of its actual endpoints |
| [Unfoldings.Cap.GeometricCutNoncrossing](../Unfoldings/Cap/GeometricCutNoncrossing.lean) | Distinct complete geometric cut edges meet only at common endpoints |
| [Unfoldings.Topology.DescendantLeavesWithin](../Unfoldings/Topology/DescendantLeavesWithin.lean) | Choose a descendant leaf using a coordinate ascending only within its subtree |
| [Unfoldings.Cap.GeometricLeafSweep](../Unfoldings/Cap/GeometricLeafSweep.lean) | Order geometric descendants and leaves in one fixed component sweep frame |
| [Unfoldings.Cap.GeometricLeafSupport](../Unfoldings/Cap/GeometricLeafSupport.lean) | Every whole geometric cut-edge point lies above a leaf whose path contains its edge |
| [Unfoldings.Cap.GeometricCutFlow](../Unfoldings/Cap/GeometricCutFlow.lean) | Unique half-open outgoing parent edge at every nonterminal geometric cut point |
| [Unfoldings.Geometry.CoalescingHeightGraphs](../Unfoldings/Geometry/CoalescingHeightGraphs.lean) | Coalescing tails preserve a consistent order on their common height interval |
| [Unfoldings.Topology.FiniteClosedActive](../Unfoldings/Topology/FiniteClosedActive.lean) | Finite closed covers use only locally active pieces near a point |
| [Unfoldings.Geometry.SegmentHeightUnique](../Unfoldings/Geometry/SegmentHeightUnique.lean) | A strictly increasing linear height determines each point of a segment |
| [Unfoldings.Geometry.HeightSegmentNetwork](../Unfoldings/Geometry/HeightSegmentNetwork.lean) | Derive permanent tail coalescence from finite forward-deterministic segments |
| [Unfoldings.Cap.GeometricHeightNetwork](../Unfoldings/Cap/GeometricHeightNetwork.lean) | Construct actual component networks in common geometric height coordinates |
| [Unfoldings.Geometry.ChainHeightCover](../Unfoldings/Geometry/ChainHeightCover.lean) | Exact height graphs cover actual edge points at every intermediate chain height |
| [Unfoldings.Cap.GeometricTailGraphs](../Unfoldings/Cap/GeometricTailGraphs.lean) | Construct covered exact height graphs for all complete paths of a component |
| [Unfoldings.Geometry.AffineHeightNetwork](../Unfoldings/Geometry/AffineHeightNetwork.lean) | Transport forward-deterministic affine segments into height networks |
| [Unfoldings.Cap.GeometricSectorNetwork](../Unfoldings/Cap/GeometricSectorNetwork.lean) | A common sector network compares branches from distinct geometric components |
| [Unfoldings.Cap.GeometricSectorTails](../Unfoldings/Cap/GeometricSectorTails.lean) | Cover actual parent tails by their common sector network |
| [Unfoldings.Cap.GeometricTailCoalescence](../Unfoldings/Cap/GeometricTailCoalescence.lean) | Construct actual tail graph data and prove permanent merging and sweep order |
| [Unfoldings.Topology.ChildlessAncestors](../Unfoldings/Topology/ChildlessAncestors.lean) | A childless nonroot has no proper descendants |
| [Unfoldings.Cap.GeometricLeafAvoidance](../Unfoldings/Cap/GeometricLeafAvoidance.lean) | A geometric leaf cannot lie on another vertex's parent path |
| [Unfoldings.Cap.GeometricTailLeaves](../Unfoldings/Cap/GeometricTailLeaves.lean) | Separate a distinct leaf from active tail graphs at its insertion height |
| [Unfoldings.Geometry.CoalescingStripInsertion](../Unfoldings/Geometry/CoalescingStripInsertion.lean) | Preserve actual ordered tails when splicing new strip separators |
| [Unfoldings.Geometry.DirectionWedgeOperations](../Unfoldings/Geometry/DirectionWedgeOperations.lean) | Convex positive-span wedges and linear images |
| [Unfoldings.Geometry.RayStrip](../Unfoldings/Geometry/RayStrip.lean) | Monotone ray boundaries enclosing a source sector |
| [Unfoldings.Topology.HeightEnumeration](../Unfoldings/Topology/HeightEnumeration.lean) | Height-ordered finite enumeration with ties |
| [Unfoldings.Geometry.MonotoneStripSubdivision](../Unfoldings/Geometry/MonotoneStripSubdivision.lean) | Finite strip subdivisions, coverage, and disjoint interiors |
| [Unfoldings.Geometry.FiniteWaterfall](../Unfoldings/Geometry/FiniteWaterfall.lean) | Construct height-ordered tail-preserving subdivisions |
| [Unfoldings.Cap.GeometricSectorPositions](../Unfoldings/Cap/GeometricSectorPositions.lean) | Sector bounds for component positions and directions |
| [Unfoldings.Cap.GeometricSectorData](../Unfoldings/Cap/GeometricSectorData.lean) | Chosen actual component sectors and enclosing strips |
| [Unfoldings.Cap.GeometricWaterfall](../Unfoldings/Cap/GeometricWaterfall.lean) | Construct the finite actual sector waterfall |
| [Unfoldings.Cap.GeometricTailEdgeCover](../Unfoldings/Cap/GeometricTailEdgeCover.lean) | Every ancestor-edge point lies on its represented tail |
| [Unfoldings.Cap.GeometricWaterfallAvoidance](../Unfoldings/Cap/GeometricWaterfallAvoidance.lean) | Assigned cuts avoid every waterfall strip interior |
| [Unfoldings.Cap.ProjectedDevelopedMap](../Unfoldings/Cap/ProjectedDevelopedMap.lean) | Construct a continuous actual projected map away from cut seams |
| [Unfoldings.Geometry.MonotoneStripOpenInjective](../Unfoldings/Geometry/MonotoneStripOpenInjective.lean) | Injectivity in positive-width open strip slabs via inset strips |
| [Unfoldings.Cap.CenteredDevelopedMap](../Unfoldings/Cap/CenteredDevelopedMap.lean) | Actual maps and compatible charts in source-centered coordinates |
| [Unfoldings.Cap.RegularStripInjective](../Unfoldings/Cap/RegularStripInjective.lean) | Uniform injectivity for actual regular developed strip maps |
| [Unfoldings.Geometry.FiveSectorInteriors](../Unfoldings/Geometry/FiveSectorInteriors.lean) | Exact sector tests and strict-versus-closed separation |
| [Unfoldings.Geometry.RayStripInterior](../Unfoldings/Geometry/RayStripInterior.lean) | Forward strip interiors are genuine strict ray cones |
| [Unfoldings.Cap.DeepRoofClips](../Unfoldings/Cap/DeepRoofClips.lean) | Choose deep clips containing a whole source sweep slab |
| [Unfoldings.Cap.GeometricWaterfallSectors](../Unfoldings/Cap/GeometricWaterfallSectors.lean) | Exclude cuts from every sector from strip interiors |
| [Unfoldings.Cap.GeometricTailCutoff](../Unfoldings/Cap/GeometricTailCutoff.lean) | Actual tail endpoints continue beyond the deep clip slab |
| [Unfoldings.Cap.DeepGeometricWaterfall](../Unfoldings/Cap/DeepGeometricWaterfall.lean) | Construct waterfall interiors in the regular physical roof |
| [Unfoldings.Cap.ExtendedWaterfallDomains](../Unfoldings/Cap/ExtendedWaterfallDomains.lean) | Regular strip domains in the actual refined roof mesh |
| [Unfoldings.Cap.ExtendedWaterfallInjective](../Unfoldings/Cap/ExtendedWaterfallInjective.lean) | Uniform actual waterfall injectivity on positive-width slabs |
| [Unfoldings.Topology.CyclicIntervals](../Unfoldings/Topology/CyclicIntervals.lean) | Construct oriented cyclic intervals with internal directed prefixes |
| [Unfoldings.Topology.CyclicRegionPairing](../Unfoldings/Topology/CyclicRegionPairing.lean) | Pair separator crossings inside a cyclic contour excursion |
| [Unfoldings.Topology.CyclicSubintervals](../Unfoldings/Topology/CyclicSubintervals.lean) | Construct prefixes and suffixes inside a two-exit cyclic region |
| [Unfoldings.Geometry.BranchingBankOrder](../Unfoldings/Geometry/BranchingBankOrder.lean) | Whole-bank order allowing opposite branch jumps |
| [Unfoldings.Cap.CompletedContourExcursion](../Unfoldings/Cap/CompletedContourExcursion.lean) | Exact developed displacement of a partial sibling excursion |
| [Unfoldings.Cap.CompletedVertexExcursions](../Unfoldings/Cap/CompletedVertexExcursions.lean) | Construct actual contour excursions between branch vertex copies |
| [Unfoldings.Cap.CompletedBranchJumpOrder](../Unfoldings/Cap/CompletedBranchJumpOrder.lean) | Derive signs of actual right and left branching-bank jumps |
| [Unfoldings.Topology.FiniteMonotonePieces](../Unfoldings/Topology/FiniteMonotonePieces.lean) | Preserve coordinate order across finite signed jumps |
| [Unfoldings.Cap.CompletedBankChainOrder](../Unfoldings/Cap/CompletedBankChainOrder.lean) | Whole actual bank chains retain left-or-above order |
| [Unfoldings.Cap.CompletedBankChainContact](../Unfoldings/Cap/CompletedBankChainContact.lean) | Opposite bank-chain interior contact is matched and flat |
| [Unfoldings.Cap.CompletedBankChains](../Unfoldings/Cap/CompletedBankChains.lean) | Construct full parent bank paths in one common sector |
| [Unfoldings.Cap.ExtendedBankChains](../Unfoldings/Cap/ExtendedBankChains.lean) | Derive complete fine-path sectors from original geometry |
| [Unfoldings.Cap.ExtendedBankChainSeparation](../Unfoldings/Cap/ExtendedBankChainSeparation.lean) | Uniform regular noncrossing of complete actual branching banks |
| [Unfoldings.Cap.ProjectedCoherence](../Unfoldings/Cap/ProjectedCoherence.lean) | Continuity at points with coincident developed bank values |
| [Unfoldings.Cap.FlatDescendantCopies](../Unfoldings/Cap/FlatDescendantCopies.lean) | Flat proper descendants create no developed endpoint displacement |
| [Unfoldings.Geometry.SegmentLocalMinimum](../Unfoldings/Geometry/SegmentLocalMinimum.lean) | Local radial minima cannot receive genuine outward segments |
| [Unfoldings.Cap.GeometricLeafMinimum](../Unfoldings/Cap/GeometricLeafMinimum.lean) | Actual geometric leaves are local radial minima |
| [Unfoldings.Cap.RadialLeafCoherence](../Unfoldings/Cap/RadialLeafCoherence.lean) | Derive coherent developed values at local radial minima |
| [Unfoldings.Cap.GeometricLeafInterior](../Unfoldings/Cap/GeometricLeafInterior.lean) | Nonterminal geometric nodes lie strictly inside the roof clip |
| [Unfoldings.Cap.ExtendedLeafCoherence](../Unfoldings/Cap/ExtendedLeafCoherence.lean) | Preserve and prove coherence at every actual geometric leaf |
| [Unfoldings.Cap.ApproachedVertexPinchWidth](../Unfoldings/Cap/ApproachedVertexPinchWidth.lean) | Derive positive width at regular approached bank points, including terminal domains |
| [Unfoldings.Cap.CompletedComparisonStartOrder](../Unfoldings/Cap/CompletedComparisonStartOrder.lean) | Bound complete comparison banks by their actual starting contour copy |
| [Unfoldings.Cap.CompletedProperComparisonData](../Unfoldings/Cap/CompletedProperComparisonData.lean) | Construct proper comparison data in a specified sector |
| [Unfoldings.Cap.EmptyStripLateCircleSeparation](../Unfoldings/Cap/EmptyStripLateCircleSeparation.lean) | Separate surviving circle slices beyond an intervening terminal strip |
| [Unfoldings.Cap.GeometricComponentBanks](../Unfoldings/Cap/GeometricComponentBanks.lean) | Retain one specified component sector along actual completed parent banks |
| [Unfoldings.Cap.GeometricTailPieces](../Unfoldings/Cap/GeometricTailPieces.lean) | Locate arbitrary actual tail points on labeled geometric parent edges |
| [Unfoldings.Cap.GeometricTailTraceOrder](../Unfoldings/Cap/GeometricTailTraceOrder.lean) | Prove both developed coordinates progress along actual visible cut tails |
| [Unfoldings.Cap.MatchedStripBankOrder](../Unfoldings/Cap/MatchedStripBankOrder.lean) | Transfer matched actual parent-bank coordinate order to adjacent strip traces |
| [Unfoldings.Cap.SameSectorEmptyCircleComparison](../Unfoldings/Cap/SameSectorEmptyCircleComparison.lean) | Continue the actual terminal contour copy in its geometric tail sector |
| [Unfoldings.Cap.TailHeightBankGeometry](../Unfoldings/Cap/TailHeightBankGeometry.lean) | Derive actual completed bank geometry from an intermediate tail height |
| [Unfoldings.Geometry.HeightGraphAffineOrder](../Unfoldings/Geometry/HeightGraphAffineOrder.lean) | Preserve affine coordinate order through continuous finite chart selection on a chain |
| [Unfoldings.Cap.EarlyTerminalBankOrder](../Unfoldings/Cap/EarlyTerminalBankOrder.lean) | Bound early surviving circle crossings by the actual intermediate terminal copy |
| [Unfoldings.Geometry.CircleInnerCornerOrder](../Unfoldings/Geometry/CircleInnerCornerOrder.lean) | Order circle endpoints separated by a corner strictly inside the circle |
| [Unfoldings.Cap.LateTerminalBankOrder](../Unfoldings/Cap/LateTerminalBankOrder.lean) | Bound late surviving circle crossings beyond the actual intermediate terminal copy |
| [Unfoldings.Cap.TerminalHeightLeafOrder](../Unfoldings/Cap/TerminalHeightLeafOrder.lean) | A permanent terminal height follows every actual leaf completed by either bank |
| [Unfoldings.Cap.SharedSeparatorPrefixValue](../Unfoldings/Cap/SharedSeparatorPrefixValue.lean) | Agree actual approached separator prefix values using independently witnessed active heights |
| [Unfoldings.Geometry.StripSlabApproach](../Unfoldings/Geometry/StripSlabApproach.lean) | Localize approached banks to open height slabs and extract later active strip points |
| [Unfoldings.Cap.EmptyNeighborCirclePrefix](../Unfoldings/Cap/EmptyNeighborCirclePrefix.lean) | Derive surviving circle crossings lie beyond the actual shared leaves of an empty neighbor |
| [Unfoldings.Geometry.CircleTerminalOrder](../Unfoldings/Geometry/CircleTerminalOrder.lean) | Combine all early and late height cases into first-quadrant circle order |
| [Unfoldings.Cap.EmptyStripCircleSeparation](../Unfoldings/Cap/EmptyStripCircleSeparation.lean) | Separate actual surviving circle slices across one disappearing strip in all height cases |
| [Unfoldings.Cap.ExtendedOneEmptyCircleGeometry](../Unfoldings/Cap/ExtendedOneEmptyCircleGeometry.lean) | Uniformly separate survivors across one disappearing strip in the same actual roof trace family |
| [Unfoldings.Geometry.SubdivisionCellChain](../Unfoldings/Geometry/SubdivisionCellChain.lean) | Retain the ordered chain of actual subdivision cell walls, including zero-width cells |
| [Unfoldings.Geometry.StripBankChain](../Unfoldings/Geometry/StripBankChain.lean) | Identify all physical banks in a finite chain of permanently collapsed strips |
| [Unfoldings.Cap.EmptyStripChainLateCircleSeparation](../Unfoldings/Cap/EmptyStripChainLateCircleSeparation.lean) | Separate surviving circle slices beyond an arbitrary chain of collapsed intermediate strips |
| [Unfoldings.Cap.PositiveWidthBankStartOrder](../Unfoldings/Cap/PositiveWidthBankStartOrder.lean) | Bound actual regular positive-width bank traces by a named starting copy without a circle condition |
| [Unfoldings.Cap.FramedVertexHeights](../Unfoldings/Cap/FramedVertexHeights.lean) | Exclude all actual physical mesh vertices using one finite set of sweep heights |
| [Unfoldings.Cap.ClosedBankStartOrder](../Unfoldings/Cap/ClosedBankStartOrder.lean) | Extend actual bank progress from a named copy through every branch vertex and interval endpoint |
| [Unfoldings.Geometry.FiniteAffineSegmentOrder](../Unfoldings/Geometry/FiniteAffineSegmentOrder.lean) | Preserve a linear coordinate along a continuous finite affine selection on a segment |
| [Unfoldings.Geometry.NearIdentityHeightOrder](../Unfoldings/Geometry/NearIdentityHeightOrder.lean) | Preserve individual right/down coordinates at equal sweep height under near-identity linear maps |
| [Unfoldings.Cap.RadialStripLevelOrder](../Unfoldings/Cap/RadialStripLevelOrder.lean) | Retain individual actual developed coordinate order across a closed physical strip level |
| [Unfoldings.Cap.GeometricSectorCutPoint](../Unfoldings/Cap/GeometricSectorCutPoint.lean) | Locate every strict-sector physical cut point on an actual leaf tail in that sector |
| [Unfoldings.Cap.GeometricLevelBankOrder](../Unfoldings/Cap/GeometricLevelBankOrder.lean) | Derive actual regular facing-bank coordinate order across any physically coincident cell walls |
| [Unfoldings.Topology.ChainIdentityContraction](../Unfoldings/Topology/ChainIdentityContraction.lean) | Contract removed identity pieces in finite endpoint-matched chains |
| [Unfoldings.Topology.OrderedBankPieces](../Unfoldings/Topology/OrderedBankPieces.lean) | Compose consecutive endpoint inequalities into pairwise order of finite bank pieces |
| [Unfoldings.Geometry.SubdivisionActiveCells](../Unfoldings/Geometry/SubdivisionActiveCells.lean) | Preserve exact physical bank contacts after arbitrarily many collapsed subdivision cells are skipped |
| [Unfoldings.Cap.WaterfallLevelBankOrder](../Unfoldings/Cap/WaterfallLevelBankOrder.lean) | Order all surviving actual bank intervals at each regular physical sweep height across arbitrary collapsed-cell runs |
| [Unfoldings.Cap.RadialStripClosedBanks](../Unfoldings/Cap/RadialStripClosedBanks.lean) | Track both actual approached banks at every height before an approached endpoint |
| [Unfoldings.Cap.WaterfallClosedLevelBankOrder](../Unfoldings/Cap/WaterfallClosedLevelBankOrder.lean) | Compare ordered actual approached banks through every physical sweep height, including terminal vertices |
| [Unfoldings.Topology.FiniteRecordProgress](../Unfoldings/Topology/FiniteRecordProgress.lean) | Propagate progress at successive strict records to a first finite maximum |
| [Unfoldings.Cap.TerminalBankIntervalOrder](../Unfoldings/Cap/TerminalBankIntervalOrder.lean) | Derive actual coordinate progress on an approached bank following an earlier terminal tail |
| [Unfoldings.Cap.TerminalRecordStep](../Unfoldings/Cap/TerminalRecordStep.lean) | Propagate actual terminal-copy coordinates to a later terminal along a shared physical tail |
| [Unfoldings.Cap.TerminalRunRecords](../Unfoldings/Cap/TerminalRunRecords.lean) | Propagate actual terminal coordinates through arbitrary finite records of disappearing strips |
| [Unfoldings.Cap.EarlyCircleTerminalPrefix](../Unfoldings/Cap/EarlyCircleTerminalPrefix.lean) | Bound early surviving circle crossings after arbitrary terminated prefixes and before terminated suffixes |
| [Unfoldings.Topology.FiniteMaxPositions](../Unfoldings/Topology/FiniteMaxPositions.lean) | Locate first and last finite maxima and threshold crossings with strict bounds outside them |
| [Unfoldings.Cap.TerminalRunLateBounds](../Unfoldings/Cap/TerminalRunLateBounds.lean) | Bound late surviving circle crossings by one actual terminal copy across a finite collapsed run |
| [Unfoldings.Cap.TerminalRunEarlyBounds](../Unfoldings/Cap/TerminalRunEarlyBounds.lean) | Bound early surviving circle crossings by extreme actual terminal maxima across arbitrary disappearing runs |
| [Unfoldings.Cap.EmptyStripRunCircleSeparation](../Unfoldings/Cap/EmptyStripRunCircleSeparation.lean) | Separate actual surviving circle slices across any finite run of disappearing nonempty strips |
| [Unfoldings.Geometry.EmptyStripBanks](../Unfoldings/Geometry/EmptyStripBanks.lean) | Identify both physical banks on a closed slab when its open strip is wholly empty |
| [Unfoldings.Geometry.StripBankContacts](../Unfoldings/Geometry/StripBankContacts.lean) | Derive finite bank-chain identities from contacts only at the tested height |
| [Unfoldings.Geometry.SubdivisionNonemptyCells](../Unfoldings/Geometry/SubdivisionNonemptyCells.lean) | Remove wholly empty physical cells while retaining exact bank contacts on the controlled slab |
| [Unfoldings.Cap.TerminalRunRecordsContacts](../Unfoldings/Cap/TerminalRunRecordsContacts.lean) | Retain actual terminal bounds with bank contacts restricted to the controlled physical slab |
| [Unfoldings.Cap.EarlyCircleTerminalPrefixContacts](../Unfoldings/Cap/EarlyCircleTerminalPrefixContacts.lean) | Retain actual terminal bounds with bank contacts restricted to the controlled physical slab |
| [Unfoldings.Cap.TerminalRunLateBoundsContacts](../Unfoldings/Cap/TerminalRunLateBoundsContacts.lean) | Retain actual terminal bounds with bank contacts restricted to the controlled physical slab |
| [Unfoldings.Cap.ContactSeparatorPrefix](../Unfoldings/Cap/ContactSeparatorPrefix.lean) | Prove coherent separator prefixes and terminal-height bounds from physical bank contact |
| [Unfoldings.Cap.ContactTraceValues](../Unfoldings/Cap/ContactTraceValues.lean) | Identify actual approached trace values at a coherent physical contact |
| [Unfoldings.Geometry.SubdivisionBankContact](../Unfoldings/Geometry/SubdivisionBankContact.lean) | Locate positive bank contacts in the root interior and identify their separators |
| [Unfoldings.Cap.EmptyNeighborContactPrefix](../Unfoldings/Cap/EmptyNeighborContactPrefix.lean) | Exclude early circle crossings on coherent prefixes using only physical bank contact |
| [Unfoldings.Cap.TerminalRunEarlyBoundsContacts](../Unfoldings/Cap/TerminalRunEarlyBoundsContacts.lean) | Propagate early actual circle bounds across terminal runs with only slab-restricted bank contact |
| [Unfoldings.Cap.EmptyStripChainLateContactSeparation](../Unfoldings/Cap/EmptyStripChainLateContactSeparation.lean) | Separate late actual circle slices across chains joined only inside the controlled slab |
| [Unfoldings.Cap.EmptyStripRunContactSeparation](../Unfoldings/Cap/EmptyStripRunContactSeparation.lean) | Separate actual circle slices across arbitrary terminal runs with slab-restricted contacts |
| [Unfoldings.Cap.ContactSeparatorValues](../Unfoldings/Cap/ContactSeparatorValues.lean) | Identify actual prefix values across physical bank contacts, including recoverable pinches |
| [Unfoldings.Geometry.TailContact](../Unfoldings/Geometry/TailContact.lean) | Transfer completion of an actual tail across slab-restricted bank contact |
| [Unfoldings.Cap.ContactSeparatorCirclePrefix](../Unfoldings/Cap/ContactSeparatorCirclePrefix.lean) | Identify circle endpoints on coherent separator prefixes after physically empty cells are removed |
| [Unfoldings.Cap.LeafTailCircleOrder](../Unfoldings/Cap/LeafTailCircleOrder.lean) | Order actual circle endpoints on opposite banks of one completed leaf tail |
| [Unfoldings.Cap.ContactSeparatorCircleOrder](../Unfoldings/Cap/ContactSeparatorCircleOrder.lean) | Order actual surviving circle endpoints after physically empty cells between their banks are removed |
| [Unfoldings.Topology.FilterRunChain](../Unfoldings/Topology/FilterRunChain.lean) | Assemble order of consecutive survivors from every finite removed run, and retain ordered list occurrences |
| [Unfoldings.Topology.IndexedRun](../Unfoldings/Topology/IndexedRun.lean) | Extract exact contacts, ordered occurrences, and both endpoint contacts from a finite list run |
| [Unfoldings.Cap.WaterfallCircleRunOrder](../Unfoldings/Cap/WaterfallCircleRunOrder.lean) | Order actual circle banks across every removed subdivision run, including the empty run |
| [Unfoldings.Cap.WaterfallCircleSurvivors](../Unfoldings/Cap/WaterfallCircleSurvivors.lean) | Prove pairwise disjointness of every surviving actual strip-circle image in one waterfall sector |
| [Unfoldings.Topology.FilterDisjoint](../Unfoldings/Topology/FilterDisjoint.lean) | Restore empty set entries after pairwise separation of a filtered list is proved |
| [Unfoldings.Cap.ExtendedSectorCircleGeometry](../Unfoldings/Cap/ExtendedSectorCircleGeometry.lean) | Derive uniform within-sector separation for all actual waterfall strip-circle images, quantified before both meshes |
| [Unfoldings.Cap.SectorBoundaryCutPoints](../Unfoldings/Cap/SectorBoundaryCutPoints.lean) | Classify actual sector-boundary cuts as radial skirt pieces or geometric leaf endpoints |
| [Unfoldings.Cap.CoherentPhysicalTraceContact](../Unfoldings/Cap/CoherentPhysicalTraceContact.lean) | Identify coherent approached values across different sector frames in one actual developed plane |
| [Unfoldings.Geometry.RadialTailPositions](../Unfoldings/Geometry/RadialTailPositions.lean) | Identify any two radial-tail positions by a positive source-centered scaling |
| [Unfoldings.Cap.SectorBoundaryComponents](../Unfoldings/Cap/SectorBoundaryComponents.lean) | Exclude attached original trees on sector-boundary components and allow both neighboring sector frames |
| [Unfoldings.Cap.SectorBoundaryBankGeometry](../Unfoldings/Cap/SectorBoundaryBankGeometry.lean) | Derive actual boundary-path direction and curved-descendant control in either neighboring sector |
| [Unfoldings.Cap.CirclePhysicalBankMatching](../Unfoldings/Cap/CirclePhysicalBankMatching.lean) | Match circle endpoints from any sector with their named actual parent-bank points in the developed plane |
| [Unfoldings.Cap.CrossFrameCircleBankOrder](../Unfoldings/Cap/CrossFrameCircleBankOrder.lean) | Order named actual circle-bank endpoints from different sector frames in one common comparison frame |
| [Unfoldings.Cap.CrossFrameTraceQuadrants](../Unfoldings/Cap/CrossFrameTraceQuadrants.lean) | Transfer actual face margins to approached traces in any comparison frame and control every sweep height |
| [Unfoldings.Cap.SectorBoundaryCircleBankOrder](../Unfoldings/Cap/SectorBoundaryCircleBankOrder.lean) | Derive cross-sector circle-bank order along actual radial boundary cuts from physical geometry and uniform face margins |
| [Unfoldings.Topology.ChainFilterEndpoints](../Unfoldings/Topology/ChainFilterEndpoints.lean) | Preserve first and last physical endpoints when identity pieces are removed from a chain |
| [Unfoldings.Geometry.SubdivisionNonemptyEndpoints](../Unfoldings/Geometry/SubdivisionNonemptyEndpoints.lean) | Retain both enclosing-strip boundary contacts after empty physical endpoint cells are removed |
| [Unfoldings.Geometry.QuadrantArgumentOrder](../Unfoldings/Geometry/QuadrantArgumentOrder.lean) | Convert equal-radius coordinate order and smaller-radius terminal barriers into exact argument inequalities |
| [Unfoldings.Geometry.QuadrantCircleOrderTransport](../Unfoldings/Geometry/QuadrantCircleOrderTransport.lean) | Preserve actual circle endpoint order between overlapping oriented quadrant frames |
| [Unfoldings.Cap.BoundaryRunTerminalPoint](../Unfoldings/Cap/BoundaryRunTerminalPoint.lean) | Place the actual highest terminal of an extreme disappearing run on its enclosing sector boundary |
| [Unfoldings.Cap.BoundaryTerminalComponent](../Unfoldings/Cap/BoundaryTerminalComponent.lean) | Place actual boundary-terminal vertices on pure radial components, including terminal leaf-height contact |
| [Unfoldings.Geometry.RayStripBankOrder](../Unfoldings/Geometry/RayStripBankOrder.lean) | Identify the named first and last ray banks of an oriented quadrant strip |
| [Unfoldings.Geometry.RadialTailComponentRays](../Unfoldings/Geometry/RadialTailComponentRays.lean) | Identify clipped radial components from positive source-centered collinearity at different positions |
| [Unfoldings.Cap.SectorBankRays](../Unfoldings/Cap/SectorBankRays.lean) | Identify named boundary rays and the same actual radial component from neighboring sector frames |
| [Unfoldings.Cap.AdjacentBoundaryRunComponents](../Unfoldings/Cap/AdjacentBoundaryRunComponents.lean) | Identify the same actual radial component for extreme disappearing runs in neighboring sectors |
| [Unfoldings.Cap.ClosedParentBankMatching](../Unfoldings/Cap/ClosedParentBankMatching.lean) | Extend named actual parent-bank chart matching through closed fine-vertex and terminal endpoints |
| [Unfoldings.Cap.RadialComponentFinePath](../Unfoldings/Cap/RadialComponentFinePath.lean) | Track every radial-component position on actual completed fine parent paths ending at the genuine outer tip |
| [Unfoldings.Geometry.FiveSectorCycle](../Unfoldings/Geometry/FiveSectorCycle.lean) | Give the actual five-sector cyclic ray order and prove their acute angles make exactly one full turn |
| [Unfoldings.Geometry.AcuteWedgeMarginAngle](../Unfoldings/Geometry/AcuteWedgeMarginAngle.lean) | Identify the exact angular slack represented by an acute wedge frame margin |
| [Unfoldings.Geometry.FiveSectorFrameMargins](../Unfoldings/Geometry/FiveSectorFrameMargins.lean) | Compute exact five-sector quadrant offsets, their cyclic increment, and their total margin |
| [Unfoldings.Geometry.OrientedFramePhase](../Unfoldings/Geometry/OrientedFramePhase.lean) | Recover an oriented frame rotation from one named ray and separate rotated quadrants |
| [Unfoldings.Geometry.FiveSectorFrameRotation](../Unfoldings/Geometry/FiveSectorFrameRotation.lean) | Recover exact five-sector frame rotations and separate nonadjacent comparison quadrants |
| [Unfoldings.Cap.NonadjacentSectorSeparation](../Unfoldings/Cap/NonadjacentSectorSeparation.lean) | Separate actual developed strip and circle images in every nonadjacent pair of sectors |
| [Unfoldings.Cap.BoundaryRunApproachedBanks](../Unfoldings/Cap/BoundaryRunApproachedBanks.lean) | Approach extreme maximal terminals along the actual enclosing bank from below |
| [Unfoldings.Cap.EnclosingBankSegments](../Unfoldings/Cap/EnclosingBankSegments.lean) | Track enclosing-ray bank positions on actual segments between controlled heights |
| [Unfoldings.Cap.RadialComponentFineAncestry](../Unfoldings/Cap/RadialComponentFineAncestry.lean) | Derive actual fine-forest ancestry from physical order on an unattached radial component |
| [Unfoldings.Cap.BoundaryRunIncomingBankMatching](../Unfoldings/Cap/BoundaryRunIncomingBankMatching.lean) | Identify extreme terminal copies with actual incoming fine parent-bank endpoints |
| [Unfoldings.Cap.RadialComponentIncomingBank](../Unfoldings/Cap/RadialComponentIncomingBank.lean) | Construct the actual incoming fine edge and its positive physical boundary-bank height |
| [Unfoldings.Geometry.OrientedInnerBarriers](../Unfoldings/Geometry/OrientedInnerBarriers.lean) | Separate outward arcs using one actual inner point in different oriented quadrant frames |
| [Unfoldings.Cap.CrossFrameInnerTerminalSeparation](../Unfoldings/Cap/CrossFrameInnerTerminalSeparation.lean) | Derive cross-frame separation for inner terminals and circle crossings from actual bank-chain progress |
| [Unfoldings.Cap.StripCirclePointBounds](../Unfoldings/Cap/StripCirclePointBounds.lean) | Bound every open strip-circle point strictly by its actual approached bank endpoints |
| [Unfoldings.Cap.CrossFrameStripCircleBounds](../Unfoldings/Cap/CrossFrameStripCircleBounds.lean) | Apply actual cross-frame bank barriers to constructed waterfall circle images with strict open-arc bounds |
| [Unfoldings.Geometry.RadialTailHeightOrder](../Unfoldings/Geometry/RadialTailHeightOrder.lean) | Put every nontip radial-component position strictly below its outer tip in any increasing linear height |
| [Unfoldings.Cap.RadialComponentCommonChain](../Unfoldings/Cap/RadialComponentCommonChain.lean) | Derive one actual fine parent chain and both sector geometries for edges on a shared radial component |
| [Unfoldings.Cap.BoundaryTerminalMargins](../Unfoldings/Cap/BoundaryTerminalMargins.lean) | Derive actual terminal-copy radius bounds and strict margins in either neighboring frame |
| [Unfoldings.Cap.TerminalRunEarlyMaximaContacts](../Unfoldings/Cap/TerminalRunEarlyMaximaContacts.lean) | Bound early circle crossings by any maximal terminal while retaining ordered tied contour copies |
| [Unfoldings.Cap.BoundaryTerminalSectorAssignment](../Unfoldings/Cap/BoundaryTerminalSectorAssignment.lean) | Retain the unique actual component-sector assignment of boundary-run terminals |
| [Unfoldings.Cap.NoAdjacentBoundaryRuns](../Unfoldings/Cap/NoAdjacentBoundaryRuns.lean) | Exclude disappearing physical boundary runs on both sides of a shared sector ray using actual component assignments |
| [Unfoldings.Cap.RadialComponentSeed](../Unfoldings/Cap/RadialComponentSeed.lean) | Identify the unique nonroot geometric position of a pure radial component and its coherent fine seed vertex |
| [Unfoldings.Cap.BoundaryTerminalSeedAncestor](../Unfoldings/Cap/BoundaryTerminalSeedAncestor.lean) | Reach actual boundary terminals from coherent fine seed vertices and derive their incoming boundary banks |
| [Unfoldings.Cap.CoherentEmptyCircleExclusion](../Unfoldings/Cap/CoherentEmptyCircleExclusion.lean) | Exclude coherent contacts between approached empty-strip points and another sector frame source circle |
| [Unfoldings.Cap.BoundaryRunClosedPrefix](../Unfoldings/Cap/BoundaryRunClosedPrefix.lean) | Cover every boundary-prefix position by an actual approached disappearing-strip bank |
| [Unfoldings.Cap.BoundaryRunCirclePrefix](../Unfoldings/Cap/BoundaryRunCirclePrefix.lean) | Put neighboring coherent circle crossings strictly beyond actual boundary-run terminals |
| [Unfoldings.Cap.BoundaryRunCircleComponent](../Unfoldings/Cap/BoundaryRunCircleComponent.lean) | Put every neighboring boundary-circle crossing on the same actual radial component as the run terminal |
| [Unfoldings.Cap.SharedSectorBankCoordinates](../Unfoldings/Cap/SharedSectorBankCoordinates.lean) | Convert positive heights on a shared physical sector bank exactly between neighboring frames |
| [Unfoldings.Cap.RadialComponentSeedPath](../Unfoldings/Cap/RadialComponentSeedPath.lean) | Cover every nontip radial-component position by the actual fine path from its seed |
| [Unfoldings.Cap.RadialStripCirclePhysicalBounds](../Unfoldings/Cap/RadialStripCirclePhysicalBounds.lean) | Bound approached source-circle points by an explicit physical source ball |
| [Unfoldings.Cap.RadialComponentCircleBanks](../Unfoldings/Cap/RadialComponentCircleBanks.lean) | Match actual circle endpoints on radial components to named fine parent banks with exact radii |
| [Unfoldings.Cap.CoherentParentBankPoints](../Unfoldings/Cap/CoherentParentBankPoints.lean) | Identify both actual named parent-bank values at coherent physical points, including child vertices |
| [Unfoldings.Cap.BoundaryRunTerminalBankCandidate](../Unfoldings/Cap/BoundaryRunTerminalBankCandidate.lean) | Derive actual inner fine-bank candidates for extreme boundary terminals, including coherent terminal vertices |
| [Unfoldings.Cap.CrossFrameCircleStrictMargins](../Unfoldings/Cap/CrossFrameCircleStrictMargins.lean) | Derive strict comparison quadrants for approached source-circle points from uniform physical face margins |
| [Unfoldings.Cap.ComponentBankCircleSeparation](../Unfoldings/Cap/ComponentBankCircleSeparation.lean) | Separate actual strip-circle images from component geometry and each strip own named bank bounds |
| [Unfoldings.Cap.BoundaryRunNeighborCircleCandidate](../Unfoldings/Cap/BoundaryRunNeighborCircleCandidate.lean) | Derive a neighboring surviving boundary-circle candidate from actual run geometry and physical bank contacts |
| [Unfoldings.Cap.BoundaryRunLateCircleCandidate](../Unfoldings/Cap/BoundaryRunLateCircleCandidate.lean) | Derive exact run-side circle-bank candidates after maximal terminals from actual collapsed bank chains |
| [Unfoldings.Cap.BoundaryRunSourceBankCandidate](../Unfoldings/Cap/BoundaryRunSourceBankCandidate.lean) | Bound every early or late run-side crossing by an actual named bank candidate and retain its approached trace origin |
| [Unfoldings.Cap.SharedBoundaryTraceMargins](../Unfoldings/Cap/SharedBoundaryTraceMargins.lean) | Derive both sector cones and strict comparison margins for actual approached copies on a shared physical bank |
| [Unfoldings.Cap.SharedBoundaryBankMargins](../Unfoldings/Cap/SharedBoundaryBankMargins.lean) | Derive both comparison margins for actual shared-ray terminals and circle endpoints |
| [Unfoldings.Cap.BoundaryRunSharedMargins](../Unfoldings/Cap/BoundaryRunSharedMargins.lean) | Obtain both neighboring comparison margins from actual terminal or late-circle candidate origins |
| [Unfoldings.Cap.BoundaryRunCircleSeparation](../Unfoldings/Cap/BoundaryRunCircleSeparation.lean) | Separate actual neighboring circle images across an upper or lower disappearing boundary run, deriving candidates and comparison margins |
| [Unfoldings.Cap.BoundaryComponentFineSeed](../Unfoldings/Cap/BoundaryComponentFineSeed.lean) | Construct a coherent represented fine seed for any sector-boundary component inside the clip |
| [Unfoldings.Cap.CrossFrameCircleCoherence](../Unfoldings/Cap/CrossFrameCircleCoherence.lean) | Identify actual circle endpoints at coherent earlier physical contacts across different sector frames |
| [Unfoldings.Geometry.RadialTailHeightMembership](../Unfoldings/Geometry/RadialTailHeightMembership.lean) | Keep later collinear positions on a radial tail until its tip height |
| [Unfoldings.Cap.SectorRadialTailHeight](../Unfoldings/Cap/SectorRadialTailHeight.lean) | Put actual radial-component tips beyond a controlled interior sweep height |
| [Unfoldings.Cap.SharedEndpointCircleSeparation](../Unfoldings/Cap/SharedEndpointCircleSeparation.lean) | Separate actual open strip-circle images at a shared developed endpoint |
| [Unfoldings.Cap.BoundaryCircleContactAlternative](../Unfoldings/Cap/BoundaryCircleContactAlternative.lean) | Classify ordered shared-ray circle contacts as equal values or a common actual radial component |
| [Unfoldings.Cap.SharedSectorBankPointOrder](../Unfoldings/Cap/SharedSectorBankPointOrder.lean) | Order shared physical bank points exactly across their different sector height scales |
| [Unfoldings.Cap.OuterCircleContactAlternative](../Unfoldings/Cap/OuterCircleContactAlternative.lean) | Classify surviving outer circle endpoints without assuming their shared physical ray is uncut |
| [Unfoldings.Cap.OuterCircleSeparation](../Unfoldings/Cap/OuterCircleSeparation.lean) | Separate actual adjacent outer circle images with coherent contacts or genuine radial cuts |
| [Unfoldings.Cap.WaterfallCircleSurvivorOrder](../Unfoldings/Cap/WaterfallCircleSurvivorOrder.lean) | Retain the full actual bank-endpoint order of every surviving source-circle interval |
| [Unfoldings.Geometry.CircleCoordinateCaps](../Unfoldings/Geometry/CircleCoordinateCaps.lean) | Describe and compare circle portions bounded by one bank coordinate |
| [Unfoldings.Cap.StripCircleCoordinateCaps](../Unfoldings/Cap/StripCircleCoordinateCaps.lean) | Place actual circle images inside their own bank-coordinate portions and separate them at common points |
| [Unfoldings.Cap.ComponentBankCircleCaps](../Unfoldings/Cap/ComponentBankCircleCaps.lean) | Separate entire coordinate-bounded circle portions using actual component-bank comparisons |
| [Unfoldings.Cap.BoundaryRunCircleCaps](../Unfoldings/Cap/BoundaryRunCircleCaps.lean) | Separate whole circle portions across either actual disappearing boundary run |
| [Unfoldings.Cap.OuterCircleCaps](../Unfoldings/Cap/OuterCircleCaps.lean) | Separate whole circle portions at actual adjacent outer banks, allowing shared-ray cuts |
| [Unfoldings.Geometry.SubdivisionCollapsedBanks](../Unfoldings/Geometry/SubdivisionCollapsedBanks.lean) | Transfer simultaneous cell-bank collapse to the enclosing subdivision banks |
| [Unfoldings.Topology.OrderedBankEndpoints](../Unfoldings/Topology/OrderedBankEndpoints.lean) | Bound every ordered interval by the first and last retained bank pieces |
| [Unfoldings.Cap.WaterfallCircleNonempty](../Unfoldings/Cap/WaterfallCircleNonempty.lean) | Prove that every controlled sector circle has an actual surviving waterfall strip |
| [Unfoldings.Topology.FilterBoundaryRuns](../Unfoldings/Topology/FilterBoundaryRuns.lean) | Retain the actual removed prefix and suffix at the first and last filtered survivors |
| [Unfoldings.Topology.IndexedBoundaryRun](../Unfoldings/Topology/IndexedBoundaryRun.lean) | Index actual initial and final removed runs with their occurrence order and facing contacts |
| [Unfoldings.Geometry.SubdivisionNonemptyBoundary](../Unfoldings/Geometry/SubdivisionNonemptyBoundary.lean) | Retain either enclosing-bank contact at an extreme physically nonempty cell |
| [Unfoldings.Geometry.SubdivisionBoundaryRun](../Unfoldings/Geometry/SubdivisionBoundaryRun.lean) | Derive a direct enclosing-bank contact or an actual indexed removed boundary run from filtered extremes |
| [Unfoldings.Cap.BoundaryRunCircleConstruction](../Unfoldings/Cap/BoundaryRunCircleConstruction.lean) | Construct extreme maximal terminals and actual circle barriers from indexed boundary-run data |
| [Unfoldings.Cap.AdjacentSurvivorCircleCaps](../Unfoldings/Cap/AdjacentSurvivorCircleCaps.lean) | Derive adjacent extreme-survivor separation from actual filtered subdivisions and rule out two boundary runs |
| [Unfoldings.Cap.WaterfallCircleSurvivorBanks](../Unfoldings/Cap/WaterfallCircleSurvivorBanks.lean) | Retain both actual bank coordinates in the full survivor endpoint order |
| [Unfoldings.Cap.WaterfallCircleExtremeBounds](../Unfoldings/Cap/WaterfallCircleExtremeBounds.lean) | Bound every actual sector circle image by its extreme surviving bank coordinates |
| [Unfoldings.Cap.AdjacentSectorCircleSeparation](../Unfoldings/Cap/AdjacentSectorCircleSeparation.lean) | Separate every actual strip-circle pair in adjacent sectors including non-extreme and empty cells |
| [Unfoldings.Cap.AllSectorCircleSeparation](../Unfoldings/Cap/AllSectorCircleSeparation.lean) | Separate all actual strip-circle images across the complete five-sector waterfall |
| [Unfoldings.Cap.WaterfallMapDistance](../Unfoldings/Cap/WaterfallMapDistance.lean) | Transfer uniform containing-face distance estimates to the actual selected projected development map |
| [Unfoldings.Cap.UniformExtendedFaceSeparation](../Unfoldings/Cap/UniformExtendedFaceSeparation.lean) | Choose a positive tilt threshold before both meshes and separate actual roof-face interiors in a controlled source ball |
| [Unfoldings.Development.NonoverlapNormalization](../Unfoldings/Development/NonoverlapNormalization.lean) | Preserve actual face-interior nonoverlap under global rigid motion, root normalization, and development uniqueness |
| [Unfoldings.Development.RefinementNonoverlap](../Unfoldings/Development/RefinementNonoverlap.lean) | Transfer nonoverlap from any actual development of a connected conforming refinement to a coarse development |
| [Unfoldings.Complex.FaceRestriction](../Unfoldings/Complex/FaceRestriction.lean) | Restrict whole triangle-complex faces and inherit exactly the seams between retained faces |
| [Unfoldings.Development.FaceRestriction](../Unfoldings/Development/FaceRestriction.lean) | Restrict actual facewise developments and preserve face-interior nonoverlap |
| [Unfoldings.Geometry.ConstrainedTriangleCover](../Unfoldings/Geometry/ConstrainedTriangleCover.lean) | Cover a coarse triangle by contained cells from a finite line-aligned geometric cover |
| [Unfoldings.Cap.ClipOriginalCoordinates](../Unfoldings/Cap/ClipOriginalCoordinates.lean) | Construct actual rigid embeddings of contained roof triangles into their original face coordinates |
| [Unfoldings.Cap.ClipOriginalPieces](../Unfoldings/Cap/ClipOriginalPieces.lean) | Cover every closed original face by actual contained roof triangles with unique original parents |
| [Unfoldings.Cap.ClipOriginalSubdivision](../Unfoldings/Cap/ClipOriginalSubdivision.lean) | Construct the actual original-face subcomplex and its isometric subdivision of the original input complex |
| [Unfoldings.Geometry.SharedEdgeInterior](../Unfoldings/Geometry/SharedEdgeInterior.lean) | Put every shared nonvertex edge point inside a region containing both opposite triangles |
| [Unfoldings.Cap.ClipOriginalRetention](../Unfoldings/Cap/ClipOriginalRetention.lean) | Retain every actual fine seam whose two triangles have the same original parent |
| [Unfoldings.Cap.ClipOriginalCopies](../Unfoldings/Cap/ClipOriginalCopies.lean) | Identify all retained fine copies of each point within one original input face, including vertices |
| [Unfoldings.Cap.ProjectedSeamCompletion](../Unfoldings/Cap/ProjectedSeamCompletion.lean) | Recover actual original seams from whole shared projected edges |
| [Unfoldings.Cap.ProjectedPointCopies](../Unfoldings/Cap/ProjectedPointCopies.lean) | Compare intrinsic projected face copies across retained original seams |
| [Unfoldings.Cap.ClipOriginalAdjacency](../Unfoldings/Cap/ClipOriginalAdjacency.lean) | Classify fine seams between distinct original parents by their common whole original edge |
| [Unfoldings.Cap.ClipOriginalRespects](../Unfoldings/Cap/ClipOriginalRespects.lean) | Map every retained fine seam to an actual retained original seam chain |
| [Unfoldings.Cap.ClipOriginalFaceMap](../Unfoldings/Cap/ClipOriginalFaceMap.lean) | Map each whole original face continuously into its retained fine subdivision |
| [Unfoldings.Complex.FaceRestrictionClasses](../Unfoldings/Complex/FaceRestrictionClasses.lean) | Preserve retained nonvertex point identifications under whole-face restriction |
| [Unfoldings.Cap.ClipRetainedClasses](../Unfoldings/Cap/ClipRetainedClasses.lean) | Keep all actual roof point identifications away from the physical cut set |
| [Unfoldings.Cap.ClipOriginalRegularCopies](../Unfoldings/Cap/ClipOriginalRegularCopies.lean) | Identify regular fine copies across original parents away from original cuts |
| [Unfoldings.Cap.ClipOriginalSeamMap](../Unfoldings/Cap/ClipOriginalSeamMap.lean) | Identify entire retained original seams in the fine realization, including endpoints |
| [Unfoldings.Cap.ClipOriginalConforming](../Unfoldings/Cap/ClipOriginalConforming.lean) | Prove exact retained-seam conformity and intrinsic metric equivalence for the actual original-face subdivision |
| [Unfoldings.Cap.ClipOriginalNonoverlap](../Unfoldings/Cap/ClipOriginalNonoverlap.lean) | Transfer nonoverlap from any actual fine development to the connected original cut cap |
| [Unfoldings.Geometry.SharedEdgeCutSet](../Unfoldings/Geometry/SharedEdgeCutSet.lean) | Show that exterior skirt cuts cannot add a whole shared edge inside the original region |
| [Unfoldings.Cap.OriginalCutCarrier](../Unfoldings/Cap/OriginalCutCarrier.lean) | Identify selected original forest segments with the actual closed original seam cut set |
| [Unfoldings.Cap.OriginalCutRestriction](../Unfoldings/Cap/OriginalCutRestriction.lean) | Prove exterior skirt cuts leave exactly the original retained seams on original faces |
| [Unfoldings.Cap.ExtendedOriginalRetain](../Unfoldings/Cap/ExtendedOriginalRetain.lean) | Derive the original retained fine seams from any actual selected auxiliary radial forest |
| [Unfoldings.Cap.ClipOriginalLocalSeparation](../Unfoldings/Cap/ClipOriginalLocalSeparation.lean) | Transfer local roof-face separation covering the original footprint to original-cap nonoverlap |
| [Unfoldings.Cap.UniformOriginalNonoverlap](../Unfoldings/Cap/UniformOriginalNonoverlap.lean) | Choose a positive mesh-independent tilt threshold for nonoverlap of every original sector-forest development |
| [Unfoldings.Cap.FlatMetric](../Unfoldings/Cap/FlatMetric.lean) | Prove the uncut flat cap development preserves the entire intrinsic metric |
| [Unfoldings.Cap.EdgeUnfolding](../Unfoldings/Cap/EdgeUnfolding.lean) | Prove O'Rourke's uniform nearly flat cap theorem with original-edge cuts, a cut disk, nonoverlap, and interior local isometry |
| [Unfoldings.Development.RestoreSeams](../Unfoldings/Development/RestoreSeams.lean) | Restore coincident whole seam banks with unchanged face placements and nonoverlap |
| [Unfoldings.Cap.OriginalBankFaceValues](../Unfoldings/Cap/OriginalBankFaceValues.lean) | Identify original parent-bank points with their actual incident-face placements |
| [Unfoldings.Cap.FlatSubtreeBanks](../Unfoldings/Cap/FlatSubtreeBanks.lean) | Prove zero-curvature original subtrees have coincident whole seam banks |
| [Unfoldings.Cap.CurvaturePrunedForest](../Unfoldings/Cap/CurvaturePrunedForest.lean) | Remove every flat descendant subtree while preserving an actual original-edge rooted forest and cut disk |
| [Unfoldings.Cap.CurvaturePrunedDevelopment](../Unfoldings/Cap/CurvaturePrunedDevelopment.lean) | Preserve necessary curvature cuts, nonoverlap, and interior local isometry after pruning flat subtrees |
| [Unfoldings.Development.ClosedFaceSeparation](../Unfoldings/Development/ClosedFaceSeparation.lean) | Exclude every foreign closed-face contact at a developed face interior or an open two-face patch |
| [Unfoldings.Development.HingeInteriorContact](../Unfoldings/Development/HingeInteriorContact.lean) | Prove unique intrinsic preimages at retained nonvertex hinges under face-interior nonoverlap |
| [Unfoldings.Cap.LocalClosedFaceSeparation](../Unfoldings/Cap/LocalClosedFaceSeparation.lean) | Exclude foreign closed-face contacts from local roof separation on an open physical region |
| [Unfoldings.Cap.LocalHingeContact](../Unfoldings/Cap/LocalHingeContact.lean) | Exclude foreign physical contacts at retained nonvertex hinges using actual local roof-face separation |
| [Unfoldings.Metric.LocalIsometryBallImage](../Unfoldings/Metric/LocalIsometryBallImage.lean) | Map sufficiently small intrinsic balls onto Euclidean balls at actual regular points |
| [Unfoldings.Development.RegularInteriorContact](../Unfoldings/Development/RegularInteriorContact.lean) | Prove unique intrinsic preimages at every regular point where a nonoverlapping development is locally isometric |
| [Unfoldings.Cap.PrunedInteriorContact](../Unfoldings/Cap/PrunedInteriorContact.lean) | Exclude every foreign developed preimage at pruned cap interior points, including all boundary copies |
| [Unfoldings.Geometry.ClosedInnerBarriers](../Unfoldings/Geometry/ClosedInnerBarriers.lean) | Identify equality under weak inner-circle barriers in different oriented frames |
| [Unfoldings.Geometry.WeakCircleCaps](../Unfoldings/Geometry/WeakCircleCaps.lean) | Retain possible endpoint contacts in circle portions with weak bank bounds |
| [Unfoldings.Cap.ClosedBarrierContact](../Unfoldings/Cap/ClosedBarrierContact.lean) | Identify the only possible contact of actual cross-frame weak circle barriers |
| [Unfoldings.Cap.StripCircleClosedBounds](../Unfoldings/Cap/StripCircleClosedBounds.lean) | Classify every approached closed strip-circle point by its open image or actual bank endpoints |
| [Unfoldings.Cap.ClosedStripCircleCaps](../Unfoldings/Cap/ClosedStripCircleCaps.lean) | Bound actual approached closed strip-circle images by both weak endpoint barriers |
| [Unfoldings.Cap.ComponentBankCircleContact](../Unfoldings/Cap/ComponentBankCircleContact.lean) | Identify actual physical points at closed component-bank contacts, including branch endpoints |
| [Unfoldings.Cap.ChainWeakCircleContact](../Unfoldings/Cap/ChainWeakCircleContact.lean) | Recover matching physical bank points from weak circle contacts even when comparison banks lie inside the circle |
| [Unfoldings.Cap.LocalRegularContact](../Unfoldings/Cap/LocalRegularContact.lean) | Exclude all foreign contacts at regular locally isometric roof points using separation only in the controlled open region |
