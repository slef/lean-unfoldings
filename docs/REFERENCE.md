# Library reference

Start with the [README](../README.md) for the main result and a usage example.
The [plan](../PLAN.md) tracks implemented features and remaining work;
the [log](../LOG.md) records proof-development milestones.

## Module index

Modules are grouped by topic and sorted by name. Each link opens the Lean
source, including its module documentation and declarations.

- [Source unfoldings](#source-unfoldings)
- [Convex caps](#convex-caps)
- [Convex roofs](#convex-roofs)
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
| [Unfoldings.Source.Abstract](../Unfoldings/Source/Abstract.lean) | State source unfolding using independent triangulation, distance, cut locus, and general net validity |
| [Unfoldings.Source.AbstractBridge](../Unfoldings/Source/AbstractBridge.lean) | Prove metric and shortest-path correspondences and that the constructed net folds to its polyhedron |
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

## Convex roofs

Start with the [theorem and proof guide](ROOFS.md). Boundary heights are unrestricted.

| Module | Purpose |
| --- | --- |
| [Unfoldings.Roof.AcrossSectorAllRadiusContact](../Unfoldings/Roof/AcrossSectorAllRadiusContact.lean) | All actual waterfall strip-circle images are pairwise disjoint across the five sectors |
| [Unfoldings.Roof.AcuteProjection](../Unfoldings/Roof/AcuteProjection.lean) | Preserve acute angle margins under uniformly small roof tilt |
| [Unfoldings.Roof.AdjacentClosedSectionSurvivorContact](../Unfoldings/Roof/AdjacentClosedSectionSurvivorContact.lean) | Actual extreme circle survivors in adjacent sectors have disjoint bounding portions |
| [Unfoldings.Roof.AdjacentSectorAllRadiusContact](../Unfoldings/Roof/AdjacentSectorAllRadiusContact.lean) | Every pair of actual waterfall circle images in adjacent sectors is disjoint |
| [Unfoldings.Roof.AdjacentSectorCircleSeparation](../Unfoldings/Roof/AdjacentSectorCircleSeparation.lean) | Every pair of actual waterfall circle images in adjacent sectors is disjoint |
| [Unfoldings.Roof.AdjacentSurvivorCircleCaps](../Unfoldings/Roof/AdjacentSurvivorCircleCaps.lean) | Actual extreme circle survivors in adjacent sectors have disjoint bounding portions |
| [Unfoldings.Roof.AllSectorAllRadiusContact](../Unfoldings/Roof/AllSectorAllRadiusContact.lean) | All actual waterfall strip-circle images are pairwise disjoint across the five sectors |
| [Unfoldings.Roof.AllSectorCircleSeparation](../Unfoldings/Roof/AllSectorCircleSeparation.lean) | All actual waterfall strip-circle images are pairwise disjoint across the five sectors |
| [Unfoldings.Roof.AllVertexContact](../Unfoldings/Roof/AllVertexContact.lean) | All coincident copies of one original vertex agree after pruning, including rim roots |
| [Unfoldings.Roof.AngleBalance](../Unfoldings/Roof/AngleBalance.lean) | Relative angle-defect balance |
| [Unfoldings.Roof.AngularCurvature](../Unfoldings/Roof/AngularCurvature.lean) | Intrinsic vertex curvature is actual outward solid angle |
| [Unfoldings.Roof.BankPositionOrder](../Unfoldings/Roof/BankPositionOrder.lean) | Actual branching bank position order |
| [Unfoldings.Roof.BankSegments](../Unfoldings/Roof/BankSegments.lean) | The matched parameters are exactly the actual straight parent-bank segments |
| [Unfoldings.Roof.Basic](../Unfoldings/Roof/Basic.lean) | Define supported convex triangular roofs with unrestricted boundary heights |
| [Unfoldings.Roof.Boundary](../Unfoldings/Roof/Boundary.lean) | Identify intrinsic roof boundary vertices with the projected domain frontier |
| [Unfoldings.Roof.BoundaryCircleContactAlternative](../Unfoldings/Roof/BoundaryCircleContactAlternative.lean) | An earlier shared-ray circle contact is coherent or puts both crossings on one actual cut |
| [Unfoldings.Roof.BoundaryCirclePhysicalAlternative](../Unfoldings/Roof/BoundaryCirclePhysicalAlternative.lean) | A coherent shared-ray circle contact retains its actual physical point equality |
| [Unfoldings.Roof.BoundaryComponentFineSeed](../Unfoldings/Roof/BoundaryComponentFineSeed.lean) | Any radial component meeting a sector bank inside the clip has a coherent fine seed |
| [Unfoldings.Roof.BoundaryFaceValues](../Unfoldings/Roof/BoundaryFaceValues.lean) | Actual original bank vertices and closed bank segments in arbitrary-rim roof face charts |
| [Unfoldings.Roof.BoundaryRunCircleCaps](../Unfoldings/Roof/BoundaryRunCircleCaps.lean) | One actual disappearing boundary run separates whole coordinate-bounded circle portions |
| [Unfoldings.Roof.BoundaryRunCircleComponent](../Unfoldings/Roof/BoundaryRunCircleComponent.lean) | Neighboring boundary-circle crossings lie on the terminal's actual radial component |
| [Unfoldings.Roof.BoundaryRunCircleConstruction](../Unfoldings/Roof/BoundaryRunCircleConstruction.lean) | Construct extreme actual terminals and separating circle portions for indexed boundary runs |
| [Unfoldings.Roof.BoundaryRunLateCircleCandidate](../Unfoldings/Roof/BoundaryRunLateCircleCandidate.lean) | Crossings after maximal boundary-run terminals supply exact actual circle-bank candidates |
| [Unfoldings.Roof.BoundaryRunNeighborCircleCandidate](../Unfoldings/Roof/BoundaryRunNeighborCircleCandidate.lean) | A neighboring surviving boundary circle supplies its actual bank candidate automatically |
| [Unfoldings.Roof.BoundaryRunNeighborCirclePhysicalCandidate](../Unfoldings/Roof/BoundaryRunNeighborCirclePhysicalCandidate.lean) | A neighboring surviving boundary circle supplies its actual bank candidate automatically |
| [Unfoldings.Roof.BoundaryRunSourceBankCandidate](../Unfoldings/Roof/BoundaryRunSourceBankCandidate.lean) | Every run-side circle crossing has its own actual component-bank bound |
| [Unfoldings.Roof.BoundaryRunTerminalBankCandidate](../Unfoldings/Roof/BoundaryRunTerminalBankCandidate.lean) | Every extreme boundary-run terminal supplies an actual inner bank candidate |
| [Unfoldings.Roof.BoundaryTerminalSectorAssignment](../Unfoldings/Roof/BoundaryTerminalSectorAssignment.lean) | A boundary terminal retains the unique assigned sector of its actual radial component |
| [Unfoldings.Roof.BoundaryTerminalSeedAncestor](../Unfoldings/Roof/BoundaryTerminalSeedAncestor.lean) | Boundary terminals are reached from coherent fine seeds of their radial components |
| [Unfoldings.Roof.BranchDisplacements](../Unfoldings/Roof/BranchDisplacements.lean) | Position gaps include every attached branch |
| [Unfoldings.Roof.CapBridge](../Unfoldings/Roof/CapBridge.lean) | View every existing convex cap as a roof without changing its faces or seams |
| [Unfoldings.Roof.ClosedContactFibers](../Unfoldings/Roof/ClosedContactFibers.lean) | Closed physical contact identification determines the entire uncut intrinsic fiber |
| [Unfoldings.Roof.ClosedFaceAllRadiusContact](../Unfoldings/Roof/ClosedFaceAllRadiusContact.lean) | Coincident actual closed-face copies identify the same physical point at controlled radii |
| [Unfoldings.Roof.ClosedLeafTailCircleContact](../Unfoldings/Roof/ClosedLeafTailCircleContact.lean) | Contact across one actual leaf tail identifies the same physical circle endpoint |
| [Unfoldings.Roof.ClosedOuterSectionComponentBank](../Unfoldings/Roof/ClosedOuterSectionComponentBank.lean) | Named component circle banks retain their exact physical surface coordinates |
| [Unfoldings.Roof.ClosedSectionBoundaryLateCandidate](../Unfoldings/Roof/ClosedSectionBoundaryLateCandidate.lean) | Closed sections retain strict terminal progress even when they end at a pinch |
| [Unfoldings.Roof.ClosedSectionBoundaryNeighborCandidate](../Unfoldings/Roof/ClosedSectionBoundaryNeighborCandidate.lean) | A neighboring surviving boundary circle supplies its actual bank candidate automatically |
| [Unfoldings.Roof.ClosedSectionBoundaryRunConstruction](../Unfoldings/Roof/ClosedSectionBoundaryRunConstruction.lean) | Construct actual extreme terminals and identify closed contacts across an indexed boundary run |
| [Unfoldings.Roof.ClosedSectionBoundaryRunContact](../Unfoldings/Roof/ClosedSectionBoundaryRunContact.lean) | Weak contacts across disappearing boundary runs identify actual physical endpoints |
| [Unfoldings.Roof.ClosedSectionBoundarySourceCandidate](../Unfoldings/Roof/ClosedSectionBoundarySourceCandidate.lean) | Early terminal bounds persist at every closed circle section, including vertex radii |
| [Unfoldings.Roof.ClosedSectionEarlyRunBounds](../Unfoldings/Roof/ClosedSectionEarlyRunBounds.lean) | Early terminal bounds persist at every closed circle section, including vertex radii |
| [Unfoldings.Roof.ClosedSectionEarlyRunMaxima](../Unfoldings/Roof/ClosedSectionEarlyRunMaxima.lean) | Early terminal bounds persist at every closed circle section, including vertex radii |
| [Unfoldings.Roof.ClosedSectionLateRunBounds](../Unfoldings/Roof/ClosedSectionLateRunBounds.lean) | Closed sections retain strict terminal progress even when they end at a pinch |
| [Unfoldings.Roof.ClosedSectionRemovedRunContact](../Unfoldings/Roof/ClosedSectionRemovedRunContact.lean) | Contacts between consecutive actual circle survivors preserve their physical surface point |
| [Unfoldings.Roof.ClosedSectionRunPhysicalContact](../Unfoldings/Roof/ClosedSectionRunPhysicalContact.lean) | Closed section contacts across disappearing strip runs preserve physical points at all radii |
| [Unfoldings.Roof.ClosedSectionSeparatorContact](../Unfoldings/Roof/ClosedSectionSeparatorContact.lean) | Circle endpoint contact across an actual shared separator preserves the physical point |
| [Unfoldings.Roof.ClosedSectionTailContact](../Unfoldings/Roof/ClosedSectionTailContact.lean) | Contact across one actual leaf tail identifies the same physical circle endpoint |
| [Unfoldings.Roof.ClosedSharedSeparatorPrefixValue](../Unfoldings/Roof/ClosedSharedSeparatorPrefixValue.lean) | Shared separator prefixes remain coherent through approached terminal pinches |
| [Unfoldings.Roof.CompletedGeometricTailTracking](../Unfoldings/Roof/CompletedGeometricTailTracking.lean) | Actual completed cut paths track the prescribed geometric tails before the deep cutoff |
| [Unfoldings.Roof.CompletionAllRadiusContact](../Unfoldings/Roof/CompletionAllRadiusContact.lean) | Uniform identification of actual closed-face contacts at all controlled radii |
| [Unfoldings.Roof.CompletionBankChainPositions](../Unfoldings/Roof/CompletionBankChainPositions.lean) | Actual fine cut paths inherit source positions and bank-opening sectors together |
| [Unfoldings.Roof.CompletionBankChains](../Unfoldings/Roof/CompletionBankChains.lean) | Entire actual fine-seam bank paths inherit one sector from the original cut component |
| [Unfoldings.Roof.CompletionCalibratedComparisonArcs](../Unfoldings/Roof/CompletionCalibratedComparisonArcs.lean) | Actual roof face bounds construct proper comparison arcs in any specified bank calibration |
| [Unfoldings.Roof.CompletionClosedEmptyCircleContinuations](../Unfoldings/Roof/CompletionClosedEmptyCircleContinuations.lean) | Construct actual disappearing-strip continuations in the same roof calibration |
| [Unfoldings.Roof.CompletionCutRestriction](../Unfoldings/Roof/CompletionCutRestriction.lean) | Exterior radial cuts preserve exactly the retained original seam classes |
| [Unfoldings.Roof.CompletionDomain](../Unfoldings/Roof/CompletionDomain.lean) | The actual support family and convex domain of a physical roof completion |
| [Unfoldings.Roof.CompletionEmptyCircleContinuations](../Unfoldings/Roof/CompletionEmptyCircleContinuations.lean) | Construct actual disappearing-strip continuations in the same roof calibration |
| [Unfoldings.Roof.CompletionEndpointVertices](../Unfoldings/Roof/CompletionEndpointVertices.lean) | Every original vertex survives as an actual vertex of the physical completion mesh |
| [Unfoldings.Roof.CompletionExtendedMesh](../Unfoldings/Roof/CompletionExtendedMesh.lean) | The constructed original and skirt cut set is an actual union of removed physical seams |
| [Unfoldings.Roof.CompletionFaceSeparation](../Unfoldings/Roof/CompletionFaceSeparation.lean) | A positive threshold chosen before both meshes separates actual roof-face interiors locally |
| [Unfoldings.Roof.CompletionLeafCoherence](../Unfoldings/Roof/CompletionLeafCoherence.lean) | Actual geometric leaves survive refinement and have coherent developed endpoint values |
| [Unfoldings.Roof.CompletionMesh](../Unfoldings/Roof/CompletionMesh.lean) | Construct tilt-preserving physical cap meshes extending arbitrary-rim roofs |
| [Unfoldings.Roof.CompletionRegion](../Unfoldings/Roof/CompletionRegion.lean) | Preserve the extended roof on any compact region in a physical completion |
| [Unfoldings.Roof.CompletionCurve](../Unfoldings/Roof/CompletionCurve.lean) | Derive strict containment and curve avoidance for the actual completion cap |
| [Unfoldings.Roof.CompletedBankComparison](../Unfoldings/Roof/CompletedBankComparison.lean) | Construct a small-error comparison cap preserving the entire Jordan filling |
| [Unfoldings.Complex.BoundaryContourPaths](../Unfoldings/Complex/BoundaryContourPaths.lean) | Complete directed contours cover actual banks and avoid vertices on open banks |
| [Unfoldings.Cap.JordanContourSegments](../Unfoldings/Cap/JordanContourSegments.lean) | Exact cyclic segment cover of a Jordan curve with its actual physical vertex positions |
| [Unfoldings.Topology.ClosedPartition](../Unfoldings/Topology/ClosedPartition.lean) | Connected pieces cannot switch closed sets away from their contacts |
| [Unfoldings.Cap.JordanContourPartition](../Unfoldings/Cap/JordanContourPartition.lean) | Assign whole actual contour banks to finite closed arcs meeting at contour vertices |
| [Unfoldings.Geometry.MarkedPointConstraints](../Unfoldings/Geometry/MarkedPointConstraints.lean) | Crossing coordinate constraints force marked points to be actual mesh corners |
| [Unfoldings.Roof.CompletionMarkedPoints](../Unfoldings/Roof/CompletionMarkedPoints.lean) | Preserve prescribed points as genuine intrinsic vertices of a completion cap |
| [Unfoldings.Geometry.RadialClosureContacts](../Unfoldings/Geometry/RadialClosureContacts.lean) | Exact radial bank contacts and the actual four-piece closure cover |
| [Unfoldings.Roof.MarkedClosureCompletion](../Unfoldings/Roof/MarkedClosureCompletion.lean) | Construct a physical completion with every closing corner on its actual contour |
| [Unfoldings.Roof.MarkedContourPartition](../Unfoldings/Roof/MarkedContourPartition.lean) | Derive whole-bank correspondence to the radial bank and three closing links |
| [Unfoldings.Topology.FiniteTwoCutOrder](../Unfoldings/Topology/FiniteTwoCutOrder.lean) | Propagate labels along finite intervals and split a cyclic order at two contacts |
| [Unfoldings.Cap.JordanContourBankOrder](../Unfoldings/Cap/JordanContourBankOrder.lean) | Derive opposite bank runs from two nontrivial geometric arcs |
| [Unfoldings.Cap.JordanContourBankInterval](../Unfoldings/Cap/JordanContourBankInterval.lean) | Identify actual geometric bank indices with a strict cyclic interval |
| [Unfoldings.Geometry.FiniteHeadingWindow](../Unfoldings/Geometry/FiniteHeadingWindow.lean) | Strict internal vertex sums are exactly last-link heading prefixes |
| [Unfoldings.Cap.JordanCyclicRolling](../Unfoldings/Cap/JordanCyclicRolling.lean) | Actual rotated intrinsic rolling has the exact geometric bank turn sum |
| [Unfoldings.Geometry.RadialBankInterior](../Unfoldings/Geometry/RadialBankInterior.lean) | Construct bank interior witnesses and exclude the two off-bank closing corners |
| [Unfoldings.Cap.RadialCyclicBankComparison](../Unfoldings/Cap/RadialCyclicBankComparison.lean) | Derive orientation and real heading comparison for the actual radial bank |
| [Unfoldings.Roof.CompletedRollingComparison](../Unfoldings/Roof/CompletedRollingComparison.lean) | Construct a uniformly small actual rolling error on a roof-preserving completion |
| [Unfoldings.Topology.ConvexJordanBoundary](../Unfoldings/Topology/ConvexJordanBoundary.lean) | A bounded convex planar body has an actual Jordan frontier |
| [Unfoldings.Roof.ConvexRestriction](../Unfoldings/Roof/ConvexRestriction.lean) | Convex whole-face restrictions preserve every intrinsic point under projection |
| [Unfoldings.Roof.CompletionOriginalCarrier](../Unfoldings/Roof/CompletionOriginalCarrier.lean) | The original physical patch has exactly its original footprint and spatial placements |
| [Unfoldings.Roof.CompletionConstraintSelection](../Unfoldings/Roof/CompletionConstraintSelection.lean) | Select named equations while keeping the exact same physical mesh and cap |
| [Unfoldings.Roof.CompletionCombinedConstraints](../Unfoldings/Roof/CompletionCombinedConstraints.lean) | Combine original-face sides and new cuts with the existing original-cut metric isometry |
| [Unfoldings.Cap.SmallBankRolling](../Unfoldings/Cap/SmallBankRolling.lean) | Concrete actual endpoint copies, bank span and unreduced rolling error conclusion |
| [Unfoldings.Roof.MarkedCompletionRolling](../Unfoldings/Roof/MarkedCompletionRolling.lean) | Uniform actual rolling bound for every marked completion mesh |
| [Unfoldings.Roof.ShortWindowRolling](../Unfoldings/Roof/ShortWindowRolling.lean) | Construct accurate intrinsic rolling from short radial-window geometry alone |
| [Unfoldings.Geometry.PolarWindowInterval](../Unfoldings/Geometry/PolarWindowInterval.lean) | Actual internal source-ray sums equal the original strict polar-window variation |
| [Unfoldings.Geometry.PolarWindowRadial](../Unfoldings/Geometry/PolarWindowRadial.lean) | Actual planar subwindows inherit genuine rays, links and strict radial progress |
| [Unfoldings.Roof.PolarWindowRolling](../Unfoldings/Roof/PolarWindowRolling.lean) | The weighted estimates' precise polar windows construct actual physical rolling comparisons |
| [Unfoldings.Geometry.RadialBlockThreshold](../Unfoldings/Geometry/RadialBlockThreshold.lean) | Positive mesh-independent heading and tilt tolerances make weighted radial loss small |
| [Unfoldings.Roof.RollingRadialBlockThreshold](../Unfoldings/Roof/RollingRadialBlockThreshold.lean) | One uniform tolerance controls actual bank rolling and radial loss at every smaller tilt |
| [Unfoldings.Development.RigidPlacements](../Unfoldings/Development/RigidPlacements.lean) | Separated joined rigid placements derive opposite-side hinges |
| [Unfoldings.Development.FlatCap](../Unfoldings/Development/FlatCap.lean) | Convex planar placements give flat caps and exact boundary fan angles |
| [Unfoldings.Roof.CompletionFacePatch](../Unfoldings/Roof/CompletionFacePatch.lean) | Actual fine pieces in one original face develop injectively onto that metric triangle |
| [Unfoldings.Geometry.TriangleBoundaryRays](../Unfoldings/Geometry/TriangleBoundaryRays.lean) | Actual frontier directions at a triangle corner recover its exact original angle |
| [Unfoldings.Cap.TriangularFootprintAngles](../Unfoldings/Cap/TriangularFootprintAngles.lean) | Triangular footprint corners have their exact projected fan angles |
| [Unfoldings.Geometry.TriangleSubsetCorners](../Unfoldings/Geometry/TriangleSubsetCorners.lean) | A contained triangle preserves every original extreme corner it contains |
| [Unfoldings.Roof.CompletionFaceAngles](../Unfoldings/Roof/CompletionFaceAngles.lean) | Fine corner contributions at every original face corner sum to its exact old angle |
| [Unfoldings.Roof.CompletionOriginalAdjacency](../Unfoldings/Roof/CompletionOriginalAdjacency.lean) | Locate fine adjacency between different original faces on their common edge |
| [Unfoldings.Roof.CompletionOriginalConforming](../Unfoldings/Roof/CompletionOriginalConforming.lean) | Prove exact retained seam classes and the original-cut metric equivalence |
| [Unfoldings.Roof.CompletionOriginalCoordinates](../Unfoldings/Roof/CompletionOriginalCoordinates.lean) | Prove that contained auxiliary pieces have the actual original face Euclidean metric |
| [Unfoldings.Roof.CompletionOriginalCopies](../Unfoldings/Roof/CompletionOriginalCopies.lean) | Identify every fine point copy within one whole original face |
| [Unfoldings.Roof.CompletionOriginalCurvature](../Unfoldings/Roof/CompletionOriginalCurvature.lean) | Completion curvature inside the original roof is supported only on original vertices |
| [Unfoldings.Roof.CompletionOriginalEdgeCover](../Unfoldings/Roof/CompletionOriginalEdgeCover.lean) | Original whole edges are exact unions of physical completion edges |
| [Unfoldings.Roof.CompletionOriginalFaceMap](../Unfoldings/Roof/CompletionOriginalFaceMap.lean) | Map each whole original face continuously into its fine cut surface |
| [Unfoldings.Roof.CompletionOriginalForestRetention](../Unfoldings/Roof/CompletionOriginalForestRetention.lean) | Auxiliary radial forests keep all fine seams needed by the original cut roof |
| [Unfoldings.Roof.CompletionOriginalLocalSeparation](../Unfoldings/Roof/CompletionOriginalLocalSeparation.lean) | Local roof-face separation over the whole original footprint proves original-roof nonoverlap |
| [Unfoldings.Roof.CompletionOriginalNonoverlap](../Unfoldings/Roof/CompletionOriginalNonoverlap.lean) | Transfer nonoverlap between the fine pieces and the original development |
| [Unfoldings.Roof.CompletionOriginalPieces](../Unfoldings/Roof/CompletionOriginalPieces.lean) | Cover every whole original face by contained auxiliary triangles with unique old parents |
| [Unfoldings.Roof.CompletionOriginalPlacementAgreement](../Unfoldings/Roof/CompletionOriginalPlacementAgreement.lean) | Normalize an actual roof development to agree with every original whole-face placement |
| [Unfoldings.Roof.CompletionOriginalRegularCopies](../Unfoldings/Roof/CompletionOriginalRegularCopies.lean) | Restrict auxiliary point identifications away from vertices and cuts |
| [Unfoldings.Roof.CompletionOriginalRespects](../Unfoldings/Roof/CompletionOriginalRespects.lean) | Send retained fine seams to retained original seam chains |
| [Unfoldings.Roof.CompletionOriginalRetention](../Unfoldings/Roof/CompletionOriginalRetention.lean) | Keep every fine seam internal to one original face |
| [Unfoldings.Roof.CompletionOriginalSeamMap](../Unfoldings/Roof/CompletionOriginalSeamMap.lean) | Join whole original face maps across retained seams, including endpoints |
| [Unfoldings.Roof.CompletionOriginalSubdivision](../Unfoldings/Roof/CompletionOriginalSubdivision.lean) | Construct the isometric subdivision of the original mesh inside the physical completion |
| [Unfoldings.Roof.CompletionOutwardForest](../Unfoldings/Roof/CompletionOutwardForest.lean) | Construct an actual outward auxiliary forest from the original forest and radial tails |
| [Unfoldings.Roof.CompletionPathWedges](../Unfoldings/Roof/CompletionPathWedges.lean) | Curvature-carrying auxiliary paths inherit the acute wedges of the constructed network |
| [Unfoldings.Roof.CompletionPlanes](../Unfoldings/Roof/CompletionPlanes.lean) | Preserve old rigid face planes and construct actual new planes in roof completions |
| [Unfoldings.Roof.CompletionPrescribedSegments](../Unfoldings/Roof/CompletionPrescribedSegments.lean) | Mesh prescribed closed segments while retaining all original roof edge constraints |
| [Unfoldings.Roof.CompletionRadialCurvature](../Unfoldings/Roof/CompletionRadialCurvature.lean) | Constructed original and radial cuts cover every positive-curvature auxiliary vertex |
| [Unfoldings.Roof.CompletionRadialMesh](../Unfoldings/Roof/CompletionRadialMesh.lean) | Construct the actual whole-edge mesh of the previously chosen exterior radial components |
| [Unfoldings.Roof.CompletionRadialWaterfallData](../Unfoldings/Roof/CompletionRadialWaterfallData.lean) | One actual radial waterfall retains all leaf provenance and developed strip data uniformly |
| [Unfoldings.Roof.CompletionRefinement](../Unfoldings/Roof/CompletionRefinement.lean) | Refine an existing physical roof completion without changing its height function or domain |
| [Unfoldings.Roof.CompletionRefinementCurvature](../Unfoldings/Roof/CompletionRefinementCurvature.lean) | Physical line refinement creates no positive curvature away from preceding mesh corners |
| [Unfoldings.Roof.CompletionRegularBankWidth](../Unfoldings/Roof/CompletionRegularBankWidth.lean) | Positive-height regular points avoid every actual geometric waterfall pinch |
| [Unfoldings.Roof.CompletionSectorCircleGeometry](../Unfoldings/Roof/CompletionSectorCircleGeometry.lean) | Uniform separation of all actual strip-circle images within each waterfall sector |
| [Unfoldings.Roof.CompletionSectorQuadrants](../Unfoldings/Roof/CompletionSectorQuadrants.lean) | One mesh-independent tilt budget controls actual directions throughout the completed roof |
| [Unfoldings.Roof.CompletionSkirtSeeds](../Unfoldings/Roof/CompletionSkirtSeeds.lean) | Actual exterior corners are selected before the radial continuation mesh is constructed |
| [Unfoldings.Roof.CompletionSourceCoherence](../Unfoldings/Roof/CompletionSourceCoherence.lean) | The planar source has one actual developed value, even when it is not a mesh vertex |
| [Unfoldings.Roof.CompletionSubtreeSectors](../Unfoldings/Roof/CompletionSubtreeSectors.lean) | Actual extended parent subtrees have derived common five-sector coordinates |
| [Unfoldings.Roof.CompletionWaterfallDomains](../Unfoldings/Roof/CompletionWaterfallDomains.lean) | Constructed waterfall strip interiors lie in the actual uncut completion domain |
| [Unfoldings.Roof.CompletionWaterfallProvenance](../Unfoldings/Roof/CompletionWaterfallProvenance.lean) | Retain actual leaf/separator provenance with cut avoidance and coherent waterfall domains |
| [Unfoldings.Roof.ComponentBankCircleCaps](../Unfoldings/Roof/ComponentBankCircleCaps.lean) | Actual component banks separate entire coordinate-bounded circle portions |
| [Unfoldings.Roof.ComponentBankCircleContact](../Unfoldings/Roof/ComponentBankCircleContact.lean) | Any weak circle contact across actual skirt-component banks is an actual named bank point |
| [Unfoldings.Roof.ComponentBankCircleSeparation](../Unfoldings/Roof/ComponentBankCircleSeparation.lean) | Actual radial-component banks separate outward circle arcs in neighboring frames |
| [Unfoldings.Roof.ContactSeparatorCircleOrder](../Unfoldings/Roof/ContactSeparatorCircleOrder.lean) | Actual adjacent developed strip-circle slices are disjoint across their shared separator |
| [Unfoldings.Roof.ContactSeparatorCirclePrefix](../Unfoldings/Roof/ContactSeparatorCirclePrefix.lean) | Actual adjacent circle endpoints agree before their shared separator's leaf |
| [Unfoldings.Roof.ContactSeparatorPrefix](../Unfoldings/Roof/ContactSeparatorPrefix.lean) | Coherent separator prefixes and terminal-height bounds need only physical bank contact |
| [Unfoldings.Roof.ContactSeparatorValues](../Unfoldings/Roof/ContactSeparatorValues.lean) | Actual developed traces agree on a separator's approached coherent prefix |
| [Unfoldings.Roof.ContourExcursion](../Unfoldings/Roof/ContourExcursion.lean) | Exact displacement for a partial contour excursion between copies of one original vertex |
| [Unfoldings.Roof.CurvatureBudget](../Unfoldings/Roof/CurvatureBudget.lean) | Nonnegative intrinsic curvature and its mesh-independent small-tilt budget |
| [Unfoldings.Roof.CurvatureCutDevelopment](../Unfoldings/Roof/CurvatureCutDevelopment.lean) | Developing cut disks while leaving flat subdivision vertices uncut |
| [Unfoldings.Roof.CurvatureNonnegative](../Unfoldings/Roof/CurvatureNonnegative.lean) | Nonnegative intrinsic curvature and its mesh-independent small-tilt budget |
| [Unfoldings.Roof.CurvaturePrunedDevelopment](../Unfoldings/Roof/CurvaturePrunedDevelopment.lean) | Pruning flat subtrees preserves necessary curvature cuts and interior local isometry |
| [Unfoldings.Roof.CurvaturePrunedForest](../Unfoldings/Roof/CurvaturePrunedForest.lean) | Remove every zero-curvature descendant subtree from the actual original cutting forest |
| [Unfoldings.Roof.DeepGeometricWaterfall](../Unfoldings/Roof/DeepGeometricWaterfall.lean) | Deep clipping makes the actual waterfall strip interiors lie in the regular roof region |
| [Unfoldings.Roof.DevelopmentCoordinates](../Unfoldings/Roof/DevelopmentCoordinates.lean) | Actual developed face charts over the horizontal coordinates of an arbitrary-rim roof |
| [Unfoldings.Roof.DevelopmentOrientation](../Unfoldings/Roof/DevelopmentOrientation.lean) | One orientation relative to actual roof projection |
| [Unfoldings.Roof.EarlyCircleTerminalPrefix](../Unfoldings/Roof/EarlyCircleTerminalPrefix.lean) | Early circle crossings beyond a terminated prefix are controlled by the first later terminal |
| [Unfoldings.Roof.EarlyCircleTerminalPrefixContacts](../Unfoldings/Roof/EarlyCircleTerminalPrefixContacts.lean) | Early circle crossings beyond a terminated prefix are controlled by the first later terminal |
| [Unfoldings.Roof.EarlyTerminalBankOrder](../Unfoldings/Roof/EarlyTerminalBankOrder.lean) | Early surviving circle crossings are bounded by the intermediate strip's terminal copy |
| [Unfoldings.Roof.EdgeUnfolding](../Unfoldings/Roof/EdgeUnfolding.lean) | Every sufficiently shallow acute convex roof has a nonoverlapping original-edge cut disk |
| [Unfoldings.Roof.EmptyNeighborCirclePrefix](../Unfoldings/Roof/EmptyNeighborCirclePrefix.lean) | A surviving circle crossing lies beyond its shared leaf when its neighbor has disappeared |
| [Unfoldings.Roof.EmptyNeighborContactPrefix](../Unfoldings/Roof/EmptyNeighborContactPrefix.lean) | A surviving circle crossing lies beyond its shared leaf when its neighbor has disappeared |
| [Unfoldings.Roof.EmptyStripChainLateCircleSeparation](../Unfoldings/Roof/EmptyStripChainLateCircleSeparation.lean) | Separate surviving circle slices beyond a finite chain of permanently collapsed strips |
| [Unfoldings.Roof.EmptyStripChainLateContactSeparation](../Unfoldings/Roof/EmptyStripChainLateContactSeparation.lean) | Separate surviving circle slices beyond a finite chain of permanently collapsed strips |
| [Unfoldings.Roof.EmptyStripCircleSeparation](../Unfoldings/Roof/EmptyStripCircleSeparation.lean) | Separate two surviving circle slices across one disappearing actual strip |
| [Unfoldings.Roof.EmptyStripLateCircleSeparation](../Unfoldings/Roof/EmptyStripLateCircleSeparation.lean) | Separate surviving strip slices beyond an intervening strip's actual terminal height |
| [Unfoldings.Roof.EmptyStripRunContactSeparation](../Unfoldings/Roof/EmptyStripRunContactSeparation.lean) | Separate circle slices across any nonempty run of disappearing actual strips |
| [Unfoldings.Roof.ExtendedComponentSectors](../Unfoldings/Roof/ExtendedComponentSectors.lean) | Every actual geometric cut component lies in one of the five fixed sectors |
| [Unfoldings.Roof.ExtendedComponentWedges](../Unfoldings/Roof/ExtendedComponentWedges.lean) | Each complete extended geometric cut component has one acute direction wedge |
| [Unfoldings.Roof.ExtendedCutCarrier](../Unfoldings/Roof/ExtendedCutCarrier.lean) | The explicit geometric parent forest represents the entire original-and-skirt cut set |
| [Unfoldings.Roof.ExtendedCutEmbedding](../Unfoldings/Roof/ExtendedCutEmbedding.lean) | The finite geometric cut forest has distinct actual projected vertex positions |
| [Unfoldings.Roof.ExtendedCutGrowth](../Unfoldings/Roof/ExtendedCutGrowth.lean) | Local outward progress on the constructed original cuts and radial skirt continuations |
| [Unfoldings.Roof.ExtendedCutLabels](../Unfoldings/Roof/ExtendedCutLabels.lean) | Consistent radial-component labels for every actual original cut and skirt continuation |
| [Unfoldings.Roof.ExtendedCutParents](../Unfoldings/Roof/ExtendedCutParents.lean) | The complete geometric original-cut and skirt network is an explicit finite parent forest |
| [Unfoldings.Roof.ExtendedGeometricCuts](../Unfoldings/Roof/ExtendedGeometricCuts.lean) | Actual original whole-edge cuts together with their exterior radial continuations |
| [Unfoldings.Roof.FaceRestriction](../Unfoldings/Roof/FaceRestriction.lean) | Restrict rigid roof geometry and identify all nonvertex projection fibers |
| [Unfoldings.Roof.FlatSubtreeBanks](../Unfoldings/Roof/FlatSubtreeBanks.lean) | Original parent seams bounding zero-curvature subtrees are actual removable flat slits |
| [Unfoldings.Roof.ForestSource](../Unfoldings/Roof/ForestSource.lean) | Choose an interior source to the right of all interior vertices, including meshes with none |
| [Unfoldings.Roof.GeometricBankPersistence](../Unfoldings/Roof/GeometricBankPersistence.lean) | An actual tail cannot leave an exterior sector bank after contacting it beyond its leaf |
| [Unfoldings.Roof.GeometricChainNetwork](../Unfoldings/Roof/GeometricChainNetwork.lean) | Physical fine cut chains inherit the actual sector network and its positive coordinates |
| [Unfoldings.Roof.GeometricChainSectors](../Unfoldings/Roof/GeometricChainSectors.lean) | Fine parent directions use the same chosen sector as their actual geometric leaf |
| [Unfoldings.Roof.GeometricComponentBanks](../Unfoldings/Roof/GeometricComponentBanks.lean) | A specified geometric component controls fine parent banks starting at any of its cut points |
| [Unfoldings.Roof.GeometricComponentNetwork](../Unfoldings/Roof/GeometricComponentNetwork.lean) | Physical component cut pieces belong to the actual deterministic sector network |
| [Unfoldings.Roof.GeometricComponentPieces](../Unfoldings/Roof/GeometricComponentPieces.lean) | Whole physical cut pieces retain their geometric component's chosen sector data |
| [Unfoldings.Roof.GeometricCutFlow](../Unfoldings/Roof/GeometricCutFlow.lean) | The complete geometric cut forest has a unique forward edge at every nonterminal point |
| [Unfoldings.Roof.GeometricCutIncidence](../Unfoldings/Roof/GeometricCutIncidence.lean) | A geometric cut vertex lying on a geometric edge is one of its actual endpoints |
| [Unfoldings.Roof.GeometricCutLabels](../Unfoldings/Roof/GeometricCutLabels.lean) | Component labels and fixed sectors on the complete geometric cut parent forest |
| [Unfoldings.Roof.GeometricCutNoncrossing](../Unfoldings/Roof/GeometricCutNoncrossing.lean) | Distinct edges of the complete geometric forest meet only at shared endpoints |
| [Unfoldings.Roof.GeometricCutPaths](../Unfoldings/Roof/GeometricCutPaths.lean) | Exact monotone height graphs for all complete geometric cut paths |
| [Unfoldings.Roof.GeometricFineTailTracking](../Unfoldings/Roof/GeometricFineTailTracking.lean) | The actual geometric tail point is on a whole edge of every outward fine cut chain |
| [Unfoldings.Roof.GeometricFreshWaterfallLeaf](../Unfoldings/Roof/GeometricFreshWaterfallLeaf.lean) | A fresh actual leaf is inserted in a positive-width cell, unless it is the source itself |
| [Unfoldings.Roof.GeometricHeightNetwork](../Unfoldings/Roof/GeometricHeightNetwork.lean) | Instantiate the forward-deterministic height network with actual geometric cut components |
| [Unfoldings.Roof.GeometricLeafAvoidance](../Unfoldings/Roof/GeometricLeafAvoidance.lean) | An unprocessed geometric leaf cannot lie on another leaf's existing root path |
| [Unfoldings.Roof.GeometricLeafInterior](../Unfoldings/Roof/GeometricLeafInterior.lean) | Every nonterminal node of the actual geometric forest lies strictly inside the roof clip |
| [Unfoldings.Roof.GeometricLeafMinimum](../Unfoldings/Roof/GeometricLeafMinimum.lean) | Actual geometric leaves are local radial minima of the complete prescribed cut network |
| [Unfoldings.Roof.GeometricLeafSupport](../Unfoldings/Roof/GeometricLeafSupport.lean) | Every geometric cut-edge point lies above a descendant leaf in its component sweep |
| [Unfoldings.Roof.GeometricLeafSweep](../Unfoldings/Roof/GeometricLeafSweep.lean) | Each geometric component admits a height sweep in which every edge lies above a leaf |
| [Unfoldings.Roof.GeometricLevelBankOrder](../Unfoldings/Roof/GeometricLevelBankOrder.lean) | Actual regular facing banks have gap order whenever their physical points coincide |
| [Unfoldings.Roof.GeometricRadialEdges](../Unfoldings/Roof/GeometricRadialEdges.lean) | Every active geometric component has an actual seed-to-tip edge in the cut forest |
| [Unfoldings.Roof.GeometricRadialGraphs](../Unfoldings/Roof/GeometricRadialGraphs.lean) | Construct the exact source-ray graph of the radial edge of every active cut component |
| [Unfoldings.Roof.GeometricRecoverableWaterfall](../Unfoldings/Roof/GeometricRecoverableWaterfall.lean) | Every constructed actual sector waterfall reopens only at its source or geometric leaves |
| [Unfoldings.Roof.GeometricSectorBankPoints](../Unfoldings/Roof/GeometricSectorBankPoints.lean) | The same numerical sector banks support the arbitrary-rim geometric forest |
| [Unfoldings.Roof.GeometricSectorBoundaryLeaves](../Unfoldings/Roof/GeometricSectorBoundaryLeaves.lean) | A nonterminal geometric node on its sector bank must be a leaf |
| [Unfoldings.Roof.GeometricSectorCutPoint](../Unfoldings/Roof/GeometricSectorCutPoint.lean) | Every actual cut point strictly inside a sweep sector belongs to a leaf tail in that sector |
| [Unfoldings.Roof.GeometricSectorData](../Unfoldings/Roof/GeometricSectorData.lean) | Actual component sector choices and exact enclosing strips for their geometric tails |
| [Unfoldings.Roof.GeometricSectorNetwork](../Unfoldings/Roof/GeometricSectorNetwork.lean) | One sector network includes every geometric tree whose edge directions lie in that sector |
| [Unfoldings.Roof.GeometricSectorPositions](../Unfoldings/Roof/GeometricSectorPositions.lean) | Choose a sector containing both the positions and the directions of an actual cut component |
| [Unfoldings.Roof.GeometricSectorTails](../Unfoldings/Roof/GeometricSectorTails.lean) | Common-sector networks control actual tails from different geometric components |
| [Unfoldings.Roof.GeometricSeparatorPrefix](../Unfoldings/Roof/GeometricSeparatorPrefix.lean) | A separator's strict-sector prefix can meet actual cuts only at coherent wall contacts |
| [Unfoldings.Roof.GeometricTailAffine](../Unfoldings/Roof/GeometricTailAffine.lean) | Actual tail graphs and exterior rays are locally affine away from geometric vertices |
| [Unfoldings.Roof.GeometricTailBankContacts](../Unfoldings/Roof/GeometricTailBankContacts.lean) | Beyond its starting leaf, an actual tail can meet a sector bank only on its radial skirt |
| [Unfoldings.Roof.GeometricTailCoalescence](../Unfoldings/Roof/GeometricTailCoalescence.lean) | Constructed actual cut tails merge permanently and retain a consistent sweep order |
| [Unfoldings.Roof.GeometricTailCutoff](../Unfoldings/Roof/GeometricTailCutoff.lean) | A deep physical roof clip puts every actual tail endpoint beyond the chosen sweep slab |
| [Unfoldings.Roof.GeometricTailEdgeCover](../Unfoldings/Roof/GeometricTailEdgeCover.lean) | Every point on an actual ancestor edge is on the exact represented tail graph |
| [Unfoldings.Roof.GeometricTailGraphs](../Unfoldings/Roof/GeometricTailGraphs.lean) | Construct exact covered height graphs for every tail of one actual geometric component |
| [Unfoldings.Roof.GeometricTailLeaves](../Unfoldings/Roof/GeometricTailLeaves.lean) | A new geometric leaf is strictly separated from every distinct existing tail at its height |
| [Unfoldings.Roof.GeometricTailLocalEdge](../Unfoldings/Roof/GeometricTailLocalEdge.lean) | Actual regular tail points avoid network vertices and retain a local physical edge graph |
| [Unfoldings.Roof.GeometricTailPieces](../Unfoldings/Roof/GeometricTailPieces.lean) | Every covered actual tail point lies on a labeled geometric parent edge |
| [Unfoldings.Roof.GeometricTailTraceOrder](../Unfoldings/Roof/GeometricTailTraceOrder.lean) | Actual visible traces progress in both coordinates along a geometric cut tail |
| [Unfoldings.Roof.GeometricTailVertices](../Unfoldings/Roof/GeometricTailVertices.lean) | A geometric vertex on an actual tail is an ancestor in that same cut component |
| [Unfoldings.Roof.GeometricVertexCutPiece](../Unfoldings/Roof/GeometricVertexCutPiece.lean) | Every nonterminal geometric cut vertex has an actual containing piece with its own label |
| [Unfoldings.Roof.GeometricWaterfall](../Unfoldings/Roof/GeometricWaterfall.lean) | Construct a finite strip subdivision from the actual geometric leaves in each sector |
| [Unfoldings.Roof.GeometricWaterfallAvoidance](../Unfoldings/Roof/GeometricWaterfallAvoidance.lean) | Actual cut edges lie on the constructed waterfall boundaries, away from strip interiors |
| [Unfoldings.Roof.GeometricWaterfallRegular](../Unfoldings/Roof/GeometricWaterfallRegular.lean) | Regularity applies to every constructed subdivision retaining the actual leaf tails |
| [Unfoldings.Roof.GeometricWaterfallSectors](../Unfoldings/Roof/GeometricWaterfallSectors.lean) | A waterfall strip interior avoids geometric cut edges from every sector |
| [Unfoldings.Roof.GermCrossing](../Unfoldings/Roof/GermCrossing.lean) | A sign change in an actual incident face meets the supported cone boundary |
| [Unfoldings.Roof.GermNormalCone](../Unfoldings/Roof/GermNormalCone.lean) | Detecting actual normal-cone membership from all incident edge directions |
| [Unfoldings.Roof.GermSupports](../Unfoldings/Roof/GermSupports.lean) | Actual supporting inequalities along incident spatial edge rays |
| [Unfoldings.Roof.GermVectors](../Unfoldings/Roof/GermVectors.lean) | Actual projected germ vectors and their rigid developed images on parent banks |
| [Unfoldings.Roof.Gnomonic](../Unfoldings/Roof/Gnomonic.lean) | Gnomonic coordinates recover the actual supporting normals |
| [Unfoldings.Roof.GnomonicArea](../Unfoldings/Roof/GnomonicArea.lean) | The actual spherical normal image has no more area than its slope polygon |
| [Unfoldings.Roof.GradientSelection](../Unfoldings/Roof/GradientSelection.lean) | Prove gradient monotonicity and straight escape rays from all omitted faces |
| [Unfoldings.Roof.HeightContinuity](../Unfoldings/Roof/HeightContinuity.lean) | Prove continuity of arbitrary-rim supporting roofs |
| [Unfoldings.Roof.HorizontalLevelCap](../Unfoldings/Roof/HorizontalLevelCap.lean) | Translate horizontal-boundary roofs into the geometric convex-cap interface |
| [Unfoldings.Roof.IncidentDirections](../Unfoldings/Roof/IncidentDirections.lean) | The closed projected corner cones cover every direction at an interior vertex |
| [Unfoldings.Roof.InjectiveEdgeUnfolding](../Unfoldings/Roof/InjectiveEdgeUnfolding.lean) | Uniformly shallow acute arbitrary-rim roofs admit globally injective original-edge unfoldings |
| [Unfoldings.Roof.LateTerminalBankOrder](../Unfoldings/Roof/LateTerminalBankOrder.lean) | Late circle crossings progress beyond an intermediate strip's actual terminal copy |
| [Unfoldings.Roof.LeafCompletedTailTracking](../Unfoldings/Roof/LeafCompletedTailTracking.lean) | Every constructed leaf's tail is tracked by the actual fine outward forest |
| [Unfoldings.Roof.LeafTailCircleOrder](../Unfoldings/Roof/LeafTailCircleOrder.lean) | Actual strip-circle slices on opposite sides of a constructed leaf tail are disjoint |
| [Unfoldings.Roof.LeafTailCircleSeparation](../Unfoldings/Roof/LeafTailCircleSeparation.lean) | Actual strip-circle slices on opposite sides of a constructed leaf tail are disjoint |
| [Unfoldings.Roof.LinkCrossingBound](../Unfoldings/Roof/LinkCrossingBound.lean) | Convexity bounds the actual cyclic vertex link by two hemisphere crossings |
| [Unfoldings.Roof.LinkCrossings](../Unfoldings/Roof/LinkCrossings.lean) | The genuine roof link has zero or two crossings according to its actual normal cone |
| [Unfoldings.Roof.MatchedBankPoints](../Unfoldings/Roof/MatchedBankPoints.lean) | Matched points on actual branching parent banks |
| [Unfoldings.Roof.NoAdjacentBoundaryRuns](../Unfoldings/Roof/NoAdjacentBoundaryRuns.lean) | The actual one-sector assignment rules out disappearing runs on both sides of a shared ray |
| [Unfoldings.Roof.NormalArea](../Unfoldings/Roof/NormalArea.lean) | A uniform area budget for all planar normal polygons |
| [Unfoldings.Roof.NormalAreaThreshold](../Unfoldings/Roof/NormalAreaThreshold.lean) | Uniform smallness of the complete planar normal image |
| [Unfoldings.Roof.NormalCone](../Unfoldings/Roof/NormalCone.lean) | The spherical normal polygon is the actual outward normal cone |
| [Unfoldings.Roof.NormalImage](../Unfoldings/Roof/NormalImage.lean) | Planar normal images of convex roof vertices |
| [Unfoldings.Roof.OriginalBankFaceValues](../Unfoldings/Roof/OriginalBankFaceValues.lean) | Every original parent-bank point is the actual affine placement of its incident face |
| [Unfoldings.Roof.OriginalCutCarrier](../Unfoldings/Roof/OriginalCutCarrier.lean) | The selected original forest segments are exactly the actual closed original seam cut set |
| [Unfoldings.Roof.OriginalCutLabels](../Unfoldings/Roof/OriginalCutLabels.lean) | Actual original cut segments have consistent tree labels at every geometric contact |
| [Unfoldings.Roof.OriginalCuts](../Unfoldings/Roof/OriginalCuts.lean) | Locate original seam cuts outside every face interior |
| [Unfoldings.Roof.OriginalFaceHeight](../Unfoldings/Roof/OriginalFaceHeight.lean) | Original whole-face height identities, including arbitrary rim points |
| [Unfoldings.Roof.OriginalSectorFrames](../Unfoldings/Roof/OriginalSectorFrames.lean) | Construct actual common quadrant frames on original faces using their physical cap completion |
| [Unfoldings.Roof.OuterCircleCaps](../Unfoldings/Roof/OuterCircleCaps.lean) | Actual outer banks separate whole coordinate-bounded circle portions across a shared ray |
| [Unfoldings.Roof.OuterCircleContactAlternative](../Unfoldings/Roof/OuterCircleContactAlternative.lean) | Actual surviving outer-bank circle endpoints coincide or belong to one radial component |
| [Unfoldings.Roof.OuterCirclePhysicalAlternative](../Unfoldings/Roof/OuterCirclePhysicalAlternative.lean) | Outer-bank circle endpoints have a common physical point or one actual radial component |
| [Unfoldings.Roof.OuterClosedCircleContact](../Unfoldings/Roof/OuterClosedCircleContact.lean) | Weak outer-circle contacts retain equality of both developed and physical endpoints |
| [Unfoldings.Roof.OuterClosedSectionAlternative](../Unfoldings/Roof/OuterClosedSectionAlternative.lean) | Outer-bank circle endpoints have a common physical point or one actual radial component |
| [Unfoldings.Roof.OuterClosedSectionContact](../Unfoldings/Roof/OuterClosedSectionContact.lean) | Weak outer-circle contacts retain equality of both developed and physical endpoints |
| [Unfoldings.Roof.ParentBankDisplacements](../Unfoldings/Roof/ParentBankDisplacements.lean) | Actual contour entrances, exits, and the positional gap at a branching parent seam |
| [Unfoldings.Roof.ParentBankNoncrossing](../Unfoldings/Roof/ParentBankNoncrossing.lean) | Noncrossing of the actual two banks of a branching parent seam |
| [Unfoldings.Roof.ParentBankOpening](../Unfoldings/Roof/ParentBankOpening.lean) | Constructed actual oriented parent-bank opening data |
| [Unfoldings.Roof.ParentBankVectorOrder](../Unfoldings/Roof/ParentBankVectorOrder.lean) | Actual branching parent-bank vector order in common sector quadrants |
| [Unfoldings.Roof.ParentDirectionRotation](../Unfoldings/Roof/ParentDirectionRotation.lean) | Actual signed parent-direction rotations in a projection-preserving frame |
| [Unfoldings.Roof.ParentRadialGrowth](../Unfoldings/Roof/ParentRadialGrowth.lean) | Every selected parent edge strictly increases source distance along its entire length |
| [Unfoldings.Roof.ParentSegments](../Unfoldings/Roof/ParentSegments.lean) | Actual projected parent segments are the original selected seam edges |
| [Unfoldings.Roof.ProjectedConformity](../Unfoldings/Roof/ProjectedConformity.lean) | Derive face-to-face conformity from an embedded roof projection |
| [Unfoldings.Roof.ProjectedFaces](../Unfoldings/Roof/ProjectedFaces.lean) | Construct exact projected face triangles for arbitrary-rim roofs |
| [Unfoldings.Roof.ProjectedFlatness](../Unfoldings/Roof/ProjectedFlatness.lean) | Projected interior links are flat |
| [Unfoldings.Roof.ProjectedLink](../Unfoldings/Roof/ProjectedLink.lean) | Actual projected rays and disjoint direction cones of a roof vertex link |
| [Unfoldings.Roof.ProjectedOpening](../Unfoldings/Roof/ProjectedOpening.lean) | Prove that actual projected roof seams open to opposite sides |
| [Unfoldings.Roof.ProjectedPointCopies](../Unfoldings/Roof/ProjectedPointCopies.lean) | Compare original point copies across retained whole edges |
| [Unfoldings.Roof.ProjectedPointCopyValues](../Unfoldings/Roof/ProjectedPointCopyValues.lean) | Actual developed values and exact vertex classification of projected face copies |
| [Unfoldings.Roof.ProjectedSeamCompletion](../Unfoldings/Roof/ProjectedSeamCompletion.lean) | Identify all matching projected whole edges with actual original seams |
| [Unfoldings.Roof.ProjectedSeamEndpoints](../Unfoldings/Roof/ProjectedSeamEndpoints.lean) | An actual projected vertex on a seam edge is one of that seam's intrinsic endpoints |
| [Unfoldings.Roof.ProjectedSeamUnique](../Unfoldings/Roof/ProjectedSeamUnique.lean) | Prove uniqueness of an original seam at a nonvertex point |
| [Unfoldings.Roof.ProjectionContour](../Unfoldings/Roof/ProjectionContour.lean) | Actual boundary contours oriented by the original roof projection |
| [Unfoldings.Roof.ProjectionFrame](../Unfoldings/Roof/ProjectionFrame.lean) | A common developed frame preserving the actual projection orientation |
| [Unfoldings.Roof.PrunedAllVertexContact](../Unfoldings/Roof/PrunedAllVertexContact.lean) | Global injectivity of curvature-pruned roof developments under physical contact control |
| [Unfoldings.Roof.PrunedContactReduction](../Unfoldings/Roof/PrunedContactReduction.lean) | All remaining self-contacts of the pruned development involve an actual intrinsic vertex |
| [Unfoldings.Roof.PrunedDevelopmentLocalIsometry](../Unfoldings/Roof/PrunedDevelopmentLocalIsometry.lean) | The actual development obtained by restoring flat cuts is locally isometric on the open disk |
| [Unfoldings.Roof.PrunedSeamContact](../Unfoldings/Roof/PrunedSeamContact.lean) | Pruning removes every coincident pair of regular banks at the same physical roof point |
| [Unfoldings.Roof.PrunedVertexContactFibers](../Unfoldings/Roof/PrunedVertexContactFibers.lean) | All remaining pruned contacts are between intrinsic copies of one physical vertex |
| [Unfoldings.Roof.RadialComponentCircleBanks](../Unfoldings/Roof/RadialComponentCircleBanks.lean) | Actual circle endpoints on radial components select named fine parent banks |
| [Unfoldings.Roof.RadialComponentCirclePhysicalBanks](../Unfoldings/Roof/RadialComponentCirclePhysicalBanks.lean) | Named component circle banks retain their exact physical surface coordinates |
| [Unfoldings.Roof.RadialComponentCommonChain](../Unfoldings/Roof/RadialComponentCommonChain.lean) | Actual fine edges on one pure radial component belong to one common parent chain |
| [Unfoldings.Roof.RadialComponentFineAncestry](../Unfoldings/Roof/RadialComponentFineAncestry.lean) | Physical order along a radial component gives actual fine-forest ancestry |
| [Unfoldings.Roof.RadialComponentFinePath](../Unfoldings/Roof/RadialComponentFinePath.lean) | Actual completed fine paths cover each unattached radial component up to its outer tip |
| [Unfoldings.Roof.RadialComponentIncomingBank](../Unfoldings/Roof/RadialComponentIncomingBank.lean) | Derive an actual incoming fine edge and its positive enclosing-ray coordinates |
| [Unfoldings.Roof.RadialComponentSeed](../Unfoldings/Roof/RadialComponentSeed.lean) | Every nonroot geometric node of a pure radial component is its single seed |
| [Unfoldings.Roof.RadialComponentSeedPath](../Unfoldings/Roof/RadialComponentSeedPath.lean) | The actual fine path from a component seed covers all of its nontip positions |
| [Unfoldings.Roof.RestoredParentBankEndpoints](../Unfoldings/Roof/RestoredParentBankEndpoints.lean) | The actual entrance and exit banks match after pruning a flat subtree |
| [Unfoldings.Roof.RestrictedBoundaryExistence](../Unfoldings/Roof/RestrictedBoundaryExistence.lean) | Construct a boundary bank for every nonempty whole-face roof restriction |
| [Unfoldings.Roof.RestrictedBoundaryFrontier](../Unfoldings/Roof/RestrictedBoundaryFrontier.lean) | Place all actual restricted banks, including endpoints, on the geometric frontier |
| [Unfoldings.Roof.RestrictedBoundaryJordan](../Unfoldings/Roof/RestrictedBoundaryJordan.lean) | Extract a Jordan curve from restricted banks despite possible coincident vertex copies |
| [Unfoldings.Roof.RestrictedDisk](../Unfoldings/Roof/RestrictedDisk.lean) | Prove the disk and Jordan-boundary theorem for whole-edge connected gradient selections |
| [Unfoldings.Roof.RestrictedEmbedding](../Unfoldings/Roof/RestrictedEmbedding.lean) | Exclude intrinsic vertex pinches in whole-face Jordan roof patches |
| [Unfoldings.Roof.RimTails](../Unfoldings/Roof/RimTails.lean) | Original rim continuations from an interior planar source, without a rim-height assumption |
| [Unfoldings.Roof.RootSubtreeContour](../Unfoldings/Roof/RootSubtreeContour.lean) | An original rim-root subtree has exactly the two original rim banks as contour exits |
| [Unfoldings.Roof.SameSectorAllRadiusContact](../Unfoldings/Roof/SameSectorAllRadiusContact.lean) | Full survivor order retains physical point equality whenever developed bank values coincide |
| [Unfoldings.Roof.SameSectorEmptyCircleComparison](../Unfoldings/Roof/SameSectorEmptyCircleComparison.lean) | A disappearing strip's own terminal copy has proper comparison arcs in that strip's sector |
| [Unfoldings.Roof.SectorBankRays](../Unfoldings/Roof/SectorBankRays.lean) | The named enclosing banks identify a common radial component across adjacent sectors |
| [Unfoldings.Roof.SectorBoundaryComponents](../Unfoldings/Roof/SectorBoundaryComponents.lean) | A skirt component on a sector boundary has no original tree attached to it |
| [Unfoldings.Roof.SectorBoundaryCutPoints](../Unfoldings/Roof/SectorBoundaryCutPoints.lean) | Cuts on sector boundary rays are radial skirt pieces or actual leaf endpoints |
| [Unfoldings.Roof.SectorDevelopment](../Unfoldings/Roof/SectorDevelopment.lean) | Construct the actual intrinsic cut disk and a locally isometric facewise development |
| [Unfoldings.Roof.SectorForest](../Unfoldings/Roof/SectorForest.lean) | Construct source-centered original-edge sector forests with interior planar sources |
| [Unfoldings.Roof.SectorForestExistence](../Unfoldings/Roof/SectorForestExistence.lean) | Choose forest and tilt parameters uniformly from only the original acute margin |
| [Unfoldings.Roof.SectorForestGeometry](../Unfoldings/Roof/SectorForestGeometry.lean) | Control source-centered positions, rim roots, and the empty forward sector gap |
| [Unfoldings.Roof.SectorForestPaths](../Unfoldings/Roof/SectorForestPaths.lean) | Prove acute-wedge and radial monotonicity of all selected original-edge paths |
| [Unfoldings.Roof.SectorQuadrants](../Unfoldings/Roof/SectorQuadrants.lean) | Projection-preserving common frames for original roof developments and their sector banks |
| [Unfoldings.Roof.SelectionComplement](../Unfoldings/Roof/SelectionComplement.lean) | Prove connected complement and enclosed-region filling for convex-gradient selections |
| [Unfoldings.Roof.SelectionComponentDisk](../Unfoldings/Roof/SelectionComponentDisk.lean) | Prove a geometric closed disk and Jordan frontier for every convex-gradient component |
| [Unfoldings.Roof.SelectionComponents](../Unfoldings/Roof/SelectionComponents.lean) | Define actual whole-edge selection components and prove connected interior |
| [Unfoldings.Roof.SelectionInteriorLabels](../Unfoldings/Roof/SelectionInteriorLabels.lean) | Propagate component labels across all interior contacts and connected selected regions |
| [Unfoldings.Roof.SelectionIntrinsicDisk](../Unfoldings/Roof/SelectionIntrinsicDisk.lean) | Prove intrinsic closed disks and injective projection for every gradient selection component |
| [Unfoldings.Roof.SharedSeparatorCirclePrefix](../Unfoldings/Roof/SharedSeparatorCirclePrefix.lean) | Actual adjacent circle endpoints agree before their shared separator's leaf |
| [Unfoldings.Roof.SharedSeparatorCircleSeparation](../Unfoldings/Roof/SharedSeparatorCircleSeparation.lean) | Actual adjacent developed strip-circle slices are disjoint across their shared separator |
| [Unfoldings.Roof.SharedSeparatorPrefixValue](../Unfoldings/Roof/SharedSeparatorPrefixValue.lean) | Actual developed traces agree on a separator's approached coherent prefix |
| [Unfoldings.Roof.SimpleEdgeUnfolding](../Unfoldings/Roof/SimpleEdgeUnfolding.lean) | The arbitrary-rim acute-roof theorem |
| [Unfoldings.Roof.SkirtAttachments](../Unfoldings/Roof/SkirtAttachments.lean) | A skirt component attaches to an original rim vertex exactly at its seed |
| [Unfoldings.Roof.SkirtRadialCuts](../Unfoldings/Roof/SkirtRadialCuts.lean) | Finite radial skirt continuations between arbitrary nested convex footprints |
| [Unfoldings.Roof.SkirtRimComponents](../Unfoldings/Roof/SkirtRimComponents.lean) | Original rim roots attach to uniquely labeled radial skirt components |
| [Unfoldings.Roof.SolidNormalArea](../Unfoldings/Roof/SolidNormalArea.lean) | A mesh-independent solid-angle budget for all roof normal cones |
| [Unfoldings.Roof.SpatialEnvelopeCap](../Unfoldings/Roof/SpatialEnvelopeCap.lean) | Assemble genuine geometric caps from actual horizontal affine-roof sections |
| [Unfoldings.Roof.SpatialEnvelopeCoordinates](../Unfoldings/Roof/SpatialEnvelopeCoordinates.lean) | Exact projected coordinates of the normalized physical affine-roof mesh |
| [Unfoldings.Roof.SpatialEnvelopeCurvature](../Unfoldings/Roof/SpatialEnvelopeCurvature.lean) | Incident slopes of the actual normalized spatial roof are active support slopes |
| [Unfoldings.Roof.SpatialEnvelopeEndpointVertices](../Unfoldings/Roof/SpatialEnvelopeEndpointVertices.lean) | Whole-edge segment coverage preserves actual vertices of spatial envelope meshes |
| [Unfoldings.Roof.SpatialEnvelopeInteriorSeams](../Unfoldings/Roof/SpatialEnvelopeInteriorSeams.lean) | Whole physical edges meeting the completion interior have actual seam partners |
| [Unfoldings.Roof.SpatialEnvelopeRetainedClasses](../Unfoldings/Roof/SpatialEnvelopeRetainedClasses.lean) | Preserve physical auxiliary seam classes away from geometric cuts |
| [Unfoldings.Roof.SpatialEnvelopeRoof](../Unfoldings/Roof/SpatialEnvelopeRoof.lean) | Construct embedded convex roofs from conforming physical support-plane partitions |
| [Unfoldings.Roof.StrictGeometricTailGraphs](../Unfoldings/Roof/StrictGeometricTailGraphs.lean) | Actual geometric cut tails and enclosing sector walls progress in both coordinates |
| [Unfoldings.Roof.SubtreeAngles](../Unfoldings/Roof/SubtreeAngles.lean) | Actual branching-subtree angles for the constructed roof forest |
| [Unfoldings.Roof.SupportingEnvelope](../Unfoldings/Roof/SupportingEnvelope.lean) | Identify a roof with the lower envelope of its actual supporting planes |
| [Unfoldings.Roof.TailHeightBankGeometry](../Unfoldings/Roof/TailHeightBankGeometry.lean) | Retargeted actual fine banks retain the specified geometric tail's sector |
| [Unfoldings.Roof.TentClips](../Unfoldings/Roof/TentClips.lean) | Prove properness and arbitrarily deep compact horizontal sections of completed roofs |
| [Unfoldings.Roof.TentCompletion](../Unfoldings/Roof/TentCompletion.lean) | Add four inactive support planes while preserving all original roof heights |
| [Unfoldings.Roof.TentNormals](../Unfoldings/Roof/TentNormals.lean) | Preserve the prescribed tilt budget with actual supporting normals of the completion |
| [Unfoldings.Roof.TerminalBankIntervalOrder](../Unfoldings/Roof/TerminalBankIntervalOrder.lean) | An approached bank following a collapsed strip's actual tail progresses in both coordinates |
| [Unfoldings.Roof.TerminalHeightLeafOrder](../Unfoldings/Roof/TerminalHeightLeafOrder.lean) | A permanently collapsed strip cannot end before a leaf completed by either bank |
| [Unfoldings.Roof.TerminalRecordStep](../Unfoldings/Roof/TerminalRecordStep.lean) | Progress from one actual terminal copy to a later terminal along the same physical tail |
| [Unfoldings.Roof.TerminalRunClosedLateBounds](../Unfoldings/Roof/TerminalRunClosedLateBounds.lean) | Late surviving bank bounds include all vertex radii, using actual closed tracking intervals |
| [Unfoldings.Roof.TerminalRunEarlyBoundsContacts](../Unfoldings/Roof/TerminalRunEarlyBoundsContacts.lean) | Early circle crossings are bounded by extreme terminal maxima of a disappearing run |
| [Unfoldings.Roof.TerminalRunEarlyMaximaContacts](../Unfoldings/Roof/TerminalRunEarlyMaximaContacts.lean) | Every maximal terminal, including either extreme tied copy, bounds an early circle crossing |
| [Unfoldings.Roof.TerminalRunLateBoundsContacts](../Unfoldings/Roof/TerminalRunLateBoundsContacts.lean) | Late surviving circle crossings progress beyond an actual terminal of a finite collapsed run |
| [Unfoldings.Roof.TerminalRunRecords](../Unfoldings/Roof/TerminalRunRecords.lean) | Actual terminal-copy progress propagates through arbitrary runs of disappearing strips |
| [Unfoldings.Roof.TerminalRunRecordsContacts](../Unfoldings/Roof/TerminalRunRecordsContacts.lean) | Actual terminal-copy progress propagates through arbitrary runs of disappearing strips |
| [Unfoldings.Roof.ThreeSectorProgress](../Unfoldings/Roof/ThreeSectorProgress.lean) | Prove actual seam progress in the prescribed acute sectors for arbitrary-rim roofs |
| [Unfoldings.Roof.Tilt](../Unfoldings/Roof/Tilt.lean) | Monotonicity of the geometric normal tilt bound for arbitrary-rim roofs |
| [Unfoldings.Roof.Topology](../Unfoldings/Roof/Topology.lean) | Derive the intrinsic disk topology of a convex-domain roof |
| [Unfoldings.Roof.UniformCurvature](../Unfoldings/Roof/UniformCurvature.lean) | A curvature threshold quantified before the entire mesh |
| [Unfoldings.Roof.UniformOriginalAllRadiusContact](../Unfoldings/Roof/UniformOriginalAllRadiusContact.lean) | Uniform control of actual original closed-face contacts at all radii |
| [Unfoldings.Roof.UniformOriginalNonoverlap](../Unfoldings/Roof/UniformOriginalNonoverlap.lean) | Uniformly small tilt makes original sector-forest developments nonoverlapping |
| [Unfoldings.Roof.VertexContourExcursion](../Unfoldings/Roof/VertexContourExcursion.lean) | Exact displacement for a partial contour excursion between copies of one original vertex |
| [Unfoldings.Roof.VertexExcursionFlatness](../Unfoldings/Roof/VertexExcursionFlatness.lean) | A zero displacement excursion contains only flat selected subtrees |
| [Unfoldings.Roof.VertexExcursionRestoration](../Unfoldings/Roof/VertexExcursionRestoration.lean) | Closing contour excursions identify their endpoints after the actual flat seams are restored |
| [Unfoldings.Roof.VertexExcursions](../Unfoldings/Roof/VertexExcursions.lean) | Construct actual contour prefixes and suffixes between developed copies of a branch vertex |
| [Unfoldings.Roof.VertexProgress](../Unfoldings/Roof/VertexProgress.lean) | Find actual outgoing original edges at interior roof vertices |
| [Unfoldings.Roof.WaterfallCircleExtremeBounds](../Unfoldings/Roof/WaterfallCircleExtremeBounds.lean) | Every actual sector circle image lies between the extreme surviving bank bounds |
| [Unfoldings.Roof.WaterfallCircleRunOrder](../Unfoldings/Roof/WaterfallCircleRunOrder.lean) | Actual facing circle endpoints retain order across every removed physical-cell run |
| [Unfoldings.Roof.WaterfallCircleSurvivorBanks](../Unfoldings/Roof/WaterfallCircleSurvivorBanks.lean) | Surviving source-circle intervals retain both ordered bank coordinates |
| [Unfoldings.Roof.WaterfallCircleSurvivorOrder](../Unfoldings/Roof/WaterfallCircleSurvivorOrder.lean) | Actual source-circle survivors retain their full ordered bank endpoints |
| [Unfoldings.Roof.WaterfallCircleSurvivors](../Unfoldings/Roof/WaterfallCircleSurvivors.lean) | Pairwise separation of surviving actual strip-circle images in one sector |
| [Unfoldings.Roof.WaterfallClosedLevelBankOrder](../Unfoldings/Roof/WaterfallClosedLevelBankOrder.lean) | Actual approached bank order extends to all sweep heights, including terminal mesh vertices |
| [Unfoldings.Roof.WaterfallClosedSectionExtremeBounds](../Unfoldings/Roof/WaterfallClosedSectionExtremeBounds.lean) | Full waterfall bank order includes closed-only sections and all vertex radii |
| [Unfoldings.Roof.WaterfallClosedSectionOrder](../Unfoldings/Roof/WaterfallClosedSectionOrder.lean) | Full waterfall bank order includes closed-only sections and all vertex radii |
| [Unfoldings.Roof.WaterfallClosedSectionPhysicalOrder](../Unfoldings/Roof/WaterfallClosedSectionPhysicalOrder.lean) | Full survivor order retains physical point equality whenever developed bank values coincide |
| [Unfoldings.Roof.WaterfallLevelBankOrder](../Unfoldings/Roof/WaterfallLevelBankOrder.lean) | All surviving actual bank intervals are ordered at every regular physical sweep height |
| [Unfoldings.Roof.WithinSectorAllRadiusContact](../Unfoldings/Roof/WithinSectorAllRadiusContact.lean) | Full survivor order retains physical point equality whenever developed bank values coincide |

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
| [Unfoldings.Complex.FaceRestrictionPairings](../Unfoldings/Complex/FaceRestrictionPairings.lean) | Preserve every original seam name between whole faces in a restriction |
| [Unfoldings.Complex.ProjectedJordanEmbedding](../Unfoldings/Complex/ProjectedJordanEmbedding.lean) | Prove exact intrinsic fibers for conforming projections onto Jordan disks |

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
| [Unfoldings.Geometry.TriangleUnionInterior](../Unfoldings/Geometry/TriangleUnionInterior.lean) | Prove regular closedness and connected interior of whole-edge connected triangular patches |
| [Unfoldings.Geometry.ConformingJordanStar](../Unfoldings/Geometry/ConformingJordanStar.lean) | Identify incident point copies in conforming nonconvex Jordan disks |
| [Unfoldings.Geometry.AffineEnvelope](../Unfoldings/Geometry/AffineEnvelope.lean) | Define continuous concave finite affine roofs, active cells, and horizontal sections |
| [Unfoldings.Geometry.GraphNormal](../Unfoldings/Geometry/GraphNormal.lean) | Construct upward unit normals for affine height graphs and prove tilt bounds |
| [Unfoldings.Geometry.SpatialAffineGraph](../Unfoldings/Geometry/SpatialAffineGraph.lean) | Construct actual rigid Euclidean coordinates for arbitrary affine height planes |
| [Unfoldings.Geometry.SupportedPlane](../Unfoldings/Geometry/SupportedPlane.lean) | Package genuine spatial support planes and derive their actual supporting halfspaces |
| [Unfoldings.Geometry.AffineEnvelopeTriangulation](../Unfoldings/Geometry/AffineEnvelopeTriangulation.lean) | Triangulate compact affine roofs while respecting every prescribed finite proper line |
| [Unfoldings.Geometry.SpatialEnvelope](../Unfoldings/Geometry/SpatialEnvelope.lean) | Construct actual spatial graphs of finite supporting-plane envelopes |
| [Unfoldings.Geometry.SpatialEnvelopeTriangles](../Unfoldings/Geometry/SpatialEnvelopeTriangles.lean) | Build physical roof triangle partitions and preserve line constraints through refinement |
| [Unfoldings.Geometry.SpatialEnvelopePairings](../Unfoldings/Geometry/SpatialEnvelopePairings.lean) | Pair all matching projected whole edges by their actual spatial isometries |

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
| [Unfoldings.Topology.EscapeRays](../Unfoldings/Topology/EscapeRays.lean) | Derive connected planar complements from straight escape rays |
| [Unfoldings.Topology.GraphVertexIdentifications](../Unfoldings/Topology/GraphVertexIdentifications.lean) | Extract actual Jordan curves when graph images identify only vertices |
| [Unfoldings.Topology.JordanBoundarySubset](../Unfoldings/Topology/JordanBoundarySubset.lean) | Derive a disk from connected interior and complement and one Jordan boundary subcurve |
| [Unfoldings.Topology.JordanFilling](../Unfoldings/Topology/JordanFilling.lean) | Identify regular patches from filled Jordan subcurves and avoid countable exceptional points |
| [Unfoldings.Topology.AmbientJordanDisk](../Unfoldings/Topology/AmbientJordanDisk.lean) | Straighten a compact Jordan domain by a homeomorphism of the entire plane |
| [Unfoldings.Topology.PuncturedJordanNeighborhood](../Unfoldings/Topology/PuncturedJordanNeighborhood.lean) | Construct arbitrarily small connected punctured neighborhoods in Jordan disks |
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
The independent [source](../Unfoldings/Source/Abstract.lean) and
[cap](../Unfoldings/Cap/Abstract.lean) abstracts are also checked: public
definitions and theorem statements may reference only their own abstract suite
and Mathlib, including through inferred instances and intermediate definitions.

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
| [Unfoldings.Geometry.ClosedCircleCapsContact](../Unfoldings/Geometry/ClosedCircleCapsContact.lean) | Identify the common named endpoint of horizontally ordered closed circle portions |
| [Unfoldings.Cap.ClosedStripCircleContact](../Unfoldings/Cap/ClosedStripCircleContact.lean) | Classify actual closed strip-circle contacts and recover both physical bank coordinates |
| [Unfoldings.Cap.CompletedBankCoordinateContact](../Unfoldings/Cap/CompletedBankCoordinateContact.lean) | Recover actual closed bank values from equality in a controlling coordinate, including branch jumps |
| [Unfoldings.Cap.NonadjacentClosedSeparation](../Unfoldings/Cap/NonadjacentClosedSeparation.lean) | Exclude all contacts of nonadjacent closed sector images away from the source, including exceptional radii |
| [Unfoldings.Cap.ClosedCircleBankCoordinates](../Unfoldings/Cap/ClosedCircleBankCoordinates.lean) | Recover physical bank endpoints from equality in an actual approached circle coordinate |
| [Unfoldings.Cap.ComponentClosedCircleContact](../Unfoldings/Cap/ComponentClosedCircleContact.lean) | Identify closed strip-contact endpoint coordinates and comparison-bank physical points across an actual component in different sector frames |
| [Unfoldings.Geometry.MonotoneStripLocalCircleCrossing](../Unfoldings/Geometry/MonotoneStripLocalCircleCrossing.lean) | Construct actual open circle slices from a radial crossing along a locally positive-width bank |
| [Unfoldings.Cap.ActiveBankCircleCrossing](../Unfoldings/Cap/ActiveBankCircleCrossing.lean) | Prove every approached active bank point lies on a genuine open circle slice |
| [Unfoldings.Cap.ClosedCirclePinches](../Unfoldings/Cap/ClosedCirclePinches.lean) | Classify all empty-circle closed contacts as actual cut-vertex pinches without removing exceptional radii |
| [Unfoldings.Cap.WaterfallClosedCircleContacts](../Unfoldings/Cap/WaterfallClosedCircleContacts.lean) | Apply the full finite waterfall order to closed contacts and construct both facing bank slices from the actual contact |
| [Unfoldings.Cap.RadialComponentCirclePhysicalBanks](../Unfoldings/Cap/RadialComponentCirclePhysicalBanks.lean) | Retain the exact physical line-map parameters of actual lower and upper component-bank circle matches |
| [Unfoldings.Cap.BoundaryCirclePhysicalAlternative](../Unfoldings/Cap/BoundaryCirclePhysicalAlternative.lean) | Retain physical point equality in the coherent shared-ray circle alternative |
| [Unfoldings.Cap.OuterCirclePhysicalAlternative](../Unfoldings/Cap/OuterCirclePhysicalAlternative.lean) | Classify outer circle endpoints with physical equality or a common actual radial component |
| [Unfoldings.Cap.OuterClosedCircleContact](../Unfoldings/Cap/OuterClosedCircleContact.lean) | Identify the same physical surface point at actual closed outer-bank contacts across adjacent sectors |
| [Unfoldings.Cap.BoundaryRunLateCirclePhysicalCandidate](../Unfoldings/Cap/BoundaryRunLateCirclePhysicalCandidate.lean) | Retain exact physical coordinates of late circle candidates past a maximal boundary-run terminal |
| [Unfoldings.Cap.BoundaryRunSourcePhysicalCandidate](../Unfoldings/Cap/BoundaryRunSourcePhysicalCandidate.lean) | Distinguish strict interior source-bank candidates from actual physical circle crossings |
| [Unfoldings.Cap.BoundaryRunNeighborCirclePhysicalCandidate](../Unfoldings/Cap/BoundaryRunNeighborCirclePhysicalCandidate.lean) | Retain actual physical parameters of neighboring-sector circle bank candidates |
| [Unfoldings.Cap.BoundaryRunClosedCircleContact](../Unfoldings/Cap/BoundaryRunClosedCircleContact.lean) | Identify actual physical endpoints at weak contacts across either disappearing boundary run |
| [Unfoldings.Cap.BoundaryRunClosedConstruction](../Unfoldings/Cap/BoundaryRunClosedConstruction.lean) | Construct actual extreme terminals and identify weak closed contacts across either indexed boundary run |
| [Unfoldings.Cap.AdjacentSurvivorClosedCircleContact](../Unfoldings/Cap/AdjacentSurvivorClosedCircleContact.lean) | Identify one physical surface point at weak contacts between adjacent extreme survivors, including disappearing boundary runs |
| [Unfoldings.Topology.OrderedBankEndpointContacts](../Unfoldings/Topology/OrderedBankEndpointContacts.lean) | Control the entire first and last interval when a different retained bank piece is tested |
| [Unfoldings.Cap.WaterfallClosedCircleExtremeBounds](../Unfoldings/Cap/WaterfallClosedCircleExtremeBounds.lean) | Bound closed sector-circle images and exclude foreign contact at either exposed extreme endpoint |
| [Unfoldings.Cap.AdjacentSectorClosedCircleContact](../Unfoldings/Cap/AdjacentSectorClosedCircleContact.lean) | Identify one physical surface point at arbitrary approached closed contacts across adjacent sectors |
| [Unfoldings.Cap.AcrossSectorClosedCircleContact](../Unfoldings/Cap/AcrossSectorClosedCircleContact.lean) | Assemble adjacent and nonadjacent cases for closed contacts across every pair of distinct waterfall sectors |
| [Unfoldings.Cap.ParentPathCircleContact](../Unfoldings/Cap/ParentPathCircleContact.lean) | Identify physical points at contacts of actual circle endpoints tracked along one completed parent path |
| [Unfoldings.Cap.LeafTailCircleContact](../Unfoldings/Cap/LeafTailCircleContact.lean) | Identify actual physical endpoints at contacts across one geometric leaf tail |
| [Unfoldings.Cap.ContactSeparatorCircleContact](../Unfoldings/Cap/ContactSeparatorCircleContact.lean) | Identify physical endpoints at circle contacts across a constructed shared separator |
| [Unfoldings.Cap.PositiveWidthBankStartContact](../Unfoldings/Cap/PositiveWidthBankStartContact.lean) | Recover an actual starting copy from equality in the controlling bank coordinate |
| [Unfoldings.Cap.TerminalRunStrictLateBoundsContacts](../Unfoldings/Cap/TerminalRunStrictLateBoundsContacts.lean) | Prove strict controlling-coordinate progress for late circle crossings beyond interior terminal copies |
| [Unfoldings.Cap.EmptyStripChainLatePhysicalContact](../Unfoldings/Cap/EmptyStripChainLatePhysicalContact.lean) | Identify physical endpoints once both circle crossings follow a collapsed chain past its terminal |
| [Unfoldings.Geometry.CircleTerminalContact](../Unfoldings/Geometry/CircleTerminalContact.lean) | Prove coincident circle endpoints must both be beyond a strictly interior terminal |
| [Unfoldings.Cap.EmptyStripRunPhysicalContact](../Unfoldings/Cap/EmptyStripRunPhysicalContact.lean) | Identify the same physical point at circle contacts across an arbitrary empty strip run |
| [Unfoldings.Cap.RemovedRunPhysicalContact](../Unfoldings/Cap/RemovedRunPhysicalContact.lean) | Assemble physical contact identification between consecutive survivors across either a separator or a removed run |
| [Unfoldings.Cap.WaterfallCirclePhysicalOrder](../Unfoldings/Cap/WaterfallCirclePhysicalOrder.lean) | Preserve actual physical point identifications in the full finite survivor order using Mathlib lexicographic order |
| [Unfoldings.Cap.WithinSectorClosedCircleContact](../Unfoldings/Cap/WithinSectorClosedCircleContact.lean) | Prove every actual controlled closed contact within one sector has the same physical strip coordinate |
| [Unfoldings.Cap.AllSectorClosedCircleContact](../Unfoldings/Cap/AllSectorClosedCircleContact.lean) | Assemble physical identification for every controlled nonexceptional closed waterfall contact across all sectors |
| [Unfoldings.Cap.ClosedTraceGraphs](../Unfoldings/Cap/ClosedTraceGraphs.lean) | Cover actual closed face copies by compact approached trace graphs, retaining physical coordinates |
| [Unfoldings.Cap.ClosedFaceCircleContact](../Unfoldings/Cap/ClosedFaceCircleContact.lean) | Identify physical points at coincident actual closed-face copies on controlled nonexceptional circles |
| [Unfoldings.Cap.UniformExtendedClosedContact](../Unfoldings/Cap/UniformExtendedClosedContact.lean) | Choose a mesh-independent tilt threshold for local physical identification of actual closed-face contacts outside finitely many image radii |
| [Unfoldings.Geometry.FiniteRadiusContact](../Unfoldings/Geometry/FiniteRadiusContact.lean) | Extend continuous agreement across every nontrivial convex contact set despite finite radius exclusions |
| [Unfoldings.Geometry.NonvertexTriangleContact](../Unfoldings/Geometry/NonvertexTriangleContact.lean) | Prove isolated triangle contacts involve a corner and construct nearby common points at all nonvertex contacts |
| [Unfoldings.Cap.ClosedFaceContactReduction](../Unfoldings/Cap/ClosedFaceContactReduction.lean) | Remove radius exclusions from every nontrivial closed-face contact set and prove foreign physical contacts form a finite set |
| [Unfoldings.Cap.ClosedFaceVertexContact](../Unfoldings/Cap/ClosedFaceVertexContact.lean) | Reduce every foreign physical closed-face contact to a corner with no excluded radii |
| [Unfoldings.Cap.UniformExtendedVertexContact](../Unfoldings/Cap/UniformExtendedVertexContact.lean) | Choose a mesh-independent tilt threshold excluding all foreign contacts between nonvertex points, including exceptional radii |
| [Unfoldings.Cap.PrunedSeamContact](../Unfoldings/Cap/PrunedSeamContact.lean) | Prove coincident copies of the same physical nonvertex point are intrinsically equal after restoring flat subtree cuts |
| [Unfoldings.Cap.ClipOriginalPlacementAgreement](../Unfoldings/Cap/ClipOriginalPlacementAgreement.lean) | Normalize one actual roof development to match all original whole-face charts and transfer closed-face contact identification |
| [Unfoldings.Cap.UniformOriginalClosedContact](../Unfoldings/Cap/UniformOriginalClosedContact.lean) | Choose a mesh-independent tilt threshold controlling actual original-face contacts outside finitely many image radii |
| [Unfoldings.Cap.UniformOriginalVertexContact](../Unfoldings/Cap/UniformOriginalVertexContact.lean) | Exclude every foreign contact between original nonvertex points, including exceptional radii, with a mesh-independent tilt threshold |
| [Unfoldings.Cap.ProjectedPointCopyValues](../Unfoldings/Cap/ProjectedPointCopyValues.lean) | Recover actual developed values and classify intrinsic vertices of projected containing-face copies |
| [Unfoldings.Cap.PrunedContactReduction](../Unfoldings/Cap/PrunedContactReduction.lean) | Reduce all self-contacts of the actual pruned development to intrinsic vertices and characterize injectivity by vertex fibers |
| [Unfoldings.Cap.PrunedDevelopmentLocalIsometry](../Unfoldings/Cap/PrunedDevelopmentLocalIsometry.lean) | Prove the actual development obtained by restoring flat cuts is locally isometric throughout its open cut disk |
| [Unfoldings.Cap.VertexContactEdgeUnfolding](../Unfoldings/Cap/VertexContactEdgeUnfolding.lean) | Construct a uniform original-edge cut disk with face-interior nonoverlap, open-disk local isometry, and injectivity off intrinsic vertices |
| [Unfoldings.Cap.ChildBankContactFlatness](../Unfoldings/Cap/ChildBankContactFlatness.lean) | Characterize coincident parent-bank child endpoints by flatness of every proper descendant subtree |
| [Unfoldings.Cap.PrunedVertexCopyUniqueness](../Unfoldings/Cap/PrunedVertexCopyUniqueness.lean) | Identify all intrinsic pruned vertex copies when proper descendant openings are flat, including actual paired child-endpoint contacts |
| [Unfoldings.Geometry.ChainCoordinateMargins](../Unfoldings/Geometry/ChainCoordinateMargins.lean) | Extend uniform edge-coordinate margins to arbitrary height-ordered points of one actual polygonal chain |
| [Unfoldings.Geometry.ClosedChainTracking](../Unfoldings/Geometry/ClosedChainTracking.lean) | Extend tracking along a finite actual chain from open intervals to their closed endpoints |
| [Unfoldings.Cap.ClosedStripIncrementError](../Unfoldings/Cap/ClosedStripIncrementError.lean) | Control increments of actual closed traces through face switches and vertices, with strict progress under physical coordinate margins |
| [Unfoldings.Cap.ClosedStripPathProgress](../Unfoldings/Cap/ClosedStripPathProgress.lean) | Prove both developed coordinates grow strictly along a uniformly margin-controlled actual path |
| [Unfoldings.Cap.ClosedParentPathProgress](../Unfoldings/Cap/ClosedParentPathProgress.lean) | Obtain strict closed-trace progress from actual completed parent paths and their sector directions |
| [Unfoldings.Cap.ClosedBankStrictStartOrder](../Unfoldings/Cap/ClosedBankStrictStartOrder.lean) | Strengthen actual closed bank start bounds to strict progress beyond the first height, including all branch vertices |
| [Unfoldings.Cap.ActiveBankClosedInterval](../Unfoldings/Cap/ActiveBankClosedInterval.lean) | Construct a later active height and an actual closed interval containing both earlier banks |
| [Unfoldings.Cap.TerminalRunClosedLateBounds](../Unfoldings/Cap/TerminalRunClosedLateBounds.lean) | Bound surviving banks beyond an actual collapsed-run terminal at every radius; prove strict bounds at strictly later heights |
| [Unfoldings.Cap.ClosedParentPathBankMatching](../Unfoldings/Cap/ClosedParentPathBankMatching.lean) | Preserve actual named lower and upper parent-bank matching through all closed vertex heights using compact physical-value graphs |
| [Unfoldings.Cap.ClosedParentPathBankContact](../Unfoldings/Cap/ClosedParentPathBankContact.lean) | Identify physical points at closed opposite-bank contacts along one actual parent path with no vertex or circle-radius exclusions |
| [Unfoldings.Cap.ClosedLateRunPhysicalContact](../Unfoldings/Cap/ClosedLateRunPhysicalContact.lean) | Identify late contacts across an actual collapsed strip run at every radius, including all branch endpoints |
| [Unfoldings.Cap.ClosedLeafTailCircleContact](../Unfoldings/Cap/ClosedLeafTailCircleContact.lean) | Identify actual leaf-tail endpoint contacts at every radius using closed parent-bank matching |
| [Unfoldings.Cap.ClosedContactSeparatorCircleContact](../Unfoldings/Cap/ClosedContactSeparatorCircleContact.lean) | Identify physical circle endpoint contacts across a constructed shared separator without removing any vertex radii |
| [Unfoldings.Cap.ClosedStripCircleSection](../Unfoldings/Cap/ClosedStripCircleSection.lean) | Represent actual closed circle sections, including sections collapsed to one pinch point |
| [Unfoldings.Cap.RadialClosedCircleSections](../Unfoldings/Cap/RadialClosedCircleSections.lean) | Construct sections at every approached circle point and prove closed-only circle images are physical singletons |
| [Unfoldings.Cap.ClosedCircleSectionDegeneracy](../Unfoldings/Cap/ClosedCircleSectionDegeneracy.lean) | Prove section bank values are canonical and collapse exactly when the open circle slice is absent |
| [Unfoldings.Cap.ClosedCircleSectionBounds](../Unfoldings/Cap/ClosedCircleSectionBounds.lean) | Bound every approached circle point by its actual closed section, including degenerate sections |
| [Unfoldings.Cap.ClosedSectionCircleContact](../Unfoldings/Cap/ClosedSectionCircleContact.lean) | Classify contacts between weakly ordered closed sections at all radii, including pinch-only sections |
| [Unfoldings.Cap.ClosedCircleSectionLexOrder](../Unfoldings/Cap/ClosedCircleSectionLexOrder.lean) | Preserve physical point labels in the weak endpoint order of genuine and collapsed closed circle sections |
| [Unfoldings.Cap.ClosedCircleAbsenceBounds](../Unfoldings/Cap/ClosedCircleAbsenceBounds.lean) | Prove a strip with no closed circle contact lies strictly inside the circle, without exceptional radii |
| [Unfoldings.Cap.ClosedEmptyCircleTerminalPinch](../Unfoldings/Cap/ClosedEmptyCircleTerminalPinch.lean) | Construct actual terminal pinches inside absent closed circles at every controlled radius |
| [Unfoldings.Cap.ClosedEmptyCircleTerminalCopy](../Unfoldings/Cap/ClosedEmptyCircleTerminalCopy.lean) | Retain the actual containing-face contour copy of each terminal below an absent closed circle |
| [Unfoldings.Cap.ClosedEmptyCircleContinuation](../Unfoldings/Cap/ClosedEmptyCircleContinuation.lean) | Construct actual proper comparison continuations whenever the entire closed circle section is absent |
| [Unfoldings.Cap.ExtendedClosedEmptyCircleContinuations](../Unfoldings/Cap/ExtendedClosedEmptyCircleContinuations.lean) | Derive closed-empty strip continuations from the actual roof geometry without any radius exclusions |
| [Unfoldings.Geometry.ClosedBankOrderLimit](../Unfoldings/Geometry/ClosedBankOrderLimit.lean) | Extend ordered circle bank contacts across finite exceptional radius sets by compactness |
| [Unfoldings.Cap.ClosedSectionBankOrderLimit](../Unfoldings/Cap/ClosedSectionBankOrderLimit.lean) | Extend actual facing-bank order to closed sections at every controlled radius |
| [Unfoldings.Cap.WaterfallClosedSectionOrder](../Unfoldings/Cap/WaterfallClosedSectionOrder.lean) | Order every pair of actual closed waterfall sections, including vertex radii and pinch-only sections |
| [Unfoldings.Cap.ClosedSharedSeparatorPrefixValue](../Unfoldings/Cap/ClosedSharedSeparatorPrefixValue.lean) | Extend actual shared-prefix coherence through terminal pinches without future positive width |
| [Unfoldings.Cap.ClosedSectionTailContact](../Unfoldings/Cap/ClosedSectionTailContact.lean) | Identify physical tail contacts for genuine and collapsed closed circle sections |
| [Unfoldings.Cap.ClosedSectionSeparatorContact](../Unfoldings/Cap/ClosedSectionSeparatorContact.lean) | Identify contacts across a constructed separator even when either closed section is a single pinch |
| [Unfoldings.Cap.ClosedBankPropertyLimit](../Unfoldings/Cap/ClosedBankPropertyLimit.lean) | Preserve closed predicates of actual bank contacts across every finite exceptional radius set |
| [Unfoldings.Cap.TerminalHeightUniqueness](../Unfoldings/Cap/TerminalHeightUniqueness.lean) | Prove permanent approached terminals have one physical height independent of the comparison radius |
| [Unfoldings.Cap.ClosedEmptyCircleRadiusGap](../Unfoldings/Cap/ClosedEmptyCircleRadiusGap.lean) | Prove a compact strip below an absent closed circle has a uniform positive radial gap |
| [Unfoldings.Cap.ClosedBankCircleCrossing](../Unfoldings/Cap/ClosedBankCircleCrossing.lean) | Cross every smaller circle on the actual approached bank below a prescribed endpoint |
| [Unfoldings.Cap.ClosedEmptyCircleRunRadiusGap](../Unfoldings/Cap/ClosedEmptyCircleRunRadiusGap.lean) | Keep a finite disappearing strip run absent from all sufficiently close smaller circles |
| [Unfoldings.Cap.ClosedSectionEarlyRunBounds](../Unfoldings/Cap/ClosedSectionEarlyRunBounds.lean) | Extend both early terminal bounds through vertex radii while preserving actual terminal heights |
| [Unfoldings.Cap.ClosedSectionLateRunBounds](../Unfoldings/Cap/ClosedSectionLateRunBounds.lean) | Track pinch-only closed sections and prove strict late progress from their actual terminal copies |
| [Unfoldings.Geometry.CircleTerminalStrictContact](../Unfoldings/Geometry/CircleTerminalStrictContact.lean) | Force coincident circle endpoints strictly beyond a smaller terminal using early and strict late bounds |
| [Unfoldings.Cap.ClosedSectionRunPhysicalContact](../Unfoldings/Cap/ClosedSectionRunPhysicalContact.lean) | Identify closed-section contacts across a nonempty disappearing strip run at every controlled radius |
| [Unfoldings.Cap.ClosedSectionRemovedRunContact](../Unfoldings/Cap/ClosedSectionRemovedRunContact.lean) | Identify physical contacts across any removed run including the adjacent-separator case |
| [Unfoldings.Cap.WaterfallClosedSectionPhysicalOrder](../Unfoldings/Cap/WaterfallClosedSectionPhysicalOrder.lean) | Preserve physical point labels in the complete closed-section survivor order at all radii |
| [Unfoldings.Cap.WithinSectorAllRadiusContact](../Unfoldings/Cap/WithinSectorAllRadiusContact.lean) | Identify every actual within-sector closed trace contact without excluding any vertex radii |
| [Unfoldings.Topology.ClosedCompactWitness](../Unfoldings/Topology/ClosedCompactWitness.lean) | Project closed conditions through finite families of compact witness spaces |
| [Unfoldings.Cap.ClosedSectionEarlyRunMaxima](../Unfoldings/Cap/ClosedSectionEarlyRunMaxima.lean) | Retain early coordinate bounds at any chosen maximal terminal of a closed-empty run |
| [Unfoldings.Cap.ClosedSectionBoundaryLateCandidate](../Unfoldings/Cap/ClosedSectionBoundaryLateCandidate.lean) | Match a late closed section to its actual radial component bank at every radius |
| [Unfoldings.Cap.ClosedSectionBoundarySourceCandidate](../Unfoldings/Cap/ClosedSectionBoundarySourceCandidate.lean) | Construct source-side component bank candidates for closed sections including terminal pinches |
| [Unfoldings.Cap.ClosedSectionBoundaryNeighborCandidate](../Unfoldings/Cap/ClosedSectionBoundaryNeighborCandidate.lean) | Preserve neighboring actual component-bank parameters through exceptional circle radii |
| [Unfoldings.Cap.ClosedSectionSharedBankMargins](../Unfoldings/Cap/ClosedSectionSharedBankMargins.lean) | Keep both comparison margins for shared-ray closed circle sections |
| [Unfoldings.Cap.ClosedSectionBoundaryRunMargins](../Unfoldings/Cap/ClosedSectionBoundaryRunMargins.lean) | Derive actual candidate comparison margins for closed sections across boundary runs |
| [Unfoldings.Cap.ClosedSectionBoundaryRunContact](../Unfoldings/Cap/ClosedSectionBoundaryRunContact.lean) | Identify physical contacts across upper and lower boundary runs at every controlled radius |
| [Unfoldings.Cap.AcrossSectorAllRadiusContact](../Unfoldings/Cap/AcrossSectorAllRadiusContact.lean) | Identify closed contacts across every pair of distinct sectors without exceptional radii |
| [Unfoldings.Cap.AdjacentClosedSectionSurvivorContact](../Unfoldings/Cap/AdjacentClosedSectionSurvivorContact.lean) | Identify contacts between adjacent-sector closed extreme survivors at every radius |
| [Unfoldings.Cap.AdjacentSectorAllRadiusContact](../Unfoldings/Cap/AdjacentSectorAllRadiusContact.lean) | Identify all actual closed contacts across adjacent sectors including pinch-only sections |
| [Unfoldings.Cap.AllSectorAllRadiusContact](../Unfoldings/Cap/AllSectorAllRadiusContact.lean) | Identify all actual five-sector closed trace contacts at every controlled positive radius |
| [Unfoldings.Cap.ClosedFaceAllRadiusContact](../Unfoldings/Cap/ClosedFaceAllRadiusContact.lean) | Identify the physical points of coincident actual closed face copies at every controlled radius |
| [Unfoldings.Cap.ClosedOuterSectionComponentBank](../Unfoldings/Cap/ClosedOuterSectionComponentBank.lean) | Match actual outer component banks through closed endpoints including coherent seeds |
| [Unfoldings.Cap.ClosedSectionBoundaryRunConstruction](../Unfoldings/Cap/ClosedSectionBoundaryRunConstruction.lean) | Construct actual closed-empty boundary runs and identify contacts with a neighboring outer bank |
| [Unfoldings.Cap.OuterClosedSectionAlternative](../Unfoldings/Cap/OuterClosedSectionAlternative.lean) | Classify facing closed outer bank endpoints by a common point or an actual radial component |
| [Unfoldings.Cap.OuterClosedSectionContact](../Unfoldings/Cap/OuterClosedSectionContact.lean) | Identify weak contacts across facing outer banks without excluding vertex radii |
| [Unfoldings.Cap.SameSectorAllRadiusContact](../Unfoldings/Cap/SameSectorAllRadiusContact.lean) | Identify arbitrary same-sector closed contacts in either physical cell order |
| [Unfoldings.Cap.WaterfallClosedSectionExtremeBounds](../Unfoldings/Cap/WaterfallClosedSectionExtremeBounds.lean) | Bound all closed circle images by the first and last closed section endpoints |
| [Unfoldings.Cap.WaterfallClosedSectionNonempty](../Unfoldings/Cap/WaterfallClosedSectionNonempty.lean) | Prove each controlled sector circle has a surviving closed section |
| [Unfoldings.Geometry.QuadrantCircleCoordinateOrder](../Unfoldings/Geometry/QuadrantCircleCoordinateOrder.lean) | Reverse vertical circle order from weak horizontal order in the positive quadrant |
| [Unfoldings.Geometry.RadialTailSeedHeight](../Unfoldings/Geometry/RadialTailSeedHeight.lean) | Bound radial component seed heights by every later physical position |
| [Unfoldings.Complex.VertexCopyFibers](../Unfoldings/Complex/VertexCopyFibers.lean) | Show that forgetting cuts preserves exactly vertex points and their original vertex labels |
| [Unfoldings.Cap.ClosedContactFibers](../Unfoldings/Cap/ClosedContactFibers.lean) | Identify uncut intrinsic fibers from closed physical face-contact identification |
| [Unfoldings.Cap.UniformExtendedAllRadiusContact](../Unfoldings/Cap/UniformExtendedAllRadiusContact.lean) | Choose a uniform roof tilt threshold identifying all closed contacts including zero radius |
| [Unfoldings.Cap.UniformOriginalAllRadiusContact](../Unfoldings/Cap/UniformOriginalAllRadiusContact.lean) | Identify all coincident original closed face points under a uniform tilt bound |
| [Unfoldings.Cap.PrunedVertexContactFibers](../Unfoldings/Cap/PrunedVertexContactFibers.lean) | Reduce every pruned self-contact to intrinsic copies of the same physical vertex |
| [Unfoldings.Cap.SameOriginalVertexEdgeUnfolding](../Unfoldings/Cap/SameOriginalVertexEdgeUnfolding.lean) | Construct a uniform original-edge unfolding with only same-original-vertex contacts remaining |
| [Unfoldings.Complex.RestoredBankEndpoints](../Unfoldings/Complex/RestoredBankEndpoints.lean) | Identify matching original endpoints after restoring their actual seam |
| [Unfoldings.Topology.CyclicInternalIntervals](../Unfoldings/Topology/CyclicInternalIntervals.lean) | Choose an internal oriented arc between any two points of a cyclic interval |
| [Unfoldings.Cap.ContourExcursion](../Unfoldings/Cap/ContourExcursion.lean) | Integrate actual paired bank displacements along partial subtree excursions |
| [Unfoldings.Cap.VertexExcursions](../Unfoldings/Cap/VertexExcursions.lean) | Construct actual contour prefixes and suffixes between branch copies |
| [Unfoldings.Cap.RestoredParentBankEndpoints](../Unfoldings/Cap/RestoredParentBankEndpoints.lean) | Match both intrinsic endpoints of actual flat parent banks after pruning |
| [Unfoldings.Cap.ContourExcursionFlatness](../Unfoldings/Cap/ContourExcursionFlatness.lean) | Characterize closing subtree excursions by flatness of their selected openings |
| [Unfoldings.Cap.ContourExcursionRestoration](../Unfoldings/Cap/ContourExcursionRestoration.lean) | Identify endpoints of closing excursions in the actual pruned intrinsic quotient |
| [Unfoldings.Cap.InternalVertexContact](../Unfoldings/Cap/InternalVertexContact.lean) | Identify arbitrary coincident contour copies of an original interior vertex |
| [Unfoldings.Complex.BoundaryEndDistinct](../Unfoldings/Complex/BoundaryEndDistinct.lean) | Distinguish the two intrinsic endpoints of any boundary bank using a spatial folding |
| [Unfoldings.Cap.RootSubtreeContour](../Unfoldings/Cap/RootSubtreeContour.lean) | Identify the two actual rim exits of every boundary-root descendant subtree |
| [Unfoldings.Cap.VertexContourExcursion](../Unfoldings/Cap/VertexContourExcursion.lean) | Integrate actual vertex excursions including original rim roots and exclude rim banks |
| [Unfoldings.Cap.VertexExcursionFlatness](../Unfoldings/Cap/VertexExcursionFlatness.lean) | Force every selected opening flat when an arbitrary vertex excursion closes |
| [Unfoldings.Cap.VertexExcursionRestoration](../Unfoldings/Cap/VertexExcursionRestoration.lean) | Identify all closing vertex-excursion endpoints in the actual pruned quotient |
| [Unfoldings.Cap.AllVertexContact](../Unfoldings/Cap/AllVertexContact.lean) | Construct internal excursions and identify every actual same-vertex contour contact |
| [Unfoldings.Cap.PrunedAllVertexContact](../Unfoldings/Cap/PrunedAllVertexContact.lean) | Prove global injectivity of the pruned development from closed physical contact control |
| [Unfoldings.Cap.InjectiveEdgeUnfolding](../Unfoldings/Cap/InjectiveEdgeUnfolding.lean) | Construct globally injective original-edge developments under a uniform acute-cap tilt bound |
| [Unfoldings.Development.SimpleBoundary](../Unfoldings/Development/SimpleBoundary.lean) | Identify the exact footprint frontier of a developed disk as a finite polygonal Jordan curve |
| [Unfoldings.Cap.SimpleEdgeUnfolding](../Unfoldings/Cap/SimpleEdgeUnfolding.lean) | Prove O'Rourke's cap theorem and expose the actual cut disk, embedding, and simple polygon frontier |
| [Unfoldings.Cap.AbstractBridge](../Unfoldings/Cap/AbstractBridge.lean) | Translate independent geometric cap data and polygon statements to the checked implementation |
| [Unfoldings.Cap.Abstract](../Unfoldings/Cap/Abstract.lean) | State the cap theorem using only independent definitions and Mathlib background notions |
| [Unfoldings.Geometry.SpatialTriangle](../Unfoldings/Geometry/SpatialTriangle.lean) | Construct rigid planar coordinates for genuine spatial triangles from their positive Gram determinant |
| [Unfoldings.Geometry.TriangleAffineEquiv](../Unfoldings/Geometry/TriangleAffineEquiv.lean) | Construct the canonical corner-matching affine equivalence of genuine triangles |
| [Unfoldings.Complex.ProjectedEmbedding](../Unfoldings/Complex/ProjectedEmbedding.lean) | Identify intrinsic seam fibers from conforming convex projections and complete geometric pairings |
| [Unfoldings.Examples.Pyramid.Coordinates](../Unfoldings/Examples/Pyramid/Coordinates.lean) | Construct genuine rigid faces of the four-face diamond pyramid |
| [Unfoldings.Examples.Pyramid.Complex](../Unfoldings/Examples/Pyramid/Complex.lean) | Pair the four actual radial pyramid seams and prove their spatial compatibility |
| [Unfoldings.Examples.Pyramid.Projection](../Unfoldings/Examples/Pyramid/Projection.lean) | Prove the exact conforming convex diamond projection of the pyramid faces |
| [Unfoldings.Examples.Pyramid.Embedding](../Unfoldings/Examples/Pyramid/Embedding.lean) | Prove injectivity of the actual intrinsic pyramid projection, including every vertex |
| [Unfoldings.Examples.Pyramid.Normals](../Unfoldings/Examples/Pyramid/Normals.lean) | Verify explicit unit upward supporting normals on the genuine nonflat pyramid |
| [Unfoldings.Examples.Pyramid](../Unfoldings/Examples/Pyramid.lean) | Construct a concrete nonflat convex cap and derive a positive acute margin |
| [Unfoldings.Geometry.SpatialEnvelopeCuts](../Unfoldings/Geometry/SpatialEnvelopeCuts.lean) | Cut whole physical seams and identify every shared projected edge |
| [Unfoldings.Geometry.SpatialEnvelopeAlignment](../Unfoldings/Geometry/SpatialEnvelopeAlignment.lean) | Prescribed line refinements preserve the actual spatial supports and parent triangles |
| [Unfoldings.Geometry.SpatialEnvelopeChordSlopes](../Unfoldings/Geometry/SpatialEnvelopeChordSlopes.lean) | An unchanged open chord forces all active supporting normal slopes to be collinear |
| [Unfoldings.Geometry.SpatialPlaneSlopes](../Unfoldings/Geometry/SpatialPlaneSlopes.lean) | Gnomonic slopes and exact height differences of rigid spatial support planes |
| [Unfoldings.Cap.MatchedBankTracePositiveHeight](../Unfoldings/Cap/MatchedBankTracePositiveHeight.lean) | Matching parent banks requires regular width only at strictly positive heights |
| [Unfoldings.Geometry.SphericalConvex](../Unfoldings/Geometry/SphericalConvex.lean) | Convert closed spherical convex normal regions to closed convex gnomonic selections |
| [Unfoldings.Roof.SphericalSelection](../Unfoldings/Roof/SphericalSelection.lean) | Prove intrinsic disks and Jordan frontiers for spherical normal selections on roofs |
| [Unfoldings.Polyhedron.SupportingNormals](../Unfoldings/Polyhedron/SupportingNormals.lean) | Construct actual outward unit supporting normals for every original face |
| [Unfoldings.Polyhedron.FaceHalfspaces](../Unfoldings/Polyhedron/FaceHalfspaces.lean) | Identify the convex body exactly as the intersection of its original face halfspaces |
| [Unfoldings.Topology.PathFrontier](../Unfoldings/Topology/PathFrontier.lean) | Cross the frontier of a closed set strictly between interior and exterior path endpoints |
| [Unfoldings.Polyhedron.UpperPlanes](../Unfoldings/Polyhedron/UpperPlanes.lean) | Construct genuine projected coordinates and original upward supporting graph planes |
| [Unfoldings.Polyhedron.UpperGraph](../Unfoldings/Polyhedron/UpperGraph.lean) | Construct the exact upper boundary graph over the full convex body projection |
| [Unfoldings.Geometry.NorthFrame](../Unfoldings/Geometry/NorthFrame.lean) | Construct an orthogonal frame for any containing hemisphere |
| [Unfoldings.Geometry.SegmentEquation](../Unfoldings/Geometry/SegmentEquation.lean) | Choose proper affine equations even for collapsed projected edges |
| [Unfoldings.Geometry.SphericalRotation](../Unfoldings/Geometry/SphericalRotation.lean) | Preserve spherical convexity under orthogonal coordinates |
| [Unfoldings.Geometry.SupportedNormalUnique](../Unfoldings/Geometry/SupportedNormalUnique.lean) | Prove uniqueness of unit supporting normals on a rigid face |
| [Unfoldings.Polyhedron.FaceNormalContact](../Unfoldings/Polyhedron/FaceNormalContact.lean) | Identify the normal of any original face with an interior support contact |
| [Unfoldings.Polyhedron.NormalSelection](../Unfoldings/Polyhedron/NormalSelection.lean) | Prove original spherical normal-selection components are intrinsic disks |
| [Unfoldings.Polyhedron.Rotation](../Unfoldings/Polyhedron/Rotation.lean) | Rotate the original polyhedron, supporting normals, and boundary conditions |
| [Unfoldings.Polyhedron.UpperAdjacency](../Unfoldings/Polyhedron/UpperAdjacency.lean) | Identify projected whole-edge adjacency with original seams |
| [Unfoldings.Polyhedron.UpperCover](../Unfoldings/Polyhedron/UpperCover.lean) | Cover the exact body footprint by original upward faces, including the silhouette |
| [Unfoldings.Polyhedron.UpperRoof](../Unfoldings/Polyhedron/UpperRoof.lean) | Construct the complete original upper roof with intrinsic projection injectivity |
| [Unfoldings.Polyhedron.UpperTriangles](../Unfoldings/Polyhedron/UpperTriangles.lean) | Prove conformity, separation, and actual seam completeness of upward triangles |
| [Unfoldings.Convex.BoundaryPotential](../Unfoldings/Convex/BoundaryPotential.lean) | Identify boundary potential and exclude interior slopes on open exterior rays |
| [Unfoldings.Convex.ExteriorRay](../Unfoldings/Convex/ExteriorRay.lean) | Identify exact constant active cells along outward supporting-side rays |
| [Unfoldings.Convex.FiniteClippedExtension](../Unfoldings/Convex/FiniteClippedExtension.lean) | Construct an actual finite polyhedral clipped conjugate |
| [Unfoldings.Convex.FiniteDual](../Unfoldings/Convex/FiniteDual.lean) | Construct finite vertex conjugates and preserve entire original supporting faces |
| [Unfoldings.Convex.FiniteDualFace](../Unfoldings/Convex/FiniteDualFace.lean) | Prove exact primal face domains at interior maximizing slopes |
| [Unfoldings.Convex.FiniteDualPlanes](../Unfoldings/Convex/FiniteDualPlanes.lean) | Partition the finite dual cost over compact slope polygons |
| [Unfoldings.Convex.FiniteDualVertices](../Unfoldings/Convex/FiniteDualVertices.lean) | Show full extension normal cells occur only at original lifted vertices |
| [Unfoldings.Convex.SlopeEnvelope](../Unfoldings/Convex/SlopeEnvelope.lean) | Construct continuous convex compact-slope envelopes and actual maximizing slopes |
| [Unfoldings.Geometry.AffineEnvelopeDomainPartition](../Unfoldings/Geometry/AffineEnvelopeDomainPartition.lean) | Triangulate affine envelopes over independently prescribed compact polygons |
| [Unfoldings.Geometry.MeshDirectionProgress](../Unfoldings/Geometry/MeshDirectionProgress.lean) | Choose original incident edges within half the corner-angle bound of any direction |
| [Unfoldings.Roof.ClippedExtension](../Unfoldings/Roof/ClippedExtension.lean) | Construct the clipped extension of actual original lifted roof vertices |
| [Unfoldings.Roof.ClippedExteriorRay](../Unfoldings/Roof/ClippedExteriorRay.lean) | Prove safe exterior rays avoid all closed selected original triangles |
| [Unfoldings.Roof.ClippedPolyhedral](../Unfoldings/Roof/ClippedPolyhedral.lean) | Construct finite polyhedral roof extensions and exact surviving normal cells |
| [Unfoldings.Roof.ClippedStrictRegion](../Unfoldings/Roof/ClippedStrictRegion.lean) | Identify the strict difference region using full original primal normal cells |
| [Unfoldings.Roof.DualFace](../Unfoldings/Roof/DualFace.lean) | Recover exact original graph heights and domain from finite primal contact hulls |
| [Unfoldings.Roof.Fenchel](../Unfoldings/Roof/Fenchel.lean) | Prove Fenchel equality for original roof normal cells, including rim cones |
| [Unfoldings.Topology.ConvexFrontier](../Unfoldings/Topology/ConvexFrontier.lean) | Keep convex sets inside a region when they avoid its frontier |
| [Unfoldings.Convex.AnnularProgress](../Unfoldings/Convex/AnnularProgress.lean) | Convert an inner slope disk and angular edge choices into uniform potential gains |
| [Unfoldings.Convex.CommonPotential](../Unfoldings/Convex/CommonPotential.lean) | Bound every incoming history using any active slope at a merger |
| [Unfoldings.Convex.ExteriorRayCompatibility](../Unfoldings/Convex/ExteriorRayCompatibility.lean) | Prove a fixed boundary direction assignment prevents open exterior ray crossings |
| [Unfoldings.Convex.PotentialPaths](../Unfoldings/Convex/PotentialPaths.lean) | Telescope changing active slopes on actual polygonal paths |
| [Unfoldings.Geometry.BoundarySupportDirection](../Unfoldings/Geometry/BoundarySupportDirection.lean) | Construct deterministic unit outward supporting directions at boundary slopes |
| [Unfoldings.Geometry.PolygonalLength](../Unfoldings/Geometry/PolygonalLength.lean) | Prove exact edge sums and projected lengths of finite polygonal chains |
| [Unfoldings.Geometry.PositiveSides](../Unfoldings/Geometry/PositiveSides.lean) | Prove distinct positive unit-normal support lines intersect at most once |
| [Unfoldings.Roof.CommonPotentialForest](../Unfoldings/Roof/CommonPotentialForest.lean) | Construct original-edge forests and prove exactly one boundary root per restricted tree |
| [Unfoldings.Roof.CommonPotentialHistories](../Unfoldings/Roof/CommonPotentialHistories.lean) | Bound every actual incoming parent history in the constructed forest |
| [Unfoldings.Roof.CommonPotentialStep](../Unfoldings/Roof/CommonPotentialStep.lean) | Choose quantitatively advancing original edges inside nonconvex selected patches |
| [Unfoldings.Roof.PrimalNormalCone](../Unfoldings/Roof/PrimalNormalCone.lean) | Identify interior primal normal cells and prove rim cells unbounded |
| [Unfoldings.Roof.SelectedStrictRegion](../Unfoldings/Roof/SelectedStrictRegion.lean) | Identify the extension strict region exactly with selected component interiors |
| [Unfoldings.Convex.ExteriorPlan](../Unfoldings/Convex/ExteriorPlan.lean) | Construct canonical safe exterior rays at prescribed exterior roots |
| [Unfoldings.Convex.ExteriorContacts](../Unfoldings/Convex/ExteriorContacts.lean) | Construct first-contact forests and straight contact-free terminal rays |
| [Unfoldings.Convex.ExteriorPieces](../Unfoldings/Convex/ExteriorPieces.lean) | Prove all first-contact open ray pieces are geometrically disjoint |
| [Unfoldings.Convex.ActiveCell](../Unfoldings/Convex/ActiveCell.lean) | Prove convexity of finite dual costs and actual active normal cells |
| [Unfoldings.Convex.CoerciveEnvelope](../Unfoldings/Convex/CoerciveEnvelope.lean) | Prove compact sublevel sets using an inner slope disk |
| [Unfoldings.Convex.ExteriorProgress](../Unfoldings/Convex/ExteriorProgress.lean) | Prove uniform boundary-potential progress along safe exterior contacts |
| [Unfoldings.Convex.FiniteSlopeModel](../Unfoldings/Convex/FiniteSlopeModel.lean) | Construct actual rigid spatial support planes for finite conjugate models |
| [Unfoldings.Convex.PhysicalModelMesh](../Unfoldings/Convex/PhysicalModelMesh.lean) | Construct conforming physical meshes respecting prescribed finite lines |
| [Unfoldings.Convex.PhysicalNormalCells](../Unfoldings/Convex/PhysicalNormalCells.lean) | Transfer positive intrinsic curvature to full active normal cells |
| [Unfoldings.Geometry.GnomonicCollinearNull](../Unfoldings/Geometry/GnomonicCollinearNull.lean) | Prove collinear gnomonic images have zero solid angle at every tilt |
| [Unfoldings.Geometry.GraphNormalSlope](../Unfoldings/Geometry/GraphNormalSlope.lean) | Recover exact slope parameters from constructed graph-plane normals |
| [Unfoldings.Roof.ClippedPhysicalCurvature](../Unfoldings/Roof/ClippedPhysicalCurvature.lean) | Construct clipped physical models and locate every positive intrinsic curvature vertex |
| [Unfoldings.Roof.CompatiblePotentialHistories](../Unfoldings/Roof/CompatiblePotentialHistories.lean) | Control all incoming histories across attached interior and exterior forests |
| [Unfoldings.Roof.CompatiblePotentialRouting](../Unfoldings/Roof/CompatiblePotentialRouting.lean) | Construct and attach original-edge forests and safe exterior continuations |
| [Unfoldings.Roof.CurvatureNormalInterior](../Unfoldings/Roof/CurvatureNormalInterior.lean) | Force full normal polygons from positive actual intrinsic curvature |
| [Unfoldings.Topology.AttachAscendingParents](../Unfoldings/Topology/AttachAscendingParents.lean) | Attach increasing forests at their roots while preserving original interior parents |
| [Unfoldings.Convex.ExteriorDirectionAngle](../Unfoldings/Convex/ExteriorDirectionAngle.lean) | Bound actual safe exterior direction angles using the slope annulus |
| [Unfoldings.Geometry.AnnularRadialMargin](../Unfoldings/Geometry/AnnularRadialMargin.lean) | Prove positivity of the explicit annular radial margin |
| [Unfoldings.Roof.CompatiblePotentialRadial](../Unfoldings/Roof/CompatiblePotentialRadial.lean) | Prove the explicit radial margin for every actual incoming merger history |
| [Unfoldings.Convex.SegmentProgress](../Unfoldings/Convex/SegmentProgress.lean) | Prove common-potential progress between arbitrary points on oriented edges |
| [Unfoldings.Roof.CompatibleCutCarrier](../Unfoldings/Roof/CompatibleCutCarrier.lean) | Construct actual cut carriers and cover every positive extension curvature vertex |
| [Unfoldings.Convex.AnnularHistoryMargin](../Unfoldings/Convex/AnnularHistoryMargin.lean) | Bound arbitrary incoming paths using the explicit annular radial margin |
| [Unfoldings.Geometry.RadialMarginSegment](../Unfoldings/Geometry/RadialMarginSegment.lean) | Extend a quantitative radial margin along an entire straight edge |
| [Unfoldings.Roof.CompatiblePotentialPaths](../Unfoldings/Roof/CompatiblePotentialPaths.lean) | Control arbitrary partial edges and unbounded terminal tails with one potential |
| [Unfoldings.Roof.CompatiblePotentialWholePaths](../Unfoldings/Roof/CompatiblePotentialWholePaths.lean) | Prove positive radial margins on whole compatible paths and terminal rays |
| [Unfoldings.Roof.ComponentPotentialForest](../Unfoldings/Roof/ComponentPotentialForest.lean) | Restrict the shared original-edge forest to each component with exactly one boundary root |
| [Unfoldings.Complex.SeamEmbedding](../Unfoldings/Complex/SeamEmbedding.lean) | Embed the original whole-seam graph in the uncut intrinsic surface |
| [Unfoldings.Convex.EnvelopeSublevels](../Unfoldings/Convex/EnvelopeSublevels.lean) | Control strict sublevels along segments with a possible boundary endpoint |
| [Unfoldings.Convex.ExteriorEmbedding](../Unfoldings/Convex/ExteriorEmbedding.lean) | Realize actual first-contact segments as an embedded straight rooted forest |
| [Unfoldings.Geometry.ParentSegments](../Unfoldings/Geometry/ParentSegments.lean) | Realize increasing parent forests by disjoint straight segments |
| [Unfoldings.Geometry.StraightGraphLinks](../Unfoldings/Geometry/StraightGraphLinks.lean) | Transfer straight-edge separation and vertex avoidance to oriented links |
| [Unfoldings.Roof.CompatibleCutEmbedding](../Unfoldings/Roof/CompatibleCutEmbedding.lean) | Construct the finite embedded forest of original and exterior parent segments |
| [Unfoldings.Roof.CompatibleCutPieces](../Unfoldings/Roof/CompatibleCutPieces.lean) | Separate all open cut pieces, including full contact-free terminal rays |
| [Unfoldings.Roof.SeamEmbedding](../Unfoldings/Roof/SeamEmbedding.lean) | Identify the roof seam embedding with exact projected straight edges |
| [Unfoldings.Roof.TerminalTruncation](../Unfoldings/Roof/TerminalTruncation.lean) | Truncate terminal rays on one actual envelope level, preserving original parents |
| [Unfoldings.Roof.TruncatedCutEmbedding](../Unfoldings/Roof/TruncatedCutEmbedding.lean) | Construct a bounded embedded forest rooted exactly on its level boundary |
| [Unfoldings.Topology.ParentLeaves](../Unfoldings/Topology/ParentLeaves.lean) | Extend increasing forests by one separately named boundary leaf per old root |
| [Unfoldings.Geometry.LocalPotentialGrowth](../Unfoldings/Geometry/LocalPotentialGrowth.lean) | Derive incident increasing segments from local growth of a convex potential |
| [Unfoldings.Geometry.PrescribedSegments](../Unfoldings/Geometry/PrescribedSegments.lean) | Prove exact whole-edge coverage of arbitrary prescribed physical segments |
| [Unfoldings.Metric.CoerciveGluing](../Unfoldings/Metric/CoerciveGluing.lean) | Prove completeness of finite noncompact gluings using compatible coercive cell heights |
| [Unfoldings.Roof.CompatibleCutMesh](../Unfoldings/Roof/CompatibleCutMesh.lean) | Construct conforming physical meshes respecting all original triangle and cut lines |
| [Unfoldings.Roof.CompatibleMeshForest](../Unfoldings/Roof/CompatibleMeshForest.lean) | Construct supported fine-edge forests and actual flat intrinsic cut disks |
| [Unfoldings.Roof.PotentialCutDisk](../Unfoldings/Roof/PotentialCutDisk.lean) | Derive genuine cut disks and local isometric developments from increasing seam parents |
| [Unfoldings.Roof.PotentialCutForest](../Unfoldings/Roof/PotentialCutForest.lean) | Choose actual increasing seams using local convex-potential growth |
| [Unfoldings.Roof.SpatialEnvelopeProjection](../Unfoldings/Roof/SpatialEnvelopeProjection.lean) | Identify actual physical mesh roof projections and footprints |
| [Unfoldings.Roof.TruncatedCutGrowth](../Unfoldings/Roof/TruncatedCutGrowth.lean) | Prove local common-potential growth through every bounded cut merger |
| [Unfoldings.Roof.TruncatedCutProgress](../Unfoldings/Roof/TruncatedCutProgress.lean) | Prove strict common-potential increase on arbitrary truncated cut subsegments |
| [Unfoldings.Roof.TruncatedCutSegments](../Unfoldings/Roof/TruncatedCutSegments.lean) | Reindex bounded cuts and construct their actual supporting and endpoint constraints |
| [Unfoldings.Geometry.ConvexInteriorRigidity](../Unfoldings/Geometry/ConvexInteriorRigidity.lean) | Extend local isometries on a convex cell interior to one rigid whole-cell motion |
| [Unfoldings.Metric.BoundaryCellDevelopment](../Unfoldings/Metric/BoundaryCellDevelopment.lean) | Derive developed whole-cell rigidity from boundary-only gluing and seam clearance |
| [Unfoldings.Metric.EuclideanLocalHomeomorph](../Unfoldings/Metric/EuclideanLocalHomeomorph.lean) | Derive local homeomorphisms from actual Euclidean charts and local metric isometries |
| [Unfoldings.Metric.FinitePlanarDevelopment](../Unfoldings/Metric/FinitePlanarDevelopment.lean) | Prove a local planar development on finitely many complete cells is globally isometric |
| [Unfoldings.Metric.FlatPlanarGluing](../Unfoldings/Metric/FlatPlanarGluing.lean) | Construct global planar isometries of simply connected flat boundary gluings |
| [Unfoldings.Topology.FiniteCellCovering](../Unfoldings/Topology/FiniteCellCovering.lean) | Derive finite fibers and a covering map from a finite complete isometric cell cover |
| [Unfoldings.Geometry.CommonInitialSubsegments](../Unfoldings/Geometry/CommonInitialSubsegments.lean) | Prove forward subsegments with one affine start overlap in their interiors |
| [Unfoldings.Geometry.HalfOpenStraightGraph](../Unfoldings/Geometry/HalfOpenStraightGraph.lean) | Separate directed half-open edges when every vertex has at most one outgoing edge |
| [Unfoldings.Geometry.OrientedSubsegments](../Unfoldings/Geometry/OrientedSubsegments.lean) | Retain coarse edge parameters and prove forward fine edges are unique |
| [Unfoldings.Geometry.PrescribedSubedge](../Unfoldings/Geometry/PrescribedSubedge.lean) | Use supporting-line constraints to place a whole fine edge in one prescribed segment |
| [Unfoldings.Roof.CompatibleMeshOrientation](../Unfoldings/Roof/CompatibleMeshOrientation.lean) | Orient fine cut seams inside unique coarse compatible segments |
| [Unfoldings.Roof.CompatibleMeshPaths](../Unfoldings/Roof/CompatibleMeshPaths.lean) | Transfer actual fine parent histories and their length bounds to the original routing |
| [Unfoldings.Roof.CompatibleMeshRetention](../Unfoldings/Roof/CompatibleMeshRetention.lean) | Prove selected fine cuts equal exactly the prescribed whole-seam cut network |
| [Unfoldings.Roof.CompatibleMeshSubedges](../Unfoldings/Roof/CompatibleMeshSubedges.lean) | Identify the single prescribed cut segment containing each fine cut edge |
| [Unfoldings.Roof.PrescribedCompatibleCutDisk](../Unfoldings/Roof/PrescribedCompatibleCutDisk.lean) | Construct flat intrinsic disks and local developments for the exact prescribed cuts |
| [Unfoldings.Roof.SeamSegments](../Unfoldings/Roof/SeamSegments.lean) | Identify a closed projected linked segment with its actual whole seam edge |
| [Unfoldings.Geometry.ChordPerturbation](../Unfoldings/Geometry/ChordPerturbation.lean) | Transfer radial margins and length constants through relative chord errors |
| [Unfoldings.Geometry.ComplexRotation](../Unfoldings/Geometry/ComplexRotation.lean) | Construct real linear isometries for complex plane rotations |
| [Unfoldings.Geometry.HeadingChordError](../Unfoldings/Geometry/HeadingChordError.lean) | Bound aligned chord errors by real heading errors and actual path length |
| [Unfoldings.Geometry.HeadingPerturbation](../Unfoldings/Geometry/HeadingPerturbation.lean) | Prove quantitative radial and length bounds under mesh-independent heading perturbations |
| [Unfoldings.Geometry.SuffixOpening](../Unfoldings/Geometry/SuffixOpening.lean) | Rotate actual chain suffixes about current hinges while retaining translations |
| [Unfoldings.Geometry.OpeningBudget](../Unfoldings/Geometry/OpeningBudget.lean) | Bound accumulated true suffix openings and their radial margin losses |
| [Unfoldings.Geometry.OpeningCurvature](../Unfoldings/Geometry/OpeningCurvature.lean) | Control heading oscillation by original curvatures spent once |
| [Unfoldings.Geometry.ChainInterval](../Unfoldings/Geometry/ChainInterval.lean) | Retain exact contiguous subchains and their original edge vectors |
| [Unfoldings.Geometry.HeadingRadialChain](../Unfoldings/Geometry/HeadingRadialChain.lean) | Preserve whole-chain radial monotonicity under uniform heading errors |
| [Unfoldings.Geometry.PolygonalRay](../Unfoldings/Geometry/PolygonalRay.lean) | Represent actual finite polygonal prefixes with unbounded straight tails |
| [Unfoldings.Geometry.PolygonalRayEmbedding](../Unfoldings/Geometry/PolygonalRayEmbedding.lean) | Derive proper embedded half-lines from source-radial tests |
| [Unfoldings.Geometry.PolygonalRayOpening](../Unfoldings/Geometry/PolygonalRayOpening.lean) | Rotate actual infinite bank suffixes and retain quantitative radial bounds |
| [Unfoldings.Geometry.RadialTwist](../Unfoldings/Geometry/RadialTwist.lean) | Construct whole-plane homeomorphisms from continuous rotations on concentric circles |
| [Unfoldings.Geometry.PolygonalRayFrame](../Unfoldings/Geometry/PolygonalRayFrame.lean) | Straighten actual radial polygonal banks by ambient plane homeomorphisms |
| [Unfoldings.Geometry.PolygonalRotationGap](../Unfoldings/Geometry/PolygonalRotationGap.lean) | Construct source-rotation gaps with exact bank frontier and source-only bank intersection |
| [Unfoldings.Geometry.UnboundedArrangement](../Unfoldings/Geometry/UnboundedArrangement.lean) | Decompose unbounded regular closed regions into finite closed convex chamber cells |
| [Unfoldings.Cone.SectorFrontier](../Unfoldings/Cone/SectorFrontier.lean) | Identify a sector frontier with exactly its two closed boundary rays |
| [Unfoldings.Geometry.ComplexLineEquation](../Unfoldings/Geometry/ComplexLineEquation.lean) | Construct proper supporting equations for entire complex lines, including degenerate segments |
| [Unfoldings.Geometry.PolygonalRayEquations](../Unfoldings/Geometry/PolygonalRayEquations.lean) | Construct finite proper affine supports for whole polygonal banks and their infinite tails |
| [Unfoldings.Geometry.SourceRotation](../Unfoldings/Geometry/SourceRotation.lean) | Represent actual source-fixed rotations as affine isometric equivalences |
| [Unfoldings.Geometry.PolygonalGapCells](../Unfoldings/Geometry/PolygonalGapCells.lean) | Construct finite closed full-dimensional convex cells with disjoint interiors covering rotation gaps |
| [Unfoldings.Geometry.ChainSplit](../Unfoldings/Geometry/ChainSplit.lean) | Split actual closed chain carriers at arbitrary retained vertices |
| [Unfoldings.Geometry.PolygonalRaySuffix](../Unfoldings/Geometry/PolygonalRaySuffix.lean) | Retain exact infinite suffixes and derive their hinge-centered radial tests |
| [Unfoldings.Geometry.ChainAffineMap](../Unfoldings/Geometry/ChainAffineMap.lean) | Retain entire polygonal chain carriers under affine maps |
| [Unfoldings.Geometry.PolygonalRayAffineMap](../Unfoldings/Geometry/PolygonalRayAffineMap.lean) | Retain complete polygonal banks and actual infinite tails under affine maps |
| [Unfoldings.Geometry.HingeGap](../Unfoldings/Geometry/HingeGap.lean) | Identify actual hinge gap banks with the old and moved infinite suffixes |
| [Unfoldings.Geometry.RaySplitRadius](../Unfoldings/Geometry/RaySplitRadius.lean) | Separate kept prefixes from infinite suffixes by actual source-radius ordering |
| [Unfoldings.Geometry.RotationGapSweep](../Unfoldings/Geometry/RotationGapSweep.lean) | Cover each rotation gap by its actual intermediate rotated banks |
| [Unfoldings.Geometry.HingeGapPrefix](../Unfoldings/Geometry/HingeGapPrefix.lean) | Prove a radial hinge gap meets its unchanged prefix only at its hinge |
| [Unfoldings.Geometry.SingleOpeningRadial](../Unfoldings/Geometry/SingleOpeningRadial.lean) | Control every partial opening angle with one quantitative radial budget |
| [Unfoldings.Geometry.SmallHingeGap](../Unfoldings/Geometry/SmallHingeGap.lean) | Derive actual gap-prefix clearance from original-bank length and radial margins |
| [Unfoldings.Metric.FiniteCompleteCover](../Unfoldings/Metric/FiniteCompleteCover.lean) | Prove completeness from a finite isometric cover by complete spaces |
| [Unfoldings.Metric.PolygonalClosedCover](../Unfoldings/Metric/PolygonalClosedCover.lean) | Identify intrinsic topology and completeness of finite closed convex-cell regions |
| [Unfoldings.Geometry.RotationGapMetric](../Unfoldings/Geometry/RotationGapMetric.lean) | Construct complete intrinsic gap metrics, finite route distances and exact sector topology |
| [Unfoldings.Geometry.WeightedHeadingBudget](../Unfoldings/Geometry/WeightedHeadingBudget.lean) | Bound length-weighted future polar variation by a finite Fubini argument |
| [Unfoldings.Geometry.HeadingSpeedError](../Unfoldings/Geometry/HeadingSpeedError.lean) | Control bank chords with simultaneous heading and intrinsic-speed errors |
| [Unfoldings.Geometry.ChordRotationControl](../Unfoldings/Geometry/ChordRotationControl.lean) | Transfer aligned chord bounds to actual bank radial margins and length constants |
| [Unfoldings.Geometry.RadialBlockError](../Unfoldings/Geometry/RadialBlockError.lean) | Prove the radial-block chord estimate without a global heading cone |
| [Unfoldings.Geometry.RadialBlockBounds](../Unfoldings/Geometry/RadialBlockBounds.lean) | Derive explicit radial margins and length constants from weighted block comparisons |
| [Unfoldings.Geometry.RadialPolarVariation](../Unfoldings/Geometry/RadialPolarVariation.lean) | Bound true link polar sweep by radial progress with the exact square-root factor |
| [Unfoldings.Geometry.ChainPolarVariation](../Unfoldings/Geometry/ChainPolarVariation.lean) | Identify true chain prefix lengths and bound length-weighted actual polar variation |
| [Unfoldings.Geometry.RadialGraphArc](../Unfoldings/Geometry/RadialGraphArc.lean) | Construct a simple interval parametrization of entire source-radial polygonal carriers |
| [Unfoldings.Topology.PathJordanArc](../Unfoldings/Topology/PathJordanArc.lean) | Convert actual injective paths to named-endpoint Jordan arcs |
| [Unfoldings.Geometry.RadialClosureSegments](../Unfoldings/Geometry/RadialClosureSegments.lean) | Prove exact disk and half-plane separation of radial closing segments |
| [Unfoldings.Geometry.RadialClosureJordan](../Unfoldings/Geometry/RadialClosureJordan.lean) | Construct Jordan closures from actual radial paths and supporting-half-plane geometry |
| [Unfoldings.Geometry.WedgeClosingDirection](../Unfoldings/Geometry/WedgeClosingDirection.lean) | Construct outward directions beyond a supporting side of every pointed wedge |
| [Unfoldings.Geometry.RadialWedgeClosure](../Unfoldings/Geometry/RadialWedgeClosure.lean) | Construct the actual three-segment Jordan closure for radially ordered pointed wedges |
| [Unfoldings.Geometry.ConvexCellRegion](../Unfoldings/Geometry/ConvexCellRegion.lean) | Construct exact region face selections when full convex-cell interiors avoid the frontier |
| [Unfoldings.Topology.ClosedJordanDomain](../Unfoldings/Topology/ClosedJordanDomain.lean) | Construct compact regular Jordan fillings, exact frontiers and ambient disk homeomorphisms |
| [Unfoldings.Topology.IncidentCellNeighborhood](../Unfoldings/Topology/IncidentCellNeighborhood.lean) | Derive whole neighborhoods from the finitely many closed cells incident at a point |
| [Unfoldings.Geometry.JordanTriangleSelection](../Unfoldings/Geometry/JordanTriangleSelection.lean) | Construct exact whole-triangle fillings for respected Jordan curves |
| [Unfoldings.Cap.JordanFaceSelection](../Unfoldings/Cap/JordanFaceSelection.lean) | Select actual projected cap faces and prove full-star inclusion inside Jordan fillings |
| [Unfoldings.Cap.JordanRegionalAngles](../Unfoldings/Cap/JordanRegionalAngles.lean) | Identify actual Jordan-boundary fan excess and bound it by total cap curvature |
| [Unfoldings.Cap.JordanAngleBalance](../Unfoldings/Cap/JordanAngleBalance.lean) | Prove exact geometric boundary-angle excess equals actual curvature strictly inside the Jordan filling |
| [Unfoldings.Geometry.ConstraintInteriors](../Unfoldings/Geometry/ConstraintInteriors.lean) | Derive strict interior constraint signs and actual curve avoidance for line-respecting meshes |
| [Unfoldings.Geometry.PolygonalClosureEquations](../Unfoldings/Geometry/PolygonalClosureEquations.lean) | Construct proper finite equations for every actual polygonal closure link |
| [Unfoldings.Roof.PolygonalClosureMesh](../Unfoldings/Roof/PolygonalClosureMesh.lean) | Construct respecting physical closure meshes and their exact geometric Jordan angle balance |
| [Unfoldings.Cap.JordanIntrinsicDisk](../Unfoldings/Cap/JordanIntrinsicDisk.lean) | Construct the actual selected intrinsic Jordan disk with injective geometric projection |
| [Unfoldings.Complex.FaceRestrictionVertices](../Unfoldings/Complex/FaceRestrictionVertices.lean) | Include restricted vertex classes and recover actual selected intrinsic corner angles |
| [Unfoldings.Complex.FaceRestrictionWeights](../Unfoldings/Complex/FaceRestrictionWeights.lean) | Recover arbitrary original corner weights from actual restricted vertex fibers |
| [Unfoldings.Cap.JordanFanAngles](../Unfoldings/Cap/JordanFanAngles.lean) | Identify intrinsic Jordan vertex fans with exactly their selected original corner contributions |

| [`JordanBoundary`](../Unfoldings/Cap/JordanBoundary.lean) | Exact intrinsic and geometric Jordan boundary; constructed contour |
| [`JordanVertexEnumeration`](../Unfoldings/Cap/JordanVertexEnumeration.lean) | Bijections with original geometric filling and boundary vertices |
| [`JordanContourTurns`](../Unfoldings/Cap/JordanContourTurns.lean) | Exact ordered intrinsic/projected boundary turn comparison |
| [`JordanBankTurnBounds`](../Unfoldings/Cap/JordanBankTurnBounds.lean) | One-sided bank error from actual closure curvature and connector error |

| [`RegionalCornerPartition`](../Unfoldings/Complex/RegionalCornerPartition.lean) | Exact complementary and disjoint face-star partitions |
| [`ComplementaryBankTurns`](../Unfoldings/Cap/ComplementaryBankTurns.lean) | Opposite bank turn errors differ by original path curvature |

| [`Complex/BoundaryRolling`](../Unfoldings/Complex/BoundaryRolling.lean) | Canonical rolled bank chain from actual intrinsic lengths and real fan turns |
| [`Development/BoundaryRolling`](../Unfoldings/Development/BoundaryRolling.lean) | Exact agreement with developed bank edges and vertices; closure from development |

| [`Complex/AffineProjection`](../Unfoldings/Complex/AffineProjection.lean) | Separate projected metric complex with inherited seam names |
| [`Complex/AffineProjectionClasses`](../Unfoldings/Complex/AffineProjectionClasses.lean) | Exact preservation of retained corner classes |
| [`Complex/AffineProjectionAngles`](../Unfoldings/Complex/AffineProjectionAngles.lean) | Actual projected corner-angle sums |
| [`Complex/AffineProjectionBoundary`](../Unfoldings/Complex/AffineProjectionBoundary.lean) | Same directed banks, vertex mates and contour order |
| [`Development/AffineProjection`](../Unfoldings/Development/AffineProjection.lean) | Global identity development from actual separated projected faces |

| [`Cap/JordanRolling`](../Unfoldings/Cap/JordanRolling.lean) | Actual intrinsic and projected Jordan bank rolling; exact real heading discrepancies |
| [`Cap/JordanRollingBounds`](../Unfoldings/Cap/JordanRollingBounds.lean) | Curvature and closing-link bounds for actual contiguous bank headings |
| [`Cap/BankLengthProjection`](../Unfoldings/Cap/BankLengthProjection.lean) | Normal-dependent contraction of actual original bank lengths |
| [`Cap/JordanBankStretch`](../Unfoldings/Cap/JordanBankStretch.lean) | Exact intrinsic/projected bank edge speed and heading factors |

| [`Geometry/GenericRadialSource`](../Unfoldings/Geometry/GenericRadialSource.lean) | Generic source perturbations preserving radial progress and strict pointed wedges |
| [`Geometry/LinearPathBounds`](../Unfoldings/Geometry/LinearPathBounds.lean) | Vertex support bounds imply support on the entire actual chain |
| [`Geometry/GenericWedgeClosure`](../Unfoldings/Geometry/GenericWedgeClosure.lean) | Generic closing points for actual radial-wedge Jordan closures |
| [`Geometry/SegmentLineAvoidance`](../Unfoldings/Geometry/SegmentLineAvoidance.lean) | Proper segment equations exclude exceptional connector incidences |
| [`Geometry/VertexAvoidingWedgeClosure`](../Unfoldings/Geometry/VertexAvoidingWedgeClosure.lean) | Actual Jordan closures with all three closing links avoiding prescribed vertices |

| [`Geometry/ChainEndTrimming`](../Unfoldings/Geometry/ChainEndTrimming.lean) | Trim actual terminal links and retain all intermediate original corners |
| [`Geometry/ChainEndTrimPaths`](../Unfoldings/Geometry/ChainEndTrimPaths.lean) | Exact subparametrizations preserve carrier order and radial progress |
| [`Geometry/ChainEndTrimTurns`](../Unfoldings/Geometry/ChainEndTrimTurns.lean) | Genuine trims preserve all original directions, turns and complex edge factors |
| [`Geometry/GenericEndTrimming`](../Unfoldings/Geometry/GenericEndTrimming.lean) | Choose interior terminal fractions avoiding any finite prescribed vertex set |

| [`Geometry/StrictRadialTrimming`](../Unfoldings/Geometry/StrictRadialTrimming.lean) | Strict original radial progress survives genuine endpoint trimming |
| [`Geometry/SegmentExtendedAvoidance`](../Unfoldings/Geometry/SegmentExtendedAvoidance.lean) | Entire extended connector lines avoid prescribed exceptional points |
| [`Geometry/GenericBankClosure`](../Unfoldings/Geometry/GenericBankClosure.lean) | Construct actual trimmed Jordan closures with three completely regular closing lines |

| [`Development/SingleSeam`](../Unfoldings/Development/SingleSeam.lean) | Construct the genuine outward development retaining one original seam |
| [`Cap/IntrinsicSectionTurns`](../Unfoldings/Cap/IntrinsicSectionTurns.lean) | Actual vertex-avoiding straight-section intrinsic turns total at most twice the tilt |
| [`Cap/IntrinsicSectionTurnAgreement`](../Unfoldings/Cap/IntrinsicSectionTurnAgreement.lean) | Hinge rigidity identifies the intrinsic turn in every retained development |

| [`Topology/PairedInvolutionExtension`](../Unfoldings/Topology/PairedInvolutionExtension.lean) | Extend any prescribed finite pairing chain to its full cycle |
| [`Topology/FinitePrefixSum`](../Unfoldings/Topology/FinitePrefixSum.lean) | Exact prefix sums under finite index inclusions |
| [`Geometry/ClosedRayChain`](../Unfoldings/Geometry/ClosedRayChain.lean) | Complementary closed-chain angular length bounds endpoint angle |
| [`Polyhedron/ComplementaryLinkAngles`](../Unfoldings/Polyhedron/ComplementaryLinkAngles.lean) | Original complementary vertex corners bound the spatial endpoint angle |
| [`Polyhedron/LinkFanTurn`](../Unfoldings/Polyhedron/LinkFanTurn.lean) | Actual convex one-sided fan exterior turns contract spatial bends |
| [`Complex/FaceRestrictionLinks`](../Unfoldings/Complex/FaceRestrictionLinks.lean) | Embed actual restricted corner chains in their original full link |
| [`Polyhedron/RestrictedBoundaryTurns`](../Unfoldings/Polyhedron/RestrictedBoundaryTurns.lean) | Spatial bend bound for actual restricted boundary fans, including reflex fans |
| [`Cap/JordanVertexTurnBound`](../Unfoldings/Cap/JordanVertexTurnBound.lean) | Spatial bend bound for every actual intrinsic Jordan boundary vertex |

| [`Cap/ProjectedPartialLink`](../Unfoldings/Cap/ProjectedPartialLink.lean) | Actual selected and complementary projected fan angle bounds |
| [`Complex/LinkCornerWeights`](../Unfoldings/Complex/LinkCornerWeights.lean) | Exact arbitrary original corner-weight sums in an actual link order |
| [`Cap/RestrictedStraightTurns`](../Unfoldings/Cap/RestrictedStraightTurns.lean) | Straight boundary fans have projected angle pi and spatially controlled turn error |
| [`Cap/JordanStraightVertex`](../Unfoldings/Cap/JordanStraightVertex.lean) | Actual straight Jordan contour errors contract spatial bends |

| [`Polyhedron/BoundaryDirections`](../Unfoldings/Polyhedron/BoundaryDirections.lean) | Actual folded bank vectors and adjacent physical boundary positions |
| [`Cap/BoundarySectionTrace`](../Unfoldings/Cap/BoundarySectionTrace.lean) | Actual straight boundary sections have total fan-turn error at most twice tilt |
| [`Cap/BoundarySectionConstruction`](../Unfoldings/Cap/BoundarySectionConstruction.lean) | Construct physical straight boundary traces from actual projected contour coordinates |
| [`Cap/JordanStraightSection`](../Unfoldings/Cap/JordanStraightSection.lean) | Uniform contour error bound on actual ordered straight Jordan intervals |

| [`Complex/BoundaryContourRotation`](../Unfoldings/Complex/BoundaryContourRotation.lean) | Reindex actual directed boundary contours while preserving every bank |
| [`Cap/CyclicBoundarySection`](../Unfoldings/Cap/CyclicBoundarySection.lean) | Straight section fan error bounds across the cyclic contour origin |
| [`Geometry/PlanarAngleArea`](../Unfoldings/Geometry/PlanarAngleArea.lean) | Exact planar angular area from the Gram determinant |
| [`Geometry/LinearAngleSine`](../Unfoldings/Geometry/LinearAngleSine.lean) | Near-unit sine ratio from actual planar length contraction |
| [`Geometry/RelativeSineError`](../Unfoldings/Geometry/RelativeSineError.lean) | Relative angular error from additive and sine ratio estimates |
| [`Cap/RelativeFaceAngleError`](../Unfoldings/Cap/RelativeFaceAngleError.lean) | Uniform relative face and corner projection-angle distortion |
| [`Cap/RegionalProjectionError`](../Unfoldings/Cap/RegionalProjectionError.lean) | Selected fan error bounded by its projected angle, independently of valence |
| [`Cap/JordanCornerError`](../Unfoldings/Cap/JordanCornerError.lean) | Uniform actual Jordan corner errors without generic incidence assumptions |

| [`Geometry/IntervalVariationPacking`](../Unfoldings/Geometry/IntervalVariationPacking.lean) | Total real variation from actual disjoint interval packing |
| [`Cap/ActiveSectionVariation`](../Unfoldings/Cap/ActiveSectionVariation.lean) | Active support faces at distinct section contacts have total bend at most twice tilt |
| [`Geometry/OppositeRayAngles`](../Unfoldings/Geometry/OppositeRayAngles.lean) | Opposite real scalar rays give exact straight angles and spatial bends |
| [`Cap/RestrictedSectionDirections`](../Unfoldings/Cap/RestrictedSectionDirections.lean) | Identify physical bank rays with their actual active support-plane directions |
| [`Cap/RestrictedSectionSum`](../Unfoldings/Cap/RestrictedSectionSum.lean) | Sum straight boundary fan errors without ordering or adjacency hypotheses |
| [`Cap/JordanSectionSet`](../Unfoldings/Cap/JordanSectionSet.lean) | Bound arbitrary selected collinear Jordan vertex sets independently of contour enumeration |

| [`Complex/DirectedBoundaryPath`](../Unfoldings/Complex/DirectedBoundaryPath.lean) | Genuine directed affine bank paths with exact physical positions |
| [`Cap/RestrictedBankSegments`](../Unfoldings/Cap/RestrictedBankSegments.lean) | Actual projected boundary banks at one vertex have distinct positive rays |
| [`Geometry/LocalLineSegment`](../Unfoldings/Geometry/LocalLineSegment.lean) | Local line containment determines the whole genuine segment direction |
| [`Cap/JordanLocalSection`](../Unfoldings/Cap/JordanLocalSection.lean) | Derive opposite bank rays and error sums from actual local boundary straightness |
| [`Cap/JordanClosingLink`](../Unfoldings/Cap/JordanClosingLink.lean) | Actual closing-link error at most twice tilt from a closed geometric curve decomposition |

| [`Topology/FiniteWeightedCover`](../Unfoldings/Topology/FiniteWeightedCover.lean) | Nonnegative finite covering weight bounds allowing overlaps |
| [`Cap/JordanBankPositions`](../Unfoldings/Cap/JordanBankPositions.lean) | Injective actual Jordan contour positions and geometric corner counts |
| [`Cap/GeometricBankTurnComparison`](../Unfoldings/Cap/GeometricBankTurnComparison.lean) | Curvature plus derived straight-link and geometric-corner bank-turn bounds |

| [`Geometry/RadialClosingLinks`](../Unfoldings/Geometry/RadialClosingLinks.lean) | Actual radial closing segments have only prescribed corner contacts |
| [`Cap/RadialBankTurnComparison`](../Unfoldings/Cap/RadialBankTurnComparison.lean) | Derived actual radial bank error bound: curvature plus six times tilt plus relative corner error |
| [`Cap/RadialBankThreshold`](../Unfoldings/Cap/RadialBankThreshold.lean) | One uniform positive tilt makes every actual radial bank turn error arbitrarily small |
| [`Roof/ClosureBankComparison`](../Unfoldings/Roof/ClosureBankComparison.lean) | Apply the uniform bank bound to the actual constructed physical closure mesh |

| [`Geometry/LocalHeadingBudget`](../Unfoldings/Geometry/LocalHeadingBudget.lean) | Chain local polar windows into a weighted real heading bound with no global cone |
| [`Geometry/LocalRadialBlocks`](../Unfoldings/Geometry/LocalRadialBlocks.lean) | Derive actual chord, radial-margin and length bounds from local bank comparisons |
| [`Geometry/RayWindowAngle`](../Unfoldings/Geometry/RayWindowAngle.lean) | Actual source-ray angles bounded by polar variation strictly between terminal links |

| [`Geometry/AxisQuadrantFrame`](../Unfoldings/Geometry/AxisQuadrantFrame.lean) | One rigid frame puts an entire quarter-angle neighborhood in an open quadrant |
| [`Geometry/OpenEndTrimming`](../Unfoldings/Geometry/OpenEndTrimming.lean) | Genuine endpoint trims enter an open set containing every internal original vertex |
| [`Geometry/RayWindowTrimming`](../Unfoldings/Geometry/RayWindowTrimming.lean) | Construct a pointed quadrant and genuine trims from a short actual ray-angle sum |
| [`Geometry/RayWindowClosure`](../Unfoldings/Geometry/RayWindowClosure.lean) | Construct supported Jordan closing links from a short radial window |

| [`Complex/SubdivisionCornerAngles`](../Unfoldings/Complex/SubdivisionCornerAngles.lean) | Exact refinement angle sums preserve individual retained vertex fans |

| [`Roof/CompletionSubdivisionAngles`](../Unfoldings/Roof/CompletionSubdivisionAngles.lean) | Actual completion subdivision preserves every original cut vertex fan |

| [`Geometry/TriangleStraightBoundary`](../Unfoldings/Geometry/TriangleStraightBoundary.lean) | Distinct genuine boundary rays at triangle noncorners form angle pi |
| [`Cap/TriangularFootprintStraightAngles`](../Unfoldings/Cap/TriangularFootprintStraightAngles.lean) | Exact straight projected fans on open sides of triangular footprints |
| [`Roof/CompletionFaceStraightAngles`](../Unfoldings/Roof/CompletionFaceStraightAngles.lean) | Flat full and half-plane fans at inserted original-face patch vertices |
| [`Roof/CompletionInsertedAngles`](../Unfoldings/Roof/CompletionInsertedAngles.lean) | Inserted original cut-bank vertices have zero real exterior rolling turn |
| [`Complex/SubdivisionWeightedAngles`](../Unfoldings/Complex/SubdivisionWeightedAngles.lean) | Arbitrary original face weights and regional fan angles survive refinement |
| [`Roof/CompletionBankSubdivision`](../Unfoldings/Roof/CompletionBankSubdivision.lean) | Whole original cut banks are exactly covered by genuine fine bank images in the cut metric |

| [`Topology/FiniteIntervalPartition`](../Unfoldings/Topology/FiniteIntervalPartition.lean) | Exact increasing order of all nondegenerate intervals in a finite partition |
| [`Geometry/SegmentPartitionOrder`](../Unfoldings/Geometry/SegmentPartitionOrder.lean) | Construct a directed segment subdivision using every genuine fine segment once |
| [`Roof/CompletionBankOrder`](../Unfoldings/Roof/CompletionBankOrder.lean) | Actual physical fine bank edges form an exact ordered segment partition |
| [`Roof/CompletionDirectedBank`](../Unfoldings/Roof/CompletionDirectedBank.lean) | The ordered fine edges follow the actual intrinsic boundary successor |
| [`Complex/BoundaryChainRolling`](../Unfoldings/Complex/BoundaryChainRolling.lean) | Roll actual finite bank chains using real turns and original edge lengths |
| [`Roof/CompletionBankRolling`](../Unfoldings/Roof/CompletionBankRolling.lean) | Construct actual old cut-bank refinements with zero extra unreduced heading |

| [`Topology/CyclicRegionTurns`](../Unfoldings/Topology/CyclicRegionTurns.lean) | Exact additive turn cancellation across actual entering and leaving banks |
| [`Topology/FiniteCyclicTurns`](../Unfoldings/Topology/FiniteCyclicTurns.lean) | Identify finite unreduced heading prefixes with selected cyclic region turn sums |
| [`Complex/SubtreeRolling`](../Unfoldings/Complex/SubtreeRolling.lean) | Actual opposite parent banks have real reversed-exit heading equal to subtree curvature |
| [`Cap/SubtreeRealHeading`](../Unfoldings/Cap/SubtreeRealHeading.lean) | Bound actual real subtree bank holonomy between zero and total cap curvature |

| [`Topology/SubtreePotentialWeights`](../Unfoldings/Topology/SubtreePotentialWeights.lean) | Exact root-path telescoping of nested subtree weights and parent membership changes |
| [`Cap/SubtreeBankPotential`](../Unfoldings/Cap/SubtreeBankPotential.lean) | Actual real opposite-bank heading potentials are bounded by original cap curvature |

| [`Convex/ActiveRayProgress`](../Unfoldings/Convex/ActiveRayProgress.lean) | Actual active slopes preserve forward support at arbitrary partial ray points |
| [`Geometry/AnnularFineMargin`](../Unfoldings/Geometry/AnnularFineMargin.lean) | Choose a positive mesh-independent routing width for the fine-vertex margin |
| [`Roof/CompatibleFineMargins`](../Unfoldings/Roof/CompatibleFineMargins.lean) | Quantitative radial margins at arbitrary fine endpoints of compatible histories |
| [`Roof/CompatibleMeshMargins`](../Unfoldings/Roof/CompatibleMeshMargins.lean) | Actual fine mesh parent histories inherit radial margins automatically |
| [`Roof/CompatibleSubhistoryMargins`](../Unfoldings/Roof/CompatibleSubhistoryMargins.lean) | Uniform margins for all fine subhistories and radial order from arbitrary earlier edge points |

| [`Geometry/RotationSweepUniqueness`](../Unfoldings/Geometry/RotationSweepUniqueness.lean) | A nonapex rotation-gap point belongs to exactly one intermediate bank |
| [`Geometry/HingeGapRadius`](../Unfoldings/Geometry/HingeGapRadius.lean) | Actual outward hinge gaps stay beyond the hinge radius and have injective circle contacts |
| [`Geometry/HingeCircleContinuity`](../Unfoldings/Geometry/HingeCircleContinuity.lean) | The actual source-circle slice of an outward hinge gap is homeomorphic to its angle interval |

| [`Topology/ProperClosedGraph`](../Unfoldings/Topology/ProperClosedGraph.lean) | A closed graph with a continuous proper coordinate is continuous |
| [`Geometry/HingeSweepContinuity`](../Unfoldings/Geometry/HingeSweepContinuity.lean) | Actual hinge-bank contacts vary jointly continuously with angle and source radius |
| [`Geometry/HingeExteriorCoordinates`](../Unfoldings/Geometry/HingeExteriorCoordinates.lean) | Product coordinates for the entire actual gap beyond its source-centered hinge circle |

| [`Topology/CirclePositiveAngle`](../Unfoldings/Topology/CirclePositiveAngle.lean) | Continuous real angular coordinates on the circle punctured at one |
| [`Geometry/ComplexNormalization`](../Unfoldings/Geometry/ComplexNormalization.lean) | Explicit relative perturbation bound for normalized complex directions |
| [`Geometry/PolygonalRayAsymptote`](../Unfoldings/Geometry/PolygonalRayAsymptote.lean) | Actual source-circle contacts converge to the original terminal-ray direction |
| [`Topology/NoncrossingOrder`](../Unfoldings/Topology/NoncrossingOrder.lean) | Ordered limits fix the order throughout a connected noncrossing family |
| [`Geometry/HingeCircleDirections`](../Unfoldings/Geometry/HingeCircleDirections.lean) | Actual normalized hinge-circle contacts and their positive real angular displacements |
| [`Geometry/HingeCircleAsymptote`](../Unfoldings/Geometry/HingeCircleAsymptote.lean) | Actual source-circle angular displacement tends to the true opening at infinity |
| [`Geometry/HingeCircleOrder`](../Unfoldings/Geometry/HingeCircleOrder.lean) | Actual contacts move strictly counterclockwise at every source radius above the hinge |

| [`Geometry/RadialNormProgress`](../Unfoldings/Geometry/RadialNormProgress.lean) | Convert quantitative radial margins to norm progress on every partial straight edge |
| [`Geometry/RadialChainProgress`](../Unfoldings/Geometry/RadialChainProgress.lean) | Uniform inverse-radius bounds between all actual polygonal-chain points |
| [`Geometry/RadialRayProgress`](../Unfoldings/Geometry/RadialRayProgress.lean) | Uniform Lipschitz radial inverse including the original unbounded terminal ray |
| [`Geometry/RadialContactPerturbation`](../Unfoldings/Geometry/RadialContactPerturbation.lean) | Convert matched bank perturbations to explicit equal-circle contact bounds |

| [`Geometry/RadialMatchedError`](../Unfoldings/Geometry/RadialMatchedError.lean) | Quantitative matched-point bounds from edge errors and actual radial progress |
| [`Geometry/OpeningMatchedError`](../Unfoldings/Geometry/OpeningMatchedError.lean) | Uniform actual equal-circle error bounds for finite hinge-opening sequences |
| [`Geometry/OpeningCircleThreshold`](../Unfoldings/Geometry/OpeningCircleThreshold.lean) | A mesh-independent opening budget keeps all actual contacts in one open source halfplane |

| [`Topology/CircleRealLift`](../Unfoldings/Topology/CircleRealLift.lean) | A real lift in an interval shorter than a full turn inherits phase continuity |
| [`Geometry/HingeCircleLift`](../Unfoldings/Geometry/HingeCircleLift.lean) | Continuous strictly increasing real angular lifts of complete actual hinge-circle arcs |

| [`Geometry/HingeCircleBelow`](../Unfoldings/Geometry/HingeCircleBelow.lean) | Circles on or below a hinge retain their exact original prefix contact |
| [`Geometry/HingeHeadingComparison`](../Unfoldings/Geometry/HingeHeadingComparison.lean) | Continuous common-frame headings have the exact positive real hinge increment |
| [`Geometry/BankCircleDirection`](../Unfoldings/Geometry/BankCircleDirection.lean) | Actual normalized contacts throughout active and inactive hinge circles |
| [`Geometry/HingeCommonHeading`](../Unfoldings/Geometry/HingeCommonHeading.lean) | Monotone common-frame headings on every positive source circle |
| [`Geometry/OpeningCommonDirection`](../Unfoldings/Geometry/OpeningCommonDirection.lean) | The actual opening budget constructs the common open-halfplane frame |
| [`Geometry/OpeningPrefixBudget`](../Unfoldings/Geometry/OpeningPrefixBudget.lean) | Actual prefix and partial-event banks obey the original cumulative budget |

| [`Geometry/OpeningZero`](../Unfoldings/Geometry/OpeningZero.lean) | Zero openings retain the exact original finite chain and terminal ray |
| [`Geometry/HingeGapCircleContacts`](../Unfoldings/Geometry/HingeGapCircleContacts.lean) | Actual gap interiors correspond to strict intermediate circle contacts |
| [`Geometry/HingeGapHeadingBounds`](../Unfoldings/Geometry/HingeGapHeadingBounds.lean) | Actual gap interiors lie strictly between their common-frame bank headings |
| [`Geometry/OpeningCircleTrace`](../Unfoldings/Geometry/OpeningCircleTrace.lean) | One monotone heading sequence for all actual banks and intermediate positive openings |
| [`Geometry/OpeningGapSeparation`](../Unfoldings/Geometry/OpeningGapSeparation.lean) | Pairwise interior separation of actual successive positive hinge gaps |
| [`Geometry/OpeningAllAnchors`](../Unfoldings/Geometry/OpeningAllAnchors.lean) | Derive every intermediate bank and suffix radial test from original subhistory bounds |
| [`Geometry/OpeningGapNonoverlap`](../Unfoldings/Geometry/OpeningGapNonoverlap.lean) | Construct nonoverlapping actual positive hinge-gap families from uniform original margins |

| [`Topology/SubtreeResidualWeights`](../Unfoldings/Topology/SubtreeResidualWeights.lean) | Subtracting immediate-child subtree weights leaves the original junction weight |
| [`Complex/SubtreeResidualHeading`](../Unfoldings/Complex/SubtreeResidualHeading.lean) | Actual unreduced opposite-bank holonomies have residual exactly the local angular defect |
| [`Cap/SubtreeResidualBudget`](../Unfoldings/Cap/SubtreeResidualBudget.lean) | Actual junction residuals are nonnegative and spend original cap curvature once |

| [`Geometry/RadialLinearHomeomorph`](../Unfoldings/Geometry/RadialLinearHomeomorph.lean) | Radius-dependent invertible linear direction changes yield ambient sphere-preserving homeomorphisms |
| [`Geometry/VariableSectorHomeomorph`](../Unfoldings/Geometry/VariableSectorHomeomorph.lean) | An ambient homeomorphism realizes a continuously varying sector width |
| [`Geometry/VariableSectorBanks`](../Unfoldings/Geometry/VariableSectorBanks.lean) | Exact geometric frontier banks of variable-opening sectors |
| [`Geometry/TwoBankAngle`](../Unfoldings/Geometry/TwoBankAngle.lean) | Continuous positive relative angular coordinates of actual radial bank contacts |
| [`Geometry/TwoBankGap`](../Unfoldings/Geometry/TwoBankGap.lean) | Construct an actual Jordan gap whose whole frontier is the two original polygonal banks |
| [`Geometry/TwoBankGapCells`](../Unfoldings/Geometry/TwoBankGapCells.lean) | Construct finite full-dimensional closed convex cells from the two actual bank supports |
| [`Geometry/TwoBankGapMetric`](../Unfoldings/Geometry/TwoBankGapMetric.lean) | Complete actual intrinsic Jordan-gap metrics with sector topology and interior Euclidean charts |

| [`Geometry/OpeningTracePositivePhase`](../Unfoldings/Geometry/OpeningTracePositivePhase.lean) | A positive source opening strictly separates actual original and final contacts on every circle |
| [`Geometry/OpeningTraceControl`](../Unfoldings/Geometry/OpeningTraceControl.lean) | Construct all whole-bank and suffix radial tests for an actual trace from original estimates |
| [`Geometry/PositiveOpeningTraceGap`](../Unfoldings/Geometry/PositiveOpeningTraceGap.lean) | Construct complete polygonal Jordan gaps from actual positive source-opening traces |

| [`Geometry/SpatialEnvelopeWholeSurface`](../Unfoldings/Geometry/SpatialEnvelopeWholeSurface.lean) | The entire actual supported roof is a plane covered by finitely many closed convex spatial cells |
| [`Geometry/SpatialEnvelopeWholeMetric`](../Unfoldings/Geometry/SpatialEnvelopeWholeMetric.lean) | A complete intrinsic polyhedral metric plane on the entire actual unbounded supported roof |

| [`Metric/PolygonalPiecewise`](../Unfoldings/Metric/PolygonalPiecewise.lean) | Finite closed-piece nonexpansion controls the actual intrinsic polygonal metric |
| [`Metric/PolygonalCoverGluing`](../Unfoldings/Metric/PolygonalCoverGluing.lean) | Finite closed convex cover gluings recover exactly the intrinsic polygonal metric, including unbounded and redundant cells |

| [`Metric/Reparametrize`](../Unfoldings/Metric/Reparametrize.lean) | Cellwise isometries preserve the actual gluing metric and all physical seams |
| [`Geometry/SpatialEnvelopeWholeGluing`](../Unfoldings/Geometry/SpatialEnvelopeWholeGluing.lean) | Exact complete planar-cell metric gluing of the entire unbounded physical roof |

| [`Metric/ChangeSeams`](../Unfoldings/Metric/ChangeSeams.lean) | Replacing seams by the same metric identifications preserves the constructed gluing metric |
| [`Metric/PolygonalBoundaryCover`](../Unfoldings/Metric/PolygonalBoundaryCover.lean) | Exact intrinsic covers with actual distinct-cell seams confined to cell boundaries |
| [`Geometry/TwoBankGapGluing`](../Unfoldings/Geometry/TwoBankGapGluing.lean) | Complete boundary-only finite planar-cell gluing models of actual two-bank Jordan gaps |

| [`Geometry/AffineSupportBoundary`](../Unfoldings/Geometry/AffineSupportBoundary.lean) | Proper affine support levels avoid supported-set interiors |
| [`Geometry/AffineEnvelopeWholePartition`](../Unfoldings/Geometry/AffineEnvelopeWholePartition.lean) | Full unbounded active-plane partitions aligned to arbitrary prescribed proper affine lines |
| [`Geometry/SpatialEnvelopePartition`](../Unfoldings/Geometry/SpatialEnvelopePartition.lean) | Exact complete boundary-only planar-cell roof partitions with prescribed lines on actual frontiers |

| [`Geometry/AffineArrangementLocalCone`](../Unfoldings/Geometry/AffineArrangementLocalCone.lean) | Exact local tangent cones from the active inequalities of actual finite affine cells |
| [`Geometry/AffineArrangementConeChart`](../Unfoldings/Geometry/AffineArrangementConeChart.lean) | Isometric whole cell-ball coordinates on the constructed active tangent cones |

| [`Metric/PhysicalSeams`](../Unfoldings/Metric/PhysicalSeams.lean) | Exact complete metric and quotient topology for arbitrary finite closed physical seam pieces, including unbounded cuts |

| [`Metric/PolygonalCut`](../Unfoldings/Metric/PolygonalCut.lean) | Complete actual cut metrics from closures of uncut physical attachments, with exact uncut recovery |
| [`Metric/PolygonalCutLocal`](../Unfoldings/Metric/PolygonalCutLocal.lean) | Restoring a closed physical cut preserves whole intrinsic metric balls away from the cut |

| [`Metric/PhysicalSeamsDiagonal`](../Unfoldings/Metric/PhysicalSeamsDiagonal.lean) | Omit same-cell physical identity seams while preserving the exact metric |
| [`Geometry/SpatialEnvelopeCut`](../Unfoldings/Geometry/SpatialEnvelopeCut.lean) | Complete unbounded planar-cell roof cut metrics with boundary-only seams and exact local restoration |

| [`Geometry/LocalConeClosure`](../Unfoldings/Geometry/LocalConeClosure.lean) | Attachment at a locally conical point is equivalent to a nonempty direction set |
| [`Geometry/AffineArrangementGerm`](../Unfoldings/Geometry/AffineArrangementGerm.lean) | Exact conical germs and retained-attachment direction tests for actual affine-cell cuts |

| [`Geometry/SegmentInequalities`](../Unfoldings/Geometry/SegmentInequalities.lean) | Exact fixed finite affine halfspace systems for actual segments and unbounded rays, including zero-length pieces |
| [`Geometry/PolygonalRayInequalities`](../Unfoldings/Geometry/PolygonalRayInequalities.lean) | Exact finite affine-cell representation of every original polygonal ray and its whole terminal tail |

| [`Geometry/PolygonalRayGerm`](../Unfoldings/Geometry/PolygonalRayGerm.lean) | Exact original cut germs and retained-attachment tests on the actual unit direction circle |

| [`Geometry/HomogeneousGerm`](../Unfoldings/Geometry/HomogeneousGerm.lean) | Uniqueness of exact positively homogeneous local direction models |
| [`Geometry/SegmentEndpointGerm`](../Unfoldings/Geometry/SegmentEndpointGerm.lean) | Actual original outgoing and incoming endpoint directions for segment and ray cut germs |

| [`Geometry/SegmentIncidentGerm`](../Unfoldings/Geometry/SegmentIncidentGerm.lean) | Actual incident endpoint-ray models for finite embedded segment networks |
| [`Geometry/IncidentDirectionCircle`](../Unfoldings/Geometry/IncidentDirectionCircle.lean) | The original incident rays give finitely many actual unit cut directions |
| [`Geometry/ParentCutGerm`](../Unfoldings/Geometry/ParentCutGerm.lean) | Exact original parent and child direction models at every branching forest vertex |

| [`Geometry/SegmentInteriorGerm`](../Unfoldings/Geometry/SegmentInteriorGerm.lean) | Exact original forward and reverse direction models at interior segment points |
| [`Geometry/RayInteriorGerm`](../Unfoldings/Geometry/RayInteriorGerm.lean) | Exact two-sided local direction models everywhere beyond an actual terminal-ray source |
| [`Geometry/EdgeGermDirectionSupport`](../Unfoldings/Geometry/EdgeGermDirectionSupport.lean) | Every actual edge and ray germ uses only its original forward and reverse directions |

| [`Roof/CompatibleCutClosed`](../Unfoldings/Roof/CompatibleCutClosed.lean) | Closedness of the actual compatible finite forest and all its complete terminal rays |
| [`Roof/CompatibleWholeCutPartition`](../Unfoldings/Roof/CompatibleWholeCutPartition.lean) | Construct complete unbounded physical roof cut metrics aligned to the actual compatible one-ended forest |

| [`Metric/ClosedSeamsTopology`](../Unfoldings/Metric/ClosedSeamsTopology.lean) | Exact metric and seam-quotient topology for finite closed-seam systems with finite classes, without compact or complete cells |

| [`Geometry/VariableSectorMembership`](../Unfoldings/Geometry/VariableSectorMembership.lean) | Exact pointwise membership in the geometric sector at the point's own radius |

| [`Geometry/VariableSectorLocalSide`](../Unfoldings/Geometry/VariableSectorLocalSide.lean) | Exact one-sided neighborhoods on both actual variable-sector banks |
| [`Geometry/TwoBankGapLocalSide`](../Unfoldings/Geometry/TwoBankGapLocalSide.lean) | Exact local side tests along both geometric frontier banks of the actual Jordan gap |

| [`Geometry/BankInitialSegment`](../Unfoldings/Geometry/BankInitialSegment.lean) | Exact rigid initial bank coordinates and physical source radii |
| [`Metric/PolygonalConvexChart`](../Unfoldings/Metric/PolygonalConvexChart.lean) | Whole intrinsic metric-ball isometries from local equality with an actual convex region |
| [`Geometry/TwoBankGapSourceSector`](../Unfoldings/Geometry/TwoBankGapSourceSector.lean) | The actual gap agrees locally with the genuine sector of its original initial edge vectors |
| [`Geometry/TwoBankGapSourceChart`](../Unfoldings/Geometry/TwoBankGapSourceChart.lean) | Exact intrinsic source-corner sector-ball isometries without an assumed tangent angle |

| [`Geometry/OpeningSourceAngle`](../Unfoldings/Geometry/OpeningSourceAngle.lean) | The original positive source opening is the exact geometric sector angle and later hinges spend no source turn |
| [`Cap/LeafGapSector`](../Unfoldings/Cap/LeafGapSector.lean) | Actual named leaf bank vectors give precisely the sector complementary to the retained original corner fan |

| [`Cone/AngularClosure`](../Unfoldings/Cone/AngularClosure.lean) | Closing only the two outer banks of a full-turn fan yields the exact Euclidean plane metric |
| [`Cone/AppendSector`](../Unfoldings/Cone/AppendSector.lean) | Complete a slit fan by its genuine complementary sector, preserving all original cell placements |
| [`Cap/LeafCompletedFan`](../Unfoldings/Cap/LeafCompletedFan.lean) | The actual leaf corner completed by its geometric bank-gap sector is isometric to the plane |

| [`Geometry/TwoBankOppositeSide`](../Unfoldings/Geometry/TwoBankOppositeSide.lean) | The actual second gap bank has the opposite geometric side in its own ambient bank frame |
| [`Metric/RouteLocal`](../Unfoldings/Metric/RouteLocal.lean) | A radial budget localizes route estimates without global step control |
| [`Metric/PolygonalGerm`](../Unfoldings/Metric/PolygonalGerm.lean) | Locally equal star-shaped corners have exact intrinsic whole-ball isometries, including reentrant corners |
| [`Geometry/FiniteRegionGermMetric`](../Unfoldings/Geometry/FiniteRegionGermMetric.lean) | Exact intrinsic corner cones of finite affine-cell regions from the actual active inequalities |
| [`Geometry/TwoBankGapCornerChart`](../Unfoldings/Geometry/TwoBankGapCornerChart.lean) | Constructed intrinsic cone-ball isometries at every actual Jordan-gap corner, retaining the original bank equations |

| [`Geometry/SourceSectorCoordinates`](../Unfoldings/Geometry/SourceSectorCoordinates.lean) | Rigid canonical coordinates for the actual Jordan-gap source metric, using its genuine bank vector |
| [`Cone/AttachSector`](../Unfoldings/Cone/AttachSector.lean) | Glue the entire retained intrinsic fan to a separate gap sector along its two named banks |
| [`Cone/AttachSectorPlane`](../Unfoldings/Cone/AttachSectorPlane.lean) | The two-piece complementary sector attachment has exactly the whole Euclidean plane metric |
| [`Cone/PhysicalGapCompletion`](../Unfoldings/Cone/PhysicalGapCompletion.lean) | Complete the retained fan with its actual geometric source sector, keeping physical bank coordinates |
| [`Cap/LeafGeometricCompletion`](../Unfoldings/Cap/LeafGeometricCompletion.lean) | Constructed plane isometry for the actual retained leaf fan completed by the physical sector of its named bank vectors |

| [`Cone/AngularRegion`](../Unfoldings/Cone/AngularRegion.lean) | Every slit fan below a full turn has exactly the intrinsic polygonal metric of its actual planar image |
| [`Cone/ReentrantSector`](../Unfoldings/Cone/ReentrantSector.lean) | Two convex halves construct an intrinsic model for any geometric sector below a full turn, including reentrant angles |
| [`Metric/PolygonalRigid`](../Unfoldings/Metric/PolygonalRigid.lean) | Rigid changes of physical region coordinates preserve the constructed intrinsic polygonal metric |
| [`Cone/ReentrantCornerChart`](../Unfoldings/Cone/ReentrantCornerChart.lean) | A proved geometric corner sector yields an exact intrinsic whole-ball fan chart, including reentrant angles |

| [`Cone/ComplementarySectors`](../Unfoldings/Cone/ComplementarySectors.lean) | Actual complementary geometric sectors cover the plane and meet exactly at their two equal-radius banks |
| [`Metric/GroupedPolygonalCover`](../Unfoldings/Metric/GroupedPolygonalCover.lean) | Grouping convex cover cells into nonconvex intrinsic pieces preserves the final physical gluing metric |
| [`Cone/ComplementarySectorPlane`](../Unfoldings/Cone/ComplementarySectorPlane.lean) | Two complementary intrinsic sectors glued along their actual banks give exactly the whole-plane metric |

| [`Complex/StrictCopyAngles`](../Unfoldings/Complex/StrictCopyAngles.lean) | Distinct sibling cut copies have boundary fans strictly smaller than their original full star |
| [`Cone/IntervalSector`](../Unfoldings/Cone/IntervalSector.lean) | The actual retained interval fan is isometric to its geometric intrinsic sector, preserving the original angular development |
| [`Cap/SplitBankSector`](../Unfoldings/Cap/SplitBankSector.lean) | Whole intrinsic sector-ball charts for actual split cap-bank copies, with a derived genuine complementary width |
| [`Geometry/PositiveGapAngle`](../Unfoldings/Geometry/PositiveGapAngle.lean) | Positive geometric bank-vector angles retain genuine reentrant openings rather than reducing them to negative principal arguments |
| [`Development/BankComplementAngle`](../Unfoldings/Development/BankComplementAngle.lean) | Actual terminal bank vectors compute exactly the complement of the real retained fan angle |
| [`Cap/SplitBankComplement`](../Unfoldings/Cap/SplitBankComplement.lean) | Constructed actual split-bank intrinsic sectors with complementary angles derived from the developed original bank vectors |

| [`Geometry/LocalConeFrontier`](../Unfoldings/Geometry/LocalConeFrontier.lean) | The frontier of an exact homogeneous corner model is forced by the original physical boundary germ |
| [`Geometry/LocalConeRegularClosed`](../Unfoldings/Geometry/LocalConeRegularClosed.lean) | Exact homogeneous local models inherit regular closedness from the physical region |
| [`Geometry/ComplexBankGerm`](../Unfoldings/Geometry/ComplexBankGerm.lean) | Original complex polygonal bank direction germs include precisely their actual incident segments and tails |
| [`Geometry/TwoBankGapConeFrontier`](../Unfoldings/Geometry/TwoBankGapConeFrontier.lean) | Constructed gap corner cones are regular closed with frontier exactly the actual original bank directions |

| [`Cone/ReentrantSectorTopology`](../Unfoldings/Cone/ReentrantSectorTopology.lean) | Actual sub-full-turn sectors are regular closed, and every strict positive-radius heading is interior |
| [`Cone/ReentrantSectorBoundary`](../Unfoldings/Cone/ReentrantSectorBoundary.lean) | Exact bank frontiers and connected geometric interiors of convex and reentrant sectors |
| [`Geometry/RegularClosedRecognition`](../Unfoldings/Geometry/RegularClosedRecognition.lean) | A regular closed region with connected interior and exterior is recognized from its boundary and one interior witness |
| [`Cone/SectorRecognition`](../Unfoldings/Cone/SectorRecognition.lean) | An exact corner cone is selected by the original bank rays and arbitrarily near geometric interior witnesses |
| [`Geometry/TwoBankGapInteriorSide`](../Unfoldings/Geometry/TwoBankGapInteriorSide.lean) | Actual strict interior tests along both polygonal gap banks, including their bends |
| [`Geometry/TwoBankGapInteriorApproach`](../Unfoldings/Geometry/TwoBankGapInteriorApproach.lean) | Small opposite circular motions from the two actual banks construct genuine gap-interior witnesses |

| [`Geometry/CircularConeApproach`](../Unfoldings/Geometry/CircularConeApproach.lean) | Original source-circle tangents inside a cone construct actual nearby geometric interior points |
| [`Geometry/TwoBankGapOrientationWitness`](../Unfoldings/Geometry/TwoBankGapOrientationWitness.lean) | Source-circle normals select actual first-bank gap orientation samples without an aperture premise |
| [`Cone/RotatedSectorRecognition`](../Unfoldings/Cone/RotatedSectorRecognition.lean) | Recognize the complete corner sector while retaining the original rigid edge frame |
| [`Geometry/TwoBankGapBankSector`](../Unfoldings/Geometry/TwoBankGapBankSector.lean) | Construct whole actual gap-bank sector charts from the original incident rays and source-circle normal |

| [`Geometry/RadialRayVertices`](../Unfoldings/Geometry/RadialRayVertices.lean) | Genuine outward bank vertices have strict radial order, avoid all open edges and miss the later whole tail |
| [`Geometry/SegmentIncidentRays`](../Unfoldings/Geometry/SegmentIncidentRays.lean) | Exact original endpoint-ray germs for finite segment families in arbitrary normed spaces |
| [`Geometry/PolygonalBankVertexGerm`](../Unfoldings/Geometry/PolygonalBankVertexGerm.lean) | A named genuine outward bank bend has precisely its original incoming and outgoing rays, with incidences derived |

The original internal first-bank corner now has a derived whole intrinsic chart:
[`exists_first_internal_vertex_chart`](../Unfoldings/Geometry/TwoBankGapInternalCorner.lean).
The original outgoing and reversed incoming edges determine its positive aperture
and rigid frame; the source-circle normal selects the occupied side. Genuine
outward edges give strict incoming progress automatically; strict outgoing
progress remains an explicit geometric hypothesis. This includes reentrant
corners and does not yet identify their widths with the actual retained cap fan.

- [`TwoBankGapSecondInternalCorner`](../Unfoldings/Geometry/TwoBankGapSecondInternalCorner.lean):
  actual second-bank internal fan-ball charts from the original edges.
- [`RadialRightCorner`](../Unfoldings/Geometry/RadialRightCorner.lean):
  original right-side frame, normal, bank rays and complementary aperture.

- [`BoundaryChainAperture`](../Unfoldings/Complex/BoundaryChainAperture.lean):
  actual original finite-roll lengths, directions and complementary aperture.
- [`Development/BoundaryChainRolling`](../Unfoldings/Development/BoundaryChainRolling.lean):
  finite intrinsic rolls realize the actual developed bank vectors and positions.
- [`RolledBankGapCorner`](../Unfoldings/Cap/RolledBankGapCorner.lean):
  actual second-bank gap charts with the complementary retained-cap width.

- [`MirroredBankGapCorner`](../Unfoldings/Cap/MirroredBankGapCorner.lean):
  first-bank complementary retained-cap chart in the mirrored orientation.
- [`OpeningStrictProgress`](../Unfoldings/Geometry/OpeningStrictProgress.lean):
  original opening budgets give strict radial progress at internal bank bends.
- [`ComplementaryModelCompletion`](../Unfoldings/Cone/ComplementaryModelCompletion.lean):
  keep the original corner model, attach its geometric complement, recover the plane.
- [`SplitBankCompletedPlane`](../Unfoldings/Cap/SplitBankCompletedPlane.lean):
  actual retained tangent fans completed along exactly their two ordered banks.

- [`Development/BoundaryChainAperture`](../Unfoldings/Development/BoundaryChainAperture.lean):
  complementary angles in the actual original common development frame.
- [`DevelopedBankGapCorner`](../Unfoldings/Cap/DevelopedBankGapCorner.lean):
  complementary second-bank charts using actual developed edge vectors.
- [`PolygonalBankTailGerm`](../Unfoldings/Geometry/PolygonalBankTailGerm.lean):
  exact original incoming and entire outgoing tail rays at the terminal vertex.
- [`TwoBankGapTailCorner`](../Unfoldings/Geometry/TwoBankGapTailCorner.lean),
  [`TwoBankGapSecondTailCorner`](../Unfoldings/Geometry/TwoBankGapSecondTailCorner.lean):
  both occupied intrinsic gap corners at the last finite bend.

- [`RadialRayEdgePoints`](../Unfoldings/Geometry/RadialRayEdgePoints.lean):
  original edge-point isolation and strict radial progress.
- [`SegmentInteriorDirections`](../Unfoldings/Geometry/SegmentInteriorDirections.lean):
  exact direction-line germs in arbitrary real normed spaces.
- [`PolygonalBankEdgeGerm`](../Unfoldings/Geometry/PolygonalBankEdgeGerm.lean):
  actual original finite-edge direction germs.
- [`TwoBankGapEdgeChart`](../Unfoldings/Geometry/TwoBankGapEdgeChart.lean),
  [`TwoBankGapSecondEdgeChart`](../Unfoldings/Geometry/TwoBankGapSecondEdgeChart.lean):
  both actual whole intrinsic half-plane charts at strict finite bank edge points.

- [`PolygonalBankTailInterior`](../Unfoldings/Geometry/PolygonalBankTailInterior.lean):
  exact infinite-tail direction germs, prefix isolation and strict radial progress.
- [`TwoBankGapTailInteriorChart`](../Unfoldings/Geometry/TwoBankGapTailInteriorChart.lean),
  [`TwoBankGapSecondTailInteriorChart`](../Unfoldings/Geometry/TwoBankGapSecondTailInteriorChart.lean):
  both actual whole intrinsic half-plane charts at positive tail points.
- [`ParentFrontierHistory`](../Unfoldings/Topology/ParentFrontierHistory.lean):
  first-contact branch processing with constructed distinct original vertex charges.
- [`ParentFrontierResidualBudget`](../Unfoldings/Cap/ParentFrontierResidualBudget.lean):
  actual original opposite-bank residual budget for every constructed history.

- [`ParentFrontierReach`](../Unfoldings/Topology/ParentFrontierReach.lean):
  processing explores exactly the original parent paths and skips old ancestors.
- [`ConsecutiveSectors`](../Unfoldings/Cone/ConsecutiveSectors.lean),
  [`ConsecutiveSectorMetric`](../Unfoldings/Cone/ConsecutiveSectorMetric.lean):
  exact common bank, geometric sum and whole intrinsic joined metric, including zero insertions.
- [`CompletedCornerRemainder`](../Unfoldings/Cone/CompletedCornerRemainder.lean):
  metric surgery remainder complementary to a retained untouched side.
- [`JunctionRemainderModel`](../Unfoldings/Cap/JunctionRemainderModel.lean):
  local cap remainder model with actual curvature increment and total-budget bound.

- [`SelectedJunctionCopies`](../Unfoldings/Complex/SelectedJunctionCopies.lean):
  actual selected parent-child incidence forces distinct sibling cut copies.
- [`SelectedJunctionModels`](../Unfoldings/Cap/SelectedJunctionModels.lean):
  actual selected junction sector charts and local curvature-charged remainder models.
- [`ParentFrontierContact`](../Unfoldings/Topology/ParentFrontierContact.lean):
  the original last fresh edge into the first processed ancestor.
- [`ContactJunctionModels`](../Unfoldings/Cap/ContactJunctionModels.lean):
  constructed contact histories supply the selected-junction hypotheses themselves.

- [`SelectedContourHistory`](../Unfoldings/Complex/SelectedContourHistory.lean):
  the actual original cyclic contour supplies a complete first-contact schedule
  and conserves every root-vanishing original weight.
- [`ContourResidualCharge`](../Unfoldings/Cap/ContourResidualCharge.lean):
  exact total original opposite-bank residual charge for that constructed schedule.

- [`ProcessedParentCuts`](../Unfoldings/Complex/ProcessedParentCuts.lean):
  exact actual retained seams at every intermediate parent-frontier stage.
- [`FreshSourceStar`](../Unfoldings/Cap/FreshSourceStar.lean):
  the unique full-original-angle cut copy of each fresh source.
- [`FreshSourceCompletion`](../Unfoldings/Cap/FreshSourceCompletion.lean):
  local intrinsic plane completion of a positive-curvature fresh source.

- [`IntervalBankClosure`](../Unfoldings/Cone/IntervalBankClosure.lean):
  close the actual full-turn retained tangent fan along only its two original banks.
- [`FreshFlatSource`](../Unfoldings/Cap/FreshFlatSource.lean):
  exact plane completion of zero-curvature fresh sources at intermediate stages.

- [`ProcessedCutForest`](../Unfoldings/Complex/ProcessedCutForest.lean):
  exact intermediate rooted forests, original parent routes and intrinsic cut disks.
- [`ProcessedCutBoundary`](../Unfoldings/Complex/ProcessedCutBoundary.lean):
  boundary copies are exactly processed vertices; construct each actual bank contour.

- [`WeightedBoundaryIncidence`](../Unfoldings/Complex/WeightedBoundaryIncidence.lean):
  actual contour incidence when internal vertex weights vanish.
- [`ProcessedCutIncidence`](../Unfoldings/Complex/ProcessedCutIncidence.lean):
  original active selector/seam bijection and exact intermediate weighted copy counts.
- [`ProcessedJunctionCopies`](../Unfoldings/Complex/ProcessedJunctionCopies.lean):
  current parent-child incidence forces intermediate sibling cut copies.
- [`ProcessedContactModels`](../Unfoldings/Cap/ProcessedContactModels.lean):
  first-contact local surgery models on actual intermediate original cut disks.

- [`ParentFrontierNeighbor`](../Unfoldings/Topology/ParentFrontierNeighbor.lean),
  [`ParentFrontierSingleton`](../Unfoldings/Topology/ParentFrontierSingleton.lean):
  fresh-neighbor first contact and singleton processed-set updates.
- [`SelectedContourNeighbors`](../Unfoldings/Complex/SelectedContourNeighbors.lean),
  [`ContourCutSteps`](../Unfoldings/Complex/ContourCutSteps.lean): actual original
  contour adjacency and exact single-seam processing.
- [`RimStartedContour`](../Unfoldings/Complex/RimStartedContour.lean),
  [`Cap.RimStartedContour`](../Unfoldings/Cap/RimStartedContour.lean): constructed
  rim-started orders and exact visited-prefix processed sets.
- [`RelativeBoundaryCopyCount`](../Unfoldings/Complex/RelativeBoundaryCopyCount.lean),
  [`SingleBoundaryCopySplit`](../Unfoldings/Complex/SingleBoundaryCopySplit.lean),
  [`ProcessedParentCopySplit`](../Unfoldings/Cap/ProcessedParentCopySplit.lean):
  exact intermediate parent-copy splitting and original angle conservation.

- [`RestoredLinkChain`](../Unfoldings/Complex/RestoredLinkChain.lean): exact
  ordered original fans survive restoration when both terminal banks remain.
- [`ProcessedContourFans`](../Unfoldings/Complex/ProcessedContourFans.lean):
  derive the surviving banks and exact original fan at earlier contour positions.

- [`ContourContactFans`](../Unfoldings/Complex/ContourContactFans.lean): identify
  the original contact fan immediately after its fresh child is processed.
- [`ContourContactRemainder`](../Unfoldings/Cap/ContourContactRemainder.lean):
  derive the contact model and exact curvature charge from the original contour.
- [`RestoredBoundaryFan`](../Unfoldings/Cone/RestoredBoundaryFan.lean): isometries
  of entire surviving original tangent fans, fixing every original cell point.

- [`BoundaryFanExcision`](../Unfoldings/Complex/BoundaryFanExcision.lean):
  actual cut restoration is a whole-ball isometry at surviving original fans.
- [`LinearTwoExits`](../Unfoldings/Topology/LinearTwoExits.lean),
  [`LinearSubtreeContour`](../Unfoldings/Complex/LinearSubtreeContour.lean):
  derive a true depth-first order and complete processing before each subtree exit.

- [`ContourActiveAncestors`](../Unfoldings/Complex/ContourActiveAncestors.lean):
  unfinished processed vertices lie on the original current ancestor path.
- [`OrientedParentBanks`](../Unfoldings/Complex/OrientedParentBanks.lean),
  [`UnprocessedParentBanks`](../Unfoldings/Complex/UnprocessedParentBanks.lean):
  original oriented bank names and actual intrinsic endpoint closure before processing.
- [`ContourContactExcision`](../Unfoldings/Complex/ContourContactExcision.lean):
  derive whole-ball restoration charts at original contour contact corners.

- [`ProcessedDescendantIncidence`](../Unfoldings/Topology/ProcessedDescendantIncidence.lean):
  exact original edge-end counts in processed descendant subtrees.
- [`ProcessedSubtreeAngles`](../Unfoldings/Complex/ProcessedSubtreeAngles.lean):
  actual intermediate contour turn equals pi minus processed original subtree curvature.

- [`BoundaryContourRegions`](../Unfoldings/Complex/BoundaryContourRegions.lean):
  arbitrary current vertex regions cross exactly their actual contour banks.
- [`ProcessedSubtreeBanks`](../Unfoldings/Complex/ProcessedSubtreeBanks.lean):
  derive the two actual current parent banks and orient their subtree entry and exit.

- [`ProcessedSubtreeRolling`](../Unfoldings/Complex/ProcessedSubtreeRolling.lean):
  exact unreduced current parent-bank heading equals processed original subtree curvature.

- [`ProcessedDescendantWeights`](../Unfoldings/Topology/ProcessedDescendantWeights.lean):
  exact singleton-step updates of original processed subtree weights.
- [`ProcessedParentBankHeading`](../Unfoldings/Cap/ProcessedParentBankHeading.lean):
  actual constructed current bank measurements, curvature bounds and exact fresh-source increments.

- [`ProcessedParentBankVariation`](../Unfoldings/Cap/ProcessedParentBankVariation.lean):
  actual current parent-bank measurements are monotone and have oscillation at most total curvature.

- [`CurrentBankSelectors`](../Unfoldings/Complex/CurrentBankSelectors.lean),
  [`LinearSubtreeBanks`](../Unfoldings/Complex/LinearSubtreeBanks.lean),
  [`FutureParentBanks`](../Unfoldings/Complex/FutureParentBanks.lean): identify
  actual upcoming current banks as original ancestor exit banks.
- [`RootwardBankEnumeration`](../Unfoldings/Complex/RootwardBankEnumeration.lean):
  exact bijection between surviving upcoming banks and processed original ancestors.
- [`RestoredContourExcursion`](../Unfoldings/Complex/RestoredContourExcursion.lean),
  [`PrunedContourStep`](../Unfoldings/Complex/PrunedContourStep.lean): restored
  excursions close intrinsically and give the actual current boundary successor.
- [`SurvivingBoundaryBanks`](../Unfoldings/Complex/SurvivingBoundaryBanks.lean):
  preserve original endpoints, lengths and entire bank parametrizations under restoration.

- [`RootwardBankOrder`](../Unfoldings/Complex/RootwardBankOrder.lean),
  [`ConsecutiveRootwardBanks`](../Unfoldings/Complex/ConsecutiveRootwardBanks.lean):
  exact ancestor order and restoration of every intervening contour bank.
- [`AncestorInterval`](../Unfoldings/Topology/AncestorInterval.lean),
  [`LinearBankInterval`](../Unfoldings/Topology/LinearBankInterval.lean):
  original parent-neighbor intervals and explicit nonwrapping cyclic bank regions.
- [`RootwardBoundaryStep`](../Unfoldings/Complex/RootwardBoundaryStep.lean),
  [`RootwardParentChain`](../Unfoldings/Complex/RootwardParentChain.lean):
  derive actual current bank adjacency and construct chains from original parent iterates.

- [`AncestorPathCuts`](../Unfoldings/Complex/AncestorPathCuts.lean):
  original reference ancestor-path cuts and canonical restoration from current cuts.
- [`RootwardPathFans`](../Unfoldings/Complex/RootwardPathFans.lean):
  derive exact one-sided reference corner sets, angles and whole-ball metric comparisons.

- [`SurvivingBoundaryChain`](../Unfoldings/Complex/SurvivingBoundaryChain.lean),
  [`RootwardReferenceChain`](../Unfoldings/Complex/RootwardReferenceChain.lean):
  actual surviving reference chains preserve every real heading and the full polygonal roll.
- [`BoundaryFanRestoration`](../Unfoldings/Cone/BoundaryFanRestoration.lean),
  [`RootwardPathFanMetric`](../Unfoldings/Cone/RootwardPathFanMetric.lean):
  whole intrinsic tangent-fan isometries fixing original supporting-wedge points.

- [`RootwardFanModels`](../Unfoldings/Cap/RootwardFanModels.lean): actual
  rootward junctions supply strict apertures, whole-ball charts and exact-curvature remainder models.

- [`RootwardProjectedBanks`](../Unfoldings/Cap/RootwardProjectedBanks.lean):
  the actual current bank chain projects pointwise to its original parent segments and rim root.

- [`PositiveRimContour`](../Unfoldings/Cap/PositiveRimContour.lean),
  [`RootwardBankSides`](../Unfoldings/Cap/RootwardBankSides.lean): construct the
  positive rim-started orientation and the physical left side of actual parent banks.
- [`RetainedFanFaces`](../Unfoldings/Complex/RetainedFanFaces.lean),
  [`RetainedFanSubdivision`](../Unfoldings/Complex/RetainedFanSubdivision.lean):
  exact original face selections and selected one-sided angle preservation under refinement.
- [`CompletionRetainedFanAngles`](../Unfoldings/Roof/CompletionRetainedFanAngles.lean):
  concrete physical completions preserve the actual selected original fan angle.

- [`BoundaryFanAgreement`](../Unfoldings/Complex/BoundaryFanAgreement.lean):
  two actual terminal bank germs determine all original corner weights and fan angles.

- [`ChainTerminalUniqueness`](../Unfoldings/Topology/ChainTerminalUniqueness.lean):
  deterministic chains with matching ends have identical lengths and ordered points.
- [`RawGermChains`](../Unfoldings/Complex/RawGermChains.lean),
  [`RestrictedFanAgreement`](../Unfoldings/Complex/RestrictedFanAgreement.lean):
  actual cut and restricted fans have the same original corner weights when their terminal germs agree.

- [`ProjectedBankUniqueness`](../Unfoldings/Cap/ProjectedBankUniqueness.lean):
  physical projected banks determine actual original germs, for either orientation.
- [`ProjectedFanOrientation`](../Unfoldings/Cap/ProjectedFanOrientation.lean):
  arbitrary link subchains have disjoint cones and actual fan terminal orientations are opposite.

- [`ProjectedFanAgreement`](../Unfoldings/Cap/ProjectedFanAgreement.lean):
  derive actual restricted fan weights and intrinsic angle from physical directed banks.

- [`Complex.RestrictedCutFanAgreement`](../Unfoldings/Complex/RestrictedCutFanAgreement.lean),
  [`Cap.RestrictedCutFanAgreement`](../Unfoldings/Cap/RestrictedCutFanAgreement.lean):
  compare actual fans in independently cut face restrictions from terminal banks.
- [`CompletionPatchFanAgreement`](../Unfoldings/Roof/CompletionPatchFanAgreement.lean):
  recover original one-sided cut angles inside concrete physical comparison patches.

- [`RestrictedBoundaryChainAgreement`](../Unfoldings/Complex/RestrictedBoundaryChainAgreement.lean),
  [`ProjectedBoundaryChainAgreement`](../Unfoldings/Cap/ProjectedBoundaryChainAgreement.lean):
  match actual chains and preserve full real rolling from physical projected vertex positions.

- [`BoundaryEdgeDetection`](../Unfoldings/Complex/BoundaryEdgeDetection.lean):
  detect an original bank from one regular quotient boundary point.
- [`JordanOriginalBanks`](../Unfoldings/Cap/JordanOriginalBanks.lean):
  construct actual Jordan banks from selected original edges on the curve.
- [`RestrictedBoundaryChainLift`](../Unfoldings/Cap/RestrictedBoundaryChainLift.lean),
  [`JordanBoundaryChainLift`](../Unfoldings/Cap/JordanBoundaryChainLift.lean):
  derive actual patch successors and preserve the entire original bank roll.

- [`PositiveRayCones`](../Unfoldings/Geometry/PositiveRayCones.lean),
  [`ProjectedBankRays`](../Unfoldings/Cap/ProjectedBankRays.lean):
  identify actual positive original banks from directed rays, independently of endpoint length.

- [`LocalTwoRays`](../Unfoldings/Geometry/LocalTwoRays.lean),
  [`ProjectedRawBankRays`](../Unfoldings/Cap/ProjectedRawBankRays.lean):
  recover physical outgoing rays and exact original labels without length assumptions.
- [`JordanLocalTwoRays`](../Unfoldings/Cap/JordanLocalTwoRays.lean),
  [`JordanBankPropagation`](../Unfoldings/Cap/JordanBankPropagation.lean),
  [`JordanLocalChainLift`](../Unfoldings/Cap/JordanLocalChainLift.lean):
  one initial selected face and local curve geometry construct the full actual Jordan bank roll.

- [`PolygonalVertexRays`](../Unfoldings/Geometry/PolygonalVertexRays.lean),
  [`RadialClosureVertexRays`](../Unfoldings/Geometry/RadialClosureVertexRays.lean):
  radial order derives the exact two original hinge rays in the actual comparison closure.

- [`ProjectedBoundaryChain`](../Unfoldings/Cap/ProjectedBoundaryChain.lean):
  the entire actual projected bank path, with exact parametrizations and original edge coverage.
- [`RadialJordanChainLift`](../Unfoldings/Cap/RadialJordanChainLift.lean):
  physical radial closure geometry constructs the actual Jordan comparison roll from one initial side.

- [`PolygonalVertexCoverage`](../Unfoldings/Geometry/PolygonalVertexCoverage.lean),
  [`JordanChainCoverage`](../Unfoldings/Cap/JordanChainCoverage.lean):
  the actual chain's internal vertices are exactly the geometric bank vertices.
- [`JordanChainTurnSum`](../Unfoldings/Cap/JordanChainTurnSum.lean):
  exact equality of actual hinge-error and geometric bank sums, with original vertex copies.

- [`RestrictedChainCornerWeights`](../Unfoldings/Complex/RestrictedChainCornerWeights.lean),
  [`OriginalChainTurnError`](../Unfoldings/Cap/OriginalChainTurnError.lean):
  exact actual projected fan weights, original cut-fan errors and physical chain preservation.
- [`JordanChainErrorBound`](../Unfoldings/Cap/JordanChainErrorBound.lean),
  [`OriginalRadialChainErrorBound`](../Unfoldings/Cap/OriginalRadialChainErrorBound.lean):
  derive the geometric curvature-and-tilt error bound for actual original one-sided cut banks.

- [`OriginalBankHeadingComparison`](../Unfoldings/Cap/OriginalBankHeadingComparison.lean):
  actual unreduced heading-prefix identities and a uniform mesh-independent small-tilt bound.

- [`ChainConcatenation`](../Unfoldings/Topology/ChainConcatenation.lean),
  [`ChainReversal`](../Unfoldings/Topology/ChainReversal.lean):
  join and reorient actual bank blocks while preserving original labels and endpoints.
- [`CommonSubedge`](../Unfoldings/Geometry/CommonSubedge.lean),
  [`CompletionBankDistinctness`](../Unfoldings/Roof/CompletionBankDistinctness.lean):
  different original cut banks have distinct actual physical fine-bank pieces.

- [`ReversedBoundaryChain`](../Unfoldings/Complex/ReversedBoundaryChain.lean),
  [`CompletionOrientedBankRolling`](../Unfoldings/Roof/CompletionOrientedBankRolling.lean):
  actual directed fine refinements in either endpoint order with zero extra real turn.
- [`CompletionBankBlockJoins`](../Unfoldings/Roof/CompletionBankBlockJoins.lean):
  derive actual fine block separation and successors from original labels and corner copies.

- [`CompletionBankMetricRefinement`](../Unfoldings/Roof/CompletionBankMetricRefinement.lean),
  [`CompletionBankBlocks`](../Unfoldings/Roof/CompletionBankBlocks.lean):
  construct directed metric blocks and concatenate them from original corner and bank labels.

- [`ChainConcatRange`](../Unfoldings/Topology/ChainConcatRange.lean),
  [`ChainBlockAssembly`](../Unfoldings/Topology/ChainBlockAssembly.lean):
  assemble finite ordered block families with exact original directed-label coverage.

- [`DirectedCutBank`](../Unfoldings/Complex/DirectedCutBank.lean),
  [`DirectedBankChain`](../Unfoldings/Complex/DirectedBankChain.lean):
  recover original seam, side and endpoint labels from actual cut-bank chains.
- [`CompletionBankPathAssembly`](../Unfoldings/Roof/CompletionBankPathAssembly.lean):
  complete physical fine paths with exact metric endpoints and directed piece coverage.

- [`BoundaryChainVertices`](../Unfoldings/Complex/BoundaryChainVertices.lean):
  starting intrinsic vertex copies of any actual boundary chain are distinct.
- [`CompletionOriginalChainRefinement`](../Unfoldings/Roof/CompletionOriginalChainRefinement.lean),
  [`CompletionChainFanRefinement`](../Unfoldings/Roof/CompletionChainFanRefinement.lean),
  [`CompletionChainHeading`](../Unfoldings/Roof/CompletionChainHeading.lean):
  whole physical fine paths preserve old fan angles and real terminal headings;
  every inserted hinge is straight.

- [`ChainSubsequence`](../Unfoldings/Topology/ChainSubsequence.lean),
  [`CompletionChainOrder`](../Unfoldings/Roof/CompletionChainOrder.lean):
  actual successors derive exact contiguous fine blocks and ordered old hinges.
- [`BoundaryChainHeadingStep`](../Unfoldings/Complex/BoundaryChainHeadingStep.lean),
  [`CompletionChainPrefixHeading`](../Unfoldings/Roof/CompletionChainPrefixHeading.lean):
  every fine piece retains its original bank's exact unreduced real heading.

- [`BoundaryChainTrace`](../Unfoldings/Complex/BoundaryChainTrace.lean),
  [`CompletionChainTrace`](../Unfoldings/Roof/CompletionChainTrace.lean):
  exact whole intrinsic bank traces under the concrete cut-metric equivalence.
- [`CompletionOriginalSpatial`](../Unfoldings/Roof/CompletionOriginalSpatial.lean),
  [`CompletionChainSpatialTrace`](../Unfoldings/Roof/CompletionChainSpatialTrace.lean):
  actual physical foldings commute, preserving whole spatial and projected bank traces.

- [`OrderedSegmentLength`](../Unfoldings/Geometry/OrderedSegmentLength.lean),
  [`BoundaryBankLength`](../Unfoldings/Complex/BoundaryBankLength.lean),
  [`CompletionBankLength`](../Unfoldings/Roof/CompletionBankLength.lean):
  genuine physical fine pieces preserve each original bank's full intrinsic length.
- [`CompletionChainLength`](../Unfoldings/Roof/CompletionChainLength.lean):
  fine-bank piece bijections, whole arclength and exact rolled block displacements and endpoint.

- [`CompletionChainRollPositions`](../Unfoldings/Roof/CompletionChainRollPositions.lean),
  [`CompletionChainRollTrace`](../Unfoldings/Roof/CompletionChainRollTrace.lean):
  exact ordered arclength parameters for every point and equality of whole rolled images.
- [`FiniteInterpolation`](../Unfoldings/Geometry/FiniteInterpolation.lean),
  [`RadialMarginSubdivision`](../Unfoldings/Geometry/RadialMarginSubdivision.lean),
  [`CompletionChainRadial`](../Unfoldings/Roof/CompletionChainRadial.lean):
  whole-bank radial order and quantitative radial margins survive actual refinement without loss.

- [`CompletionRootwardChain`](../Unfoldings/Roof/CompletionRootwardChain.lean):
  actual current rootward stems construct full physical fine paths with their reference roll.
- [`JordanSeamSideSelection`](../Unfoldings/Cap/JordanSeamSideSelection.lean),
  [`JordanInitialSeamBank`](../Unfoldings/Cap/JordanInitialSeamBank.lean):
  construct the unique selected initial original seam bank, retaining actual endpoint transport.

- [`ProjectedSignedBankRays`](../Unfoldings/Cap/ProjectedSignedBankRays.lean),
  [`SignedJordanBankPropagation`](../Unfoldings/Cap/SignedJordanBankPropagation.lean),
  [`SignedJordanLocalChainLift`](../Unfoldings/Cap/SignedJordanLocalChainLift.lean):
  actual occupied-side ray uniqueness and Jordan bank propagation in either orientation.
- [`SignedRadialJordanChainLift`](../Unfoldings/Cap/SignedRadialJordanChainLift.lean),
  [`SignedOriginalRadialChainErrorBound`](../Unfoldings/Cap/SignedOriginalRadialChainErrorBound.lean),
  [`SignedOriginalBankHeadingComparison`](../Unfoldings/Cap/SignedOriginalBankHeadingComparison.lean):
  construct actual radial comparison chains and uniform real-heading bounds without a sign input.

- [`JordanComplementaryChainError`](../Unfoldings/Cap/JordanComplementaryChainError.lean):
  complementary original fan sums along actual Jordan chains pay at most one extra
  total-curvature term, with a uniform mesh-independent small-tilt budget.

- [`BankLengths`](../Unfoldings/Polyhedron/BankLengths.lean),
  [`ProjectedUnsignedBankRays`](../Unfoldings/Cap/ProjectedUnsignedBankRays.lean):
  directed rays determine original full edge vectors on either incident side, and intrinsic lengths.
- [`JordanPhysicalInitialBank`](../Unfoldings/Cap/JordanPhysicalInitialBank.lean),
  [`JordanPhysicalBankPropagation`](../Unfoldings/Cap/JordanPhysicalBankPropagation.lean):
  construct the actual initial side and propagate full physical bank geometry without face matching.
- [`PhysicalBoundaryChainLift`](../Unfoldings/Cap/PhysicalBoundaryChainLift.lean),
  [`JordanPhysicalChainLift`](../Unfoldings/Cap/JordanPhysicalChainLift.lean),
  [`RadialJordanPhysicalChain`](../Unfoldings/Cap/RadialJordanPhysicalChain.lean):
  whole actual radial Jordan traversals from geometry alone, without an initial-side input.

- [`ChainSuffix`](../Unfoldings/Topology/ChainSuffix.lean),
  [`ChainComplement`](../Unfoldings/Topology/ChainComplement.lean),
  [`ChainConcatSum`](../Unfoldings/Topology/ChainConcatSum.lean):
  exact complementary original intervals, derived cycle partitions and additive weights.
- [`ComplementaryLinkChains`](../Unfoldings/Complex/ComplementaryLinkChains.lean):
  actual complementary interior vertex-link intervals partition every original corner weight.

- [`RawLinkComplement`](../Unfoldings/Complex/RawLinkComplement.lean),
  [`OppositeRestrictedFans`](../Unfoldings/Complex/OppositeRestrictedFans.lean):
  opposite actual retained fans partition all original corner weights from their seam endpoints.
- [`EdgeReverseGerm`](../Unfoldings/Complex/EdgeReverseGerm.lean):
  original seam endpoint transport commutes with directed edge reversal.

- [`PhysicalBankSideDichotomy`](../Unfoldings/Cap/PhysicalBankSideDichotomy.lean),
  [`PhysicalOppositeFanWeights`](../Unfoldings/Cap/PhysicalOppositeFanWeights.lean),
  [`PhysicalOppositeFanError`](../Unfoldings/Cap/PhysicalOppositeFanError.lean):
  actual physical chains choose one consistent original side; opposite fan errors add to curvature.
- [`OriginalChainCurvature`](../Unfoldings/Cap/OriginalChainCurvature.lean),
  [`PhysicalChainErrorComparison`](../Unfoldings/Cap/PhysicalChainErrorComparison.lean):
  derive distinct original hinge charges and compare either actual fan side at total-curvature cost.
- [`UnconditionalOriginalRadialChainErrorBound`](../Unfoldings/Cap/UnconditionalOriginalRadialChainErrorBound.lean),
  [`UnconditionalOriginalBankHeadingComparison`](../Unfoldings/Cap/UnconditionalOriginalBankHeadingComparison.lean):
  original real-heading bounds from admissible radial closure geometry, without initial-side inputs.

- [`EventualRayCell`](../Unfoldings/Geometry/EventualRayCell.lean),
  [`AffineSideRayCells`](../Unfoldings/Geometry/AffineSideRayCells.lean):
  a ray in a finite convex cover eventually lies in one cell; aligned closed cells
  supply a terminal cell on each specified side of the line.
- [`PhysicalSeamLabels`](../Unfoldings/Metric/PhysicalSeamLabels.lean),
  [`AffineCutBanks`](../Unfoldings/Metric/AffineCutBanks.lean):
  local affine cuts preserve side labels and distinguish actual metric bank copies.
- [`SpatialEnvelopeCutRays`](../Unfoldings/Geometry/SpatialEnvelopeCutRays.lean),
  [`SpatialEnvelopeCutBanks`](../Unfoldings/Geometry/SpatialEnvelopeCutBanks.lean),
  [`RayForwardHalfspace`](../Unfoldings/Geometry/RayForwardHalfspace.lean),
  [`SpatialEnvelopeRayBanks`](../Unfoldings/Geometry/SpatialEnvelopeRayBanks.lean):
  construct two disjoint unbounded bank tails with exact folding and spatial distances.
- [`CompatibleTerminalBanks`](../Unfoldings/Roof/CompatibleTerminalBanks.lean):
  construct those actual terminal banks simultaneously for every compatible forest end.
