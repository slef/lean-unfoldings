# Library reference

Start with the [README](../README.md) for the main result and a usage example.
The [plan](../PLAN.md) tracks implemented features and remaining work;
the [log](../LOG.md) records proof-development milestones.

## Module index

Modules are grouped by topic and sorted by name. Each link opens the Lean
source, including its module documentation and declarations.

- [Source unfoldings](#source-unfoldings)
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
| [Unfoldings.Source.ConvexDomain](../Unfoldings/Source/ConvexDomain.lean) | Actual convex-boundary path-space homeomorphisms and surjective projection |
| [Unfoldings.Source.ConvexDomainInterior](../Unfoldings/Source/ConvexDomainInterior.lean) | Exact characterization of source-domain interior by regular retained endpoints |
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
| [Unfoldings.Source.Domain](../Unfoldings/Source/Domain.lean) | Compact planar path images and continuous endpoint projection |
| [Unfoldings.Source.DomainBoundary](../Unfoldings/Source/DomainBoundary.lean) | Exact boundary projection onto the closed cut union singular points |
| [Unfoldings.Source.DomainDensity](../Unfoldings/Source/DomainDensity.lean) | Every proper radial prefix is interior; its closure is the whole compact domain |
| [Unfoldings.Source.DomainInterior](../Unfoldings/Source/DomainInterior.lean) | Regular unique endpoints give actual interior source vectors |
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
| [Unfoldings.Source.Radial](../Unfoldings/Source/Radial.lean) | Injectivity from uniqueness of radial lifts |
| [Unfoldings.Source.RadialDomain](../Unfoldings/Source/RadialDomain.lean) | Exact prefix-vector scaling and star-shaped planar source images |
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

## Triangle complexes

| Module | Purpose |
| --- | --- |
| [Unfoldings.Complex](../Unfoldings/Complex.lean) | Finite edge-paired complexes and their cut realizations |
| [Unfoldings.Complex.Angles](../Unfoldings/Complex/Angles.lean) | Total angles and conservation across cut vertex copies |
| [Unfoldings.Complex.BoundaryQuotient](../Unfoldings/Complex/BoundaryQuotient.lean) | Compact actual bank boundaries and exact boundary-only fibers of seam restoration |
| [Unfoldings.Complex.Charts](../Unfoldings/Complex/Charts.lean) | Constructed face-interior Euclidean metric charts |
| [Unfoldings.Complex.Classes](../Unfoldings/Complex/Classes.lean) | Finite corner classes and unique nonvertex seam neighbors |
| [Unfoldings.Complex.Connectivity](../Unfoldings/Complex/Connectivity.lean) | Finite metrics and geodesics for connected face incidence |
| [Unfoldings.Complex.CutDisk](../Unfoldings/Complex/CutDisk.lean) | Boundary-preserving cut disks imply open-disk complements and tree bank-image graphs |
| [Unfoldings.Complex.CutGraph](../Unfoldings/Complex/CutGraph.lean) | Construct exact finite spatial embedded straight graphs of all unpaired bank images |
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
| [Unfoldings.Complex.Hinge](../Unfoldings/Complex/Hinge.lean) | Intrinsic upper bounds from local unfolded hinge chords |
| [Unfoldings.Complex.HingeCharts](../Unfoldings/Complex/HingeCharts.lean) | Constructed Euclidean metric balls at retained edge interiors |
| [Unfoldings.Complex.HingeCoordinates](../Unfoldings/Complex/HingeCoordinates.lean) | Local hinge frames and exact local distances |
| [Unfoldings.Complex.InteriorTags](../Unfoldings/Complex/InteriorTags.lean) | Original face-interior points have unique tagged representatives |
| [Unfoldings.Complex.LinkConnectivity](../Unfoldings/Complex/LinkConnectivity.lean) | Germ components are exactly metric vertex classes |
| [Unfoldings.Complex.LinkOrdering](../Unfoldings/Complex/LinkOrdering.lean) | Constructed link orders and their Euclidean angle sums |
| [Unfoldings.Complex.Links](../Unfoldings/Complex/Links.lean) | Vertex-link involutions and boundary fixed germs |
| [Unfoldings.Complex.Neighborhood](../Unfoldings/Complex/Neighborhood.lean) | Quantitative neighborhoods of two-face seam classes |
| [Unfoldings.Complex.Paths](../Unfoldings/Complex/Paths.lean) | Intrinsic path metric and geodesic existence for cut complexes |
| [Unfoldings.Complex.PointFiber](../Unfoldings/Complex/PointFiber.lean) | Exact point fibers have at most one copy per original face and bounded seam paths |
| [Unfoldings.Complex.PointSeamRoute](../Unfoldings/Complex/PointSeamRoute.lean) | Actual bounded oriented seam routes, including at vertices |
| [Unfoldings.Complex.Regular](../Unfoldings/Complex/Regular.lean) | Constructed regular points and unique intrinsic geodesic continuation |
| [Unfoldings.Complex.RegularEdges](../Unfoldings/Complex/RegularEdges.lean) | Constructed edge charts from either seam bank |
| [Unfoldings.Complex.SeamFaceRoute](../Unfoldings/Complex/SeamFaceRoute.lean) | Constructed entry/exit points and bounded seam resolutions of all face-route junctions |
| [Unfoldings.Complex.SeamWord](../Unfoldings/Complex/SeamWord.lean) | Finite oriented words construct rigid hinge placements agreeing at actual crossing points |
| [Unfoldings.Complex.SeamWordMotion](../Unfoldings/Complex/SeamWordMotion.lean) | Exact whole-motion propagation through finite oriented seam words |
| [Unfoldings.Complex.Star](../Unfoldings/Complex/Star.lean) | Actual vertex stars, conserved angles and local metric comparisons |
| [Unfoldings.Complex.Vertices](../Unfoldings/Complex/Vertices.lean) | Actual cut vertex classes, boundary incidence and copy maps |

## Cuts and layouts

| Module | Purpose |
| --- | --- |
| [Unfoldings.Boundary](../Unfoldings/Boundary.lean) | Boundary-edge labels, bank maps, and restoration of banks |
| [Unfoldings.Boundary.Charts](../Unfoldings/Boundary/Charts.lean) | Constructed half-ball metric charts at boundary edge interiors |
| [Unfoldings.Boundary.Exact](../Unfoldings/Boundary/Exact.lean) | Metric separation of distinct cut-bank interiors |
| [Unfoldings.Development](../Unfoldings/Development.lean) | Facewise placements, nonoverlap, multiplicity, and metric descent |
| [Unfoldings.Development.Hinge](../Unfoldings/Development/Hinge.lean) | Nonoverlapping developments of arbitrary two-triangle hinges |
| [Unfoldings.PolygonalLayout](../Unfoldings/PolygonalLayout.lean) | Finite polygon layouts with separate rigid face maps and optional nonoverlap |

## Metrics and gluing

| Module | Purpose |
| --- | --- |
| [Unfoldings.Metric.BallChart](../Unfoldings/Metric/BallChart.lean) | Whole metric-ball charts in a named model space |
| [Unfoldings.Metric.BallIsometry](../Unfoldings/Metric/BallIsometry.lean) | Restrict isometries to balls with specified centers |
| [Unfoldings.Metric.BallParametrization](../Unfoldings/Metric/BallParametrization.lean) | Whole-ball charts from isometric parametrizations with ball coverage |
| [Unfoldings.Metric.Barrier](../Unfoldings/Metric/Barrier.lean) | Capped distance separators and local class transport |
| [Unfoldings.Metric.CenterBounds](../Unfoldings/Metric/CenterBounds.lean) | Local center bounds imply global distance bounds on real intervals |
| [Unfoldings.Metric.ClosedSeams](../Unfoldings/Metric/ClosedSeams.lean) | Exactness for closed isometric seams with finite classes |
| [Unfoldings.Metric.Connected](../Unfoldings/Metric/Connected.lean) | Preconnected extended metric spaces have finite distances |
| [Unfoldings.Metric.Excision](../Unfoldings/Metric/Excision.lean) | Whole-ball isometries when cutting distant seams |
| [Unfoldings.Metric.FiniteComponent](../Unfoldings/Metric/FiniteComponent.lean) | Clopen finite-distance components as compact metric spaces |
| [Unfoldings.Metric.Gluing](../Unfoldings/Metric/Gluing.lean) | Metric quotient, descent, and restoration of seams |
| [Unfoldings.Metric.IsometricCells](../Unfoldings/Metric/IsometricCells.lean) | Compatible isometric cell maps exclude intrinsic cell shortcuts |
| [Unfoldings.Metric.Lipschitz](../Unfoldings/Metric/Lipschitz.lean) | Compatible Lipschitz cell maps descend through metric gluing |
| [Unfoldings.Metric.Local](../Unfoldings/Metric/Local.lean) | Seam clearance, metric ball images, and local cell isometries |
| [Unfoldings.Metric.LocalComposition](../Unfoldings/Metric/LocalComposition.lean) | Compose local isometries and obtain local center bounds |
| [Unfoldings.Metric.LocalInverse](../Unfoldings/Metric/LocalInverse.lean) | Constructed isometric inverse neighborhoods |
| [Unfoldings.Metric.LocalMap](../Unfoldings/Metric/LocalMap.lean) | Metric lower bounds from estimates on short local routes |
| [Unfoldings.Metric.LocalRigidMap](../Unfoldings/Metric/LocalRigidMap.lean) | A constructed local isometry has an actual rigid expression in any open Euclidean chart |
| [Unfoldings.Metric.LocalSeams](../Unfoldings/Metric/LocalSeams.lean) | Local estimates from compatibility at incident closed seams |
| [Unfoldings.Metric.OpenChart](../Unfoldings/Metric/OpenChart.lean) | Recenter open isometric charts on whole ambient balls |
| [Unfoldings.Metric.Paths](../Unfoldings/Metric/Paths.lean) | Continuous-path/route metric equality and shortest metric paths |
| [Unfoldings.Metric.Polygonal](../Unfoldings/Metric/Polygonal.lean) | Constructed intrinsic metrics from allowed straight steps and nonexpanding inclusions |
| [Unfoldings.Metric.PolygonalCompletion](../Unfoldings/Metric/PolygonalCompletion.lean) | Isometric dense interior inclusion and complete compact closed-domain model |
| [Unfoldings.Metric.PolygonalLocal](../Unfoldings/Metric/PolygonalLocal.lean) | Isometric neighborhoods for the development and its inverse on open regions |
| [Unfoldings.Metric.PolygonalMap](../Unfoldings/Metric/PolygonalMap.lean) | Local center bounds descend to intrinsic polygonal metrics |
| [Unfoldings.Metric.PolygonalPaths](../Unfoldings/Metric/PolygonalPaths.lean) | Straight-step geodesics and equality of route and continuous-path distance |
| [Unfoldings.Metric.PolygonalStar](../Unfoldings/Metric/PolygonalStar.lean) | Radial contraction identifies intrinsic and ambient topology through the boundary |
| [Unfoldings.Metric.Quotient](../Unfoldings/Metric/Quotient.lean) | Declared seam classes, exactness, compactness, and completeness |
| [Unfoldings.Metric.RegularGeodesic](../Unfoldings/Metric/RegularGeodesic.lean) | A whole regular chart supplies a nonconstant geodesic through its center |
| [Unfoldings.Metric.RegularLocus](../Unfoldings/Metric/RegularLocus.lean) | Metric regularity is open and open charts recenter to whole metric balls |
| [Unfoldings.Metric.RigidChartTransition](../Unfoldings/Metric/RigidChartTransition.lean) | Construct rigid affine transitions between actual overlapping metric charts |
| [Unfoldings.Metric.Route](../Unfoldings/Metric/Route.lean) | Finite routes and the generated extended pseudometric |
| [Unfoldings.Metric.Unglued](../Unfoldings/Metric/Unglued.lean) | Exact metric formulas and separation with no seams |

## Paths and geodesics

| Module | Purpose |
| --- | --- |
| [Unfoldings.Path.AffineSamples](../Unfoldings/Path/AffineSamples.lean) | Continue geodesic coordinate identities across a whole chart interval |
| [Unfoldings.Path.Chart](../Unfoldings/Path/Chart.lean) | Straight coordinates and uniqueness in isometric charts |
| [Unfoldings.Path.ChartPartition](../Unfoldings/Path/ChartPartition.lean) | Finite strictly ordered chart partitions of actual regular paths |
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
| [Unfoldings.Path.Subpath](../Unfoldings/Path/Subpath.lean) | Affine constant-speed subpaths, including reversed intervals |
| [Unfoldings.Path.SubpathBounds](../Unfoldings/Path/SubpathBounds.lean) | Strict subpath-time bounds and density of proper unit-interval times |

## Convex polyhedra

| Module | Purpose |
| --- | --- |
| [Unfoldings.Polyhedron.Chords](../Unfoldings/Polyhedron/Chords.lean) | Exact boundary-chord distances and unique intrinsic geodesics |
| [Unfoldings.Polyhedron.Closedness](../Unfoldings/Polyhedron/Closedness.lean) | Derived seam pairing of every original edge and cyclicity at every vertex |
| [Unfoldings.Polyhedron.Convex](../Unfoldings/Polyhedron/Convex.lean) | Geometric convex-boundary adapter and derived geodesics |
| [Unfoldings.Polyhedron.ConvexCurvature](../Unfoldings/Polyhedron/ConvexCurvature.lean) | Extremality iff positive curvature and avoidance, with no interior premise |
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
| [Unfoldings.Polyhedron.VertexSlice](../Unfoldings/Polyhedron/VertexSlice.lean) | Constructed nonempty transverse sections at spatial extreme vertices |
| [Unfoldings.Polyhedron.VertexSliceInterior](../Unfoldings/Polyhedron/VertexSliceInterior.lean) | Actual vertex sections with a spatial interior center |

## Cone geometry

| Module | Purpose |
| --- | --- |
| [Unfoldings.Cone.AngularChord](../Unfoldings/Cone/AngularChord.lean) | Exact intrinsic lengths of covered chords in reentrant fans |
| [Unfoldings.Cone.AngularCoordinates](../Unfoldings/Cone/AngularCoordinates.lean) | Closed headings, bank coordinates and full-plane coverage |
| [Unfoldings.Cone.AngularFan](../Unfoldings/Cone/AngularFan.lean) | Slit sector fans, cumulative real headings and planar developments |
| [Unfoldings.Cone.AngularFibers](../Unfoldings/Cone/AngularFibers.lean) | All closed-bank fibers at one full turn |
| [Unfoldings.Cone.AngularHeadingShortcut](../Unfoldings/Cone/AngularHeadingShortcut.lean) | Strict shortcuts across multiple angular pieces |
| [Unfoldings.Cone.AngularImages](../Unfoldings/Cone/AngularImages.lean) | Genuine rigid piece images and their open heading intervals |
| [Unfoldings.Cone.AngularInjective](../Unfoldings/Cone/AngularInjective.lean) | Boundary-inclusive development injectivity below a full turn |
| [Unfoldings.Cone.AngularMetric](../Unfoldings/Cone/AngularMetric.lean) | Common fan apex, exact radial distances and ordinary metric |
| [Unfoldings.Cone.AngularOverlap](../Unfoldings/Cone/AngularOverlap.lean) | Exact nonoverlap criterion and arbitrary-radius interior overlaps |
| [Unfoldings.Cone.AngularSector](../Unfoldings/Cone/AngularSector.lean) | Exact Euclidean sector metric when total angle is less than pi |
| [Unfoldings.Cone.AngularShortcut](../Unfoldings/Cone/AngularShortcut.lean) | Strict intrinsic shortcuts and apex avoidance in convex angular fans |
| [Unfoldings.Cone.Apex](../Unfoldings/Cone/Apex.lean) | Common tangent apex derived from vertex-link connectivity |
| [Unfoldings.Cone.AppendFirst](../Unfoldings/Cone/AppendFirst.lean) | A repeated first sector with exact continued real headings |
| [Unfoldings.Cone.AppendMap](../Unfoldings/Cone/AppendMap.lean) | Nonexpanding cyclic maps continued across their closing bank |
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
| [Unfoldings.Cone.Polar](../Unfoldings/Cone/Polar.lean) | Real-heading polar maps, exact injectivity criterion and overlap witnesses |
| [Unfoldings.Cone.PolarEquality](../Unfoldings/Cone/PolarEquality.lean) | Equality of closed full-turn polar coordinates, including outer banks |
| [Unfoldings.Cone.Proper](../Unfoldings/Cone/Proper.lean) | Compact closed tangent balls, properness and completeness |
| [Unfoldings.Cone.Radial](../Unfoldings/Cone/Radial.lean) | Exact radial distance and finite ordinary tangent metric |
| [Unfoldings.Cone.SeamBoundary](../Unfoldings/Cone/SeamBoundary.lean) | Actual radial banks of retained seams |
| [Unfoldings.Cone.SeamCoordinates](../Unfoldings/Cone/SeamCoordinates.lean) | Directed angular coordinates of every actual radial seam point |
| [Unfoldings.Cone.SeamRadius](../Unfoldings/Cone/SeamRadius.lean) | Actual radial seam witnesses at every nonnegative radius |
| [Unfoldings.Cone.Sector](../Unfoldings/Cone/Sector.lean) | Real-angle sectors as positive spans of their boundary rays |
| [Unfoldings.Cone.SectorClosed](../Unfoldings/Cone/SectorClosed.lean) | Closed polar coordinates for sectors and the whole plane |
| [Unfoldings.Cone.SectorCoordinates](../Unfoldings/Cone/SectorCoordinates.lean) | Positive-span sectors, ambient coordinates and interiors |
| [Unfoldings.Cone.SectorInterior](../Unfoldings/Cone/SectorInterior.lean) | Positive-radius open-heading coordinates for actual sector interiors |
| [Unfoldings.Cone.SectorReflection](../Unfoldings/Cone/SectorReflection.lean) | Isometric bank exchange by angular-bisector reflection |
| [Unfoldings.Cone.SectorShortcut](../Unfoldings/Cone/SectorShortcut.lean) | Strict chord shortcuts for nonzero points of pointed sectors |
| [Unfoldings.Cone.SmallDilation](../Unfoldings/Cone/SmallDilation.lean) | One positive scale places any two tangent points in an apex ball |
| [Unfoldings.Cone.Spatial](../Unfoldings/Cone/Spatial.lean) | Extended spatial foldings and tangent-cell isometries |
| [Unfoldings.Cone.SpatialConvexLift](../Unfoldings/Cone/SpatialConvexLift.lean) | Isometric inverse tangent folding on every convex spatial subset |
| [Unfoldings.Cone.SpatialEmbedding](../Unfoldings/Cone/SpatialEmbedding.lean) | Proper tangent folding and closed spatial embeddings of actual uncut fans |
| [Unfoldings.Cone.SpatialHinge](../Unfoldings/Cone/SpatialHinge.lean) | Transfer entire spatial hinge parametrizations to intrinsic metric charts |
| [Unfoldings.Cone.SpatialParametrization](../Unfoldings/Cone/SpatialParametrization.lean) | Finite piecewise rigid spatial parametrizations give intrinsic tangent isometries |
| [Unfoldings.Cone.SpatialRange](../Unfoldings/Cone/SpatialRange.lean) | Exact radial homogeneity of the actual tangent image |
| [Unfoldings.Cone.SurfaceComparison](../Unfoldings/Cone/SurfaceComparison.lean) | Local metric comparison from tangent fans to original surfaces |
| [Unfoldings.Cone.SurfaceTags](../Unfoldings/Cone/SurfaceTags.lean) | Local maps from tangent wedges into original triangle cells |
| [Unfoldings.Cone.Tangent](../Unfoldings/Cone/Tangent.lean) | Actual wedge cells and radially extended seam gluings |
| [Unfoldings.Cone.TangentAngularCells](../Unfoldings/Cone/TangentAngularCells.lean) | Directed angular coordinates on every actual tangent cell |
| [Unfoldings.Cone.TangentComparison](../Unfoldings/Cone/TangentComparison.lean) | Local metric comparison from original surfaces to tangent fans |
| [Unfoldings.Cone.TangentShortcut](../Unfoldings/Cone/TangentShortcut.lean) | Strict apex shortcuts for all actual positive-curvature tangent pairs |
| [Unfoldings.Cone.TriangleInclusion](../Unfoldings/Cone/TriangleInclusion.lean) | Original triangles included in their actual tangent wedges |
| [Unfoldings.Cone.VertexAvoidance](../Unfoldings/Cone/VertexAvoidance.lean) | Original intrinsic geodesics avoid positive-curvature interior vertices |

## Euclidean geometry

| Module | Purpose |
| --- | --- |
| [Unfoldings.Geometry.AdjacentBoundaryEdges](../Unfoldings/Geometry/AdjacentBoundaryEdges.lean) | Simple convex boundary edges keep the same radial orientation |
| [Unfoldings.Geometry.Affine](../Unfoldings/Geometry/Affine.lean) | Rigid edge extensions and line reflection |
| [Unfoldings.Geometry.AffineArrangement](../Unfoldings/Geometry/AffineArrangement.lean) | General finite affine chamber covers of regular closed sets |
| [Unfoldings.Geometry.AffineEnd](../Unfoldings/Geometry/AffineEnd.lean) | Finite-dimensional rigid self-embeddings are surjective and open |
| [Unfoldings.Geometry.AffineMaximum](../Unfoldings/Geometry/AffineMaximum.lean) | Local maxima force affine functionals to be constant |
| [Unfoldings.Geometry.AffineOrientation](../Unfoldings/Geometry/AffineOrientation.lean) | Affine signed-area scaling and rigid preservation of relative signs |
| [Unfoldings.Geometry.AffinePlaneRange](../Unfoldings/Geometry/AffinePlaneRange.lean) | Common-point affine planes agree when their linear directions agree |
| [Unfoldings.Geometry.AffineSupport](../Unfoldings/Geometry/AffineSupport.lean) | Nonzero affine equations for genuine bisectors and triangle edge lines |
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
| [Unfoldings.Geometry.ConvexPatchRigidity](../Unfoldings/Geometry/ConvexPatchRigidity.lean) | Overlapping convex face patches force equality of their whole rigid motions |
| [Unfoldings.Geometry.ConvexRigidity](../Unfoldings/Geometry/ConvexRigidity.lean) | Actual isometries on convex sets with interior extend rigidly through the boundary |
| [Unfoldings.Geometry.Corner](../Unfoldings/Geometry/Corner.lean) | Supporting wedges and actual corner wedge-ball geometry |
| [Unfoldings.Geometry.CornerEdges](../Unfoldings/Geometry/CornerEdges.lean) | Radial edge lines inside a triangle remain on the actual edge |
| [Unfoldings.Geometry.CornerFrame](../Unfoldings/Geometry/CornerFrame.lean) | Constructed rigid apex/first-ray/upper-side normalization |
| [Unfoldings.Geometry.CornerSpan](../Unfoldings/Geometry/CornerSpan.lean) | Unique boundary-ray coordinates and actual wedge interiors |
| [Unfoldings.Geometry.Edge](../Unfoldings/Geometry/Edge.lean) | Edge intersections and endpoint preservation by isometries |
| [Unfoldings.Geometry.EdgeChordInterior](../Unfoldings/Geometry/EdgeChordInterior.lean) | Chords between different edge interiors enter a triangle interior |
| [Unfoldings.Geometry.EdgeLine](../Unfoldings/Geometry/EdgeLine.lean) | Affine edge agreement extends to the entire supporting line |
| [Unfoldings.Geometry.EdgeParameters](../Unfoldings/Geometry/EdgeParameters.lean) | Strict edge interpolation avoids all original triangle vertices |
| [Unfoldings.Geometry.EdgePerfect](../Unfoldings/Geometry/EdgePerfect.lean) | Every neighborhood in a genuine closed edge contains a nonvertex point |
| [Unfoldings.Geometry.EdgeSides](../Unfoldings/Geometry/EdgeSides.lean) | Edge membership and proportional supporting coordinates |
| [Unfoldings.Geometry.Endpoints](../Unfoldings/Geometry/Endpoints.lean) | Endpoint permutations induced by full-edge isometries |
| [Unfoldings.Geometry.ExtremeSeparation](../Unfoldings/Geometry/ExtremeSeparation.lean) | Strict finite-hull supporting functionals with a uniform margin |
| [Unfoldings.Geometry.FiniteAffineSelection](../Unfoldings/Geometry/FiniteAffineSelection.lean) | Proper affine supports for coincidences and constancy of finite continuous affine selections |
| [Unfoldings.Geometry.FiniteAngles](../Unfoldings/Geometry/FiniteAngles.lean) | Every nonempty finite point list has a nonstraight chosen corner |
| [Unfoldings.Geometry.FrontierProjection](../Unfoldings/Geometry/FrontierProjection.lean) | Continuous gauge projection from an actual body interior point |
| [Unfoldings.Geometry.FrontierRays](../Unfoldings/Geometry/FrontierRays.lean) | Gauge-normalized frontier rays and disjoint positive radial hulls |
| [Unfoldings.Geometry.FunctionalHomothety](../Unfoldings/Geometry/FunctionalHomothety.lean) | Positive homotheties preserve support levels and half-spaces |
| [Unfoldings.Geometry.FunctionalPlane](../Unfoldings/Geometry/FunctionalPlane.lean) | Constructed affine Euclidean coordinates on nonzero functional level planes |
| [Unfoldings.Geometry.Halfplane](../Unfoldings/Geometry/Halfplane.lean) | Supporting heights and finite corner bounds |
| [Unfoldings.Geometry.Hinge](../Unfoldings/Geometry/Hinge.lean) | Opposite sides imply adjacent-cell nonoverlap |
| [Unfoldings.Geometry.HingePatch](../Unfoldings/Geometry/HingePatch.lean) | Exact hinge intersections and local planar coverage |
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
| [Unfoldings.Geometry.RadialSlice](../Unfoldings/Geometry/RadialSlice.lean) | Actual compact convex level sections and radial generator projections |
| [Unfoldings.Geometry.RadialSliceAngles](../Unfoldings/Geometry/RadialSliceAngles.lean) | Positive radial slicing preserves affine apex angles |
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
| [Unfoldings.Geometry.Triangle](../Unfoldings/Geometry/Triangle.lean) | Nondegenerate cells and full edge subspaces |
| [Unfoldings.Geometry.TriangleBoundary](../Unfoldings/Geometry/TriangleBoundary.lean) | Every noninterior closed triangle point lies on an actual edge |
| [Unfoldings.Geometry.UnitLine](../Unfoldings/Geometry/UnitLine.lean) | A nonzero real line has two opposite unit directions |

## Topology and combinatorics

| Module | Purpose |
| --- | --- |
| [Unfoldings.Combinatorics.FiniteReach](../Unfoldings/Combinatorics/FiniteReach.lean) | Bounded rounds of finite choices give a finite set of reachable states |
| [Unfoldings.Topology.BallBoundaryQuotient](../Unfoldings/Topology/BallBoundaryQuotient.lean) | Disk quotients have open-disk complements; spherical targets force boundary graphs to be trees |
| [Unfoldings.Topology.BoundaryQuotient](../Unfoldings/Topology/BoundaryQuotient.lean) | Boundary-only quotient maps, complement homeomorphisms, and descended boundary retractions |
| [Unfoldings.Topology.ChainPairings](../Unfoldings/Topology/ChainPairings.lean) | Every link pairing is consecutive or closes the outer banks |
| [Unfoldings.Topology.CommonFibers](../Unfoldings/Topology/CommonFibers.lean) | Compact quotient maps with the same fibers identify their targets |
| [Unfoldings.Topology.ContractibleLift](../Unfoldings/Topology/ContractibleLift.lean) | Covering-space lifts from contractible domains, without local path-connectedness assumptions |
| [Unfoldings.Topology.ConvexBoundary](../Unfoldings/Topology/ConvexBoundary.lean) | Sphere topology and connectedness of bounded convex boundaries |
| [Unfoldings.Topology.CyclicLabels](../Unfoldings/Topology/CyclicLabels.lean) | Nonconstant cyclic lists have no more labels than changes |
| [Unfoldings.Topology.FiberGraph](../Unfoldings/Topology/FiberGraph.lean) | Equivalence chains in finite fibers yield short simple graph paths |
| [Unfoldings.Topology.FiniteClasses](../Unfoldings/Topology/FiniteClasses.lean) | Finite equivalence classes from finitely many branching points |
| [Unfoldings.Topology.FiniteEmbeddedGraph](../Unfoldings/Topology/FiniteEmbeddedGraph.lean) | Finite embedded multigraphs, compact carriers, and topological-to-graph connectedness |
| [Unfoldings.Topology.FiniteIntervalCover](../Unfoldings/Topology/FiniteIntervalCover.lean) | Bounded subdivisions subordinate to finite closed interval covers |
| [Unfoldings.Topology.FiniteSubdivision](../Unfoldings/Topology/FiniteSubdivision.lean) | Existence and uniqueness of consecutive marked real intervals |
| [Unfoldings.Topology.GraphAcyclic](../Unfoldings/Topology/GraphAcyclic.lean) | Contractible finite embedded graphs are simple and their adjacency graphs are trees |
| [Unfoldings.Topology.GraphExtension](../Unfoldings/Topology/GraphExtension.lean) | Continuous extension of compatible vertex and edge maps to the actual graph carrier |
| [Unfoldings.Topology.GraphPoints](../Unfoldings/Topology/GraphPoints.lean) | Vertex points and continuous edge inclusions into the embedded graph carrier |
| [Unfoldings.Topology.GraphPotential](../Unfoldings/Topology/GraphPotential.lean) | Selected-edge circle winding maps and real vertex potentials from contractibility |
| [Unfoldings.Topology.PairedInvolutions](../Unfoldings/Topology/PairedInvolutions.lean) | Generic finite interval/cycle order from two involutions |
| [Unfoldings.Topology.PerfectProjection](../Unfoldings/Topology/PerfectProjection.lean) | A perfect boundary cannot project injectively to finite exceptions outside a closed set |
| [Unfoldings.Topology.PuncturedSphere](../Unfoldings/Topology/PuncturedSphere.lean) | Contractibility of a unit sphere punctured at any specified point |
| [Unfoldings.Topology.QuotientRetraction](../Unfoldings/Topology/QuotientRetraction.lean) | Continuous quotient descent and contractibility of retracts |

## Examples and core imports

| Module | Purpose |
| --- | --- |
| [Audit](../Audit.lean) | Transitive axiom check for all imported library declarations |
| [Unfoldings](../Unfoldings.lean) | Public umbrella import for the library |
| [Unfoldings.Basic](../Unfoldings/Basic.lean) | Common Euclidean plane and spatial coordinate types |
| [Unfoldings.Examples.Hinge](../Unfoldings/Examples/Hinge.lean) | Joined hinges, boundary contact, and a layout with interior overlap |
| [Unfoldings.Examples.Metric](../Unfoldings/Examples/Metric.lean) | Metric recovery, disconnectedness, and shortcuts |

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
It rejects unfinished proofs and native-decision axioms.

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
