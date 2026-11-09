# Unfoldings

A Lean library for polyhedral metrics, cuts, and planar developments, with source
unfolding of convex polyhedra as its first major target. Overlapping developments
are supported; nonoverlap is a separate property and permits boundary contacts.

The design and feature checklist are in [PLAN.md](PLAN.md). The regular source
development, its intrinsic boundary completion and disk topology are constructed;
finite cut-graph characterizations remain in progress.
The initial library has no placeholder propositions or unfinished proofs.

## Current interfaces

- `Route.distance` constructs extended distance from finite routes. It satisfies
  the metric inequalities and is maximal among pseudometrics bounded by the
  allowed step costs.
- `MetricGluing.Realization` glues a family of metric cells using that distance.
  Compatible nonexpanding maps descend uniquely. Removing seams cannot shorten
  distance. Disconnected cells can remain infinitely far apart.
- `MetricGluing.SeamQuotient` identifies exactly finite chains of declared seams.
  It maps continuously and surjectively to the metric realization. `Exact`
  states that this map is injective; compatible nonexpanding coordinates can
  certify it. For finite compact cells the metric realization is compact and
  complete, and exactness gives a homeomorphism with the seam quotient.
  `ClosedSeams.exact_of_finite_classes` proves exactness for finitely many
  closed isometric seams with finite equivalence classes, using capped distance
  barriers; the cells themselves need not be compact.
- `TriangleComplex` describes finitely many nondegenerate Euclidean triangles
  and whole-edge isometric equivalences, with each edge in at most one pair.
  Its metric realization depends on an explicit set of retained seams.
  `BoundaryBank` labels the unpaired local edges. Cutting a seam gives two
  distinct bank labels; restoring it identifies their metric images pointwise.
  With every seam cut, exactness and isometric face maps are proved.
  `TriangleComplex.exact` proves exactness for every retained-seam set, and
  `realizationHomeomorph` identifies the metric and cell-quotient topologies.
  `FaceChart` constructs Euclidean metric-ball charts at all face-interior
  points. Distinct boundary-bank interiors have distinct metric images.
  Route distance equals continuous-path distance, and every finite distance
  is attained by a constant-speed metric geodesic.
  `BoundaryChart` constructs metric half-ball charts at all nonvertex boundary
  bank points. `HingeChart` constructs whole Euclidean ball charts at nonvertex
  retained-seam points with distinct incident faces, agreeing with both faces
  in outward hinge coordinates. Connected retained face incidence gives finite
  distances, an ordinary intrinsic metric, and geodesics between every pair.
  `Vertex` is the finite quotient of tagged corners by retained seam chains,
  with injective metric images and explicit maps between cut copies. Its total
  angles use the actual Euclidean corner angles and are conserved under cuts.
  Vertex-link orders are constructed from endpoint transport: interior links
  are cyclic and boundary links are intervals with exactly two unpaired germs.
  Each incident corner is listed once, including self-pairings and loop links.
  Cutting all seams away from a chosen vertex preserves its corner class,
  total angle and a whole small intrinsic ball. Original corner neighborhoods
  are convex supporting wedges. `TangentFan` glues their radial seam extensions
  with a constructed proper, complete metric and exact radial distance.
  Its continuous-path metric agrees, explicit radial paths are geodesics, and
  spatial foldings extend to it. `TangentChart` constructs an isometry between
  whole small tangent and original vertex balls whenever a spatial folding is
  supplied, agreeing with every incident face coordinate. Radial dilations
  multiply all intrinsic distances by their scale; positive scales have
  reciprocal homeomorphisms. Every actual wedge now has a rigid angular sector
  isometry at its genuine corner angle. Slit angular fans have constructed
  metrics and developments at every total angle. Every actual boundary tangent
  fan is isometric to its angular model, without a spatial-folding hypothesis.
  Full-turn cyclic tangent fans are isometric to the Euclidean plane.
  Spatially folded complexes therefore have constructed whole Euclidean ball
  charts at flat interior vertices, agreeing with their incident face coordinates.
  Strict cyclic shortcuts, including across a chosen slit, prove that nonconstant
  geodesics avoid positive-curvature interior vertices at all interior times.
- Slit angular fans have pairwise disjoint genuine piece interiors **iff** their
  total angle is at most a full turn. At equality the developed outer banks
  coincide. Above a full turn, two piece interiors overlap at every positive radius.
- `FacewiseDevelopment` places each original triangle exactly once, agrees on
  retained edges, and puts the incident triangles on opposite sides. Retained
  dual cycles are allowed. The map descends to the cut realization and is
  nonexpanding, even with global overlap.
- `FacewiseDevelopment.Nonoverlapping` means disjoint face interiors and is
  equivalent to multiplicity at most one. Linear separators checked on corners
  certify whole-cell nonoverlap.
- `Hinge.development` constructs a nonoverlapping development of any two
  triangles with a full-edge isometric pairing. The construction extends the
  edge isometry to a rigid motion and reflects it if needed to open outward.
- `SourceFrame` constructs full-length planar vectors from actual shortest paths
  starting at any regular source. Vector norms equal source distance. On convex
  boundaries the vectors distinguish all shortest paths, retaining tied paths
  at cut-locus endpoints. Uniform convergence makes the whole shortest-path
  space compact; its coordinates identify it homeomorphically with a compact,
  star-shaped planar image. Endpoint projection is continuous and surjective.
  Every proper positive-time prefix is proved unique by an actual geodesic
  splice and continuation from its unchanged tail.
  `sourceCutLocus` is the closure of nonunique endpoints and misses a whole
  source ball. Off the closed cut locus, the unique shortest path varies
  continuously; its actual source coordinates are continuous and injective,
  and are locally isometric at every regular retained point. Terminal affine
  charts are constructed along whole regular paths and uniformly for nearby
  shortest paths. Every proper prefix avoids the closed cut locus; the retained
  shortest paths are constructed and develop to exact radial segments. Inclusion
  of extreme cone endpoints follows from the boundary-circle theorem and
  finiteness of singular vertices, including unique incoming cone leaves.
  Finite cut-locus tree structure remains open. The compact planar domain is
  the closure of its star-shaped interior, and the flat retained surface is
  homeomorphic to that interior by its actual locally isometric source coordinates.
  Boundary projection is exactly the closed cut locus union singular points,
  recorded explicitly as `sourceSlitSet`.
  The cone-leaf theorem proves this slit set equals `sourceCutLocus` itself;
  the retained surface is exactly its complement.
  The polygonal cut metric equals continuous-path distance in the original
  retained surface. Its completion is the compact closed source domain with
  its intrinsic metric: the interior includes isometrically and densely.
  The completed development is injective and nonexpanding, and the endpoint
  projection is continuous, surjective and nonexpanding. The completed net is
  homeomorphic to the closed disk, carrying exactly its boundary to the unit
  circle. Its radial geodesics project to every original shortest path, with
  source distances preserved at every boundary copy. Finite polygonal boundary
  descriptions remain open.
- `SpatialFolding` gives compatible rigid placements into three-dimensional
  space. Every original face is isometric for every cut metric. Spatial
  injectivity is separate and gives a homeomorphism onto the triangle union.
  `SpatialFolding.ConvexBoundary` requires that this union be the frontier of
  its actual finite corner hull, with nonempty spatial interior. Sphere topology,
  connectedness, finite intrinsic distance and geodesics are derived. Flat
  subdivision corners are allowed; a separate maximal-facet API remains open.
  Every spatial chord contained in the boundary has exact intrinsic length
  and a unique geodesic, across any number of subdivision triangles.
  Every geodesic has a constructed finite face partition with at most
  `2 * card Face + 1` pieces, exact spatial affine coordinates, and exact total
  chord length.
  Every original edge is proved paired and every original vertex link cyclic.
  At all triangulation vertices, spatial extremality is equivalent to
  total angle below `2π`. Nonconstant geodesics avoid these extreme vertices
  at interior times. Every nonextreme subdivision vertex has a constructed
  Euclidean metric-ball chart, including genuine creases. Consequently every
  interior point of a nonconstant geodesic is regular and initial agreement
  forces unique continuation. Numerical angle equality at nonextreme vertices
  remains open. Actual regular points are exactly the complement of true
  extreme vertex points, by a constructed geodesic through every regular center.
  Every nonvertex point has a constructed face or hinge Euclidean chart.
  Extreme vertices have constructed compact convex planar vertex figures,
  with finite noncollinear generators and actual interior centers. Their
  boundaries are exactly the slice-plane intersections with the surface,
  covered by radial segments from the incident original triangles. The actual
  cyclic link gives a simple Mathlib polygon. Its central fan makes exactly
  one turn; its polygon angle sum and the strict lateral pyramid budget prove
  the genuine surface angle bound, including flat facet subdivisions.
- Shortest paths on embedded surfaces cannot leave and re-enter a closed original
  face: each face visit is one closed parameter interval. Saturated nonexpanding
  images of geodesics are proved to be affine straight paths.
  Constructed face, hinge and flat-vertex ball charts certify regular points.
  Two geodesics sharing an initial interval have the same continuation through
  regular points, proved by chart straightness and continuous induction.
- `Path.eLength` measures continuous paths by total variation, allowing
  infinite length. Reversal, concatenation, Lipschitz bounds and invariance
  under isometries are proved independently of polyhedra. Rectifiable paths
  have bounded-speed replacements with the same image. In compact extended
  metric spaces they admit shortest replacements, comparing against every
  continuous competitor.
- `injective_of_radial_paths` proves injectivity of a locally injective map
  when paths from one fixed source develop to radial segments. This isolates
  the eventual source-unfolding argument without assuming shortest-path or
  cut-locus existence.

The facewise interface enforces local opening at edges. Unbranched local
isometry at uncut vertices will be part of the later surface-development layer,
after vertex links and surface interiors are constructed.

For arbitrary gluing data the separation quotient may identify more points than
the generated seam equivalence; a checked example demonstrates this. For finite
triangle complexes, exactness, compactness, completeness, and agreement with
the cell-quotient topology are all proved. Face maps are unconditionally
nonexpanding; a consistent rigid development strengthens them to isometries.
Vertex charts without a spatial folding, self-paired-edge charts, and the full
manifold conditions remain open.

## Module map

| Module | Purpose |
| --- | --- |
| `Unfoldings.Metric.Route` | Finite routes and the generated extended pseudometric |
| `Unfoldings.Metric.Gluing` | Metric quotient, descent, and restoration of seams |
| `Unfoldings.Metric.Quotient` | Declared seam classes, exactness, compactness, and completeness |
| `Unfoldings.Metric.Unglued` | Exact metric formulas and separation with no seams |
| `Unfoldings.Metric.Barrier` | Capped distance separators and local class transport |
| `Unfoldings.Metric.ClosedSeams` | Exactness for closed isometric seams with finite classes |
| `Unfoldings.Metric.Local` | Seam clearance, metric ball images, and local cell isometries |
| `Unfoldings.Metric.LocalSeams` | Local estimates from compatibility at incident closed seams |
| `Unfoldings.Metric.LocalMap` | Metric lower bounds from estimates on short local routes |
| `Unfoldings.Metric.FiniteComponent` | Clopen finite-distance components as compact metric spaces |
| `Unfoldings.Metric.Paths` | Continuous-path/route metric equality and shortest metric paths |
| `Unfoldings.Geometry.Triangle` | Nondegenerate cells and full edge subspaces |
| `Unfoldings.Geometry.Edge` | Edge intersections and endpoint preservation by isometries |
| `Unfoldings.Geometry.Halfplane` | Supporting heights and finite corner bounds |
| `Unfoldings.Geometry.Interior` | Interior clearance and Euclidean cell balls |
| `Unfoldings.Geometry.Barycentric` | Affine coordinates and local edge half-planes |
| `Unfoldings.Geometry.EdgeSides` | Edge membership and proportional supporting coordinates |
| `Unfoldings.Geometry.HingePatch` | Exact hinge intersections and local planar coverage |
| `Unfoldings.Geometry.Paths` | Straight paths in triangle cells with exact Euclidean length |
| `Unfoldings.Geometry.Affine` | Rigid edge extensions and line reflection |
| `Unfoldings.Geometry.Placement` | Constructed strict outward hinge placements |
| `Unfoldings.Complex` | Finite edge-paired complexes and their cut realizations |
| `Unfoldings.Complex.Classes` | Finite corner classes and unique nonvertex seam neighbors |
| `Unfoldings.Complex.Exact` | Exact metric identifications and quotient homeomorphism |
| `Unfoldings.Complex.Charts` | Constructed face-interior Euclidean metric charts |
| `Unfoldings.Complex.Paths` | Intrinsic path metric and geodesic existence for cut complexes |
| `Unfoldings.Complex.Neighborhood` | Quantitative neighborhoods of two-face seam classes |
| `Unfoldings.Topology.ConvexBoundary` | Sphere topology and connectedness of bounded convex boundaries |
| `Unfoldings.Cone.Tangent` | Actual wedge cells and radially extended seam gluings |
| `Unfoldings.Cone.Apex` | Common tangent apex derived from vertex-link connectivity |
| `Unfoldings.Cone.Radial` | Exact radial distance and finite ordinary tangent metric |
| `Unfoldings.Cone.Proper` | Compact closed tangent balls, properness and completeness |
| `Unfoldings.Cone.Paths` | Intrinsic path metric and explicit radial geodesics |
| `Unfoldings.Cone.Spatial` | Extended spatial foldings and tangent-cell isometries |
| `Unfoldings.Cone.Charts` | Constructed whole-ball cone charts for spatial foldings |
| `Unfoldings.Cone.Dilation` | Exact radial similarities and reciprocal homeomorphisms |
| `Unfoldings.Geometry.ConvexCover` | Common Lipschitz bounds across finite closed covers |
| `Unfoldings.Geometry.CornerSpan` | Unique boundary-ray coordinates and actual wedge interiors |
| `Unfoldings.Cone.LinkSeams` | Actual retained radial seams along ordered corner chains |
| `Unfoldings.Cone.Polar` | Real-heading polar maps, exact injectivity criterion and overlap witnesses |
| `Unfoldings.Cone.SectorCoordinates` | Positive-span sectors, ambient coordinates and interiors |
| `Unfoldings.Geometry.CornerFrame` | Constructed rigid apex/first-ray/upper-side normalization |
| `Unfoldings.Cone.CornerSector` | Actual triangle wedges isometric to their angular sectors |
| `Unfoldings.Cone.AngularFan` | Slit sector fans, cumulative real headings and planar developments |
| `Unfoldings.Cone.AngularMetric` | Common fan apex, exact radial distances and ordinary metric |
| `Unfoldings.Cone.LinkAngles` | Genuine angle lists from the constructed retained-link order |
| `Unfoldings.Cone.SectorReflection` | Isometric bank exchange by angular-bisector reflection |
| `Unfoldings.Cone.CornerDirection` | Actual corner frames oriented by the chosen initial germ |
| `Unfoldings.Cone.SeamRadius` | Actual radial seam witnesses at every nonnegative radius |
| `Unfoldings.Cone.GermFrames` | Exact initial/terminal coordinates on the actual radial banks |
| `Unfoldings.Cone.LinkComparison` | Surjective nonexpanding angular-to-tangent comparison |
| `Unfoldings.Cone.SectorInterior` | Positive-radius open-heading coordinates for actual sector interiors |
| `Unfoldings.Cone.AngularImages` | Genuine rigid piece images and their open heading intervals |
| `Unfoldings.Cone.AngularOverlap` | Exact nonoverlap criterion and arbitrary-radius interior overlaps |
| `Unfoldings.Topology.ChainPairings` | Every link pairing is consecutive or closes the outer banks |
| `Unfoldings.Cone.TangentAngularCells` | Directed angular coordinates on every actual tangent cell |
| `Unfoldings.Cone.IntervalSeams` | Every interval-link radial seam is consecutive |
| `Unfoldings.Cone.IntervalCompatibility` | Actual seams respect the inverse interval comparison |
| `Unfoldings.Cone.IntervalIsometry` | Boundary tangent fans isometric to their actual angular models |
| `Unfoldings.Cone.CyclicSeams` | Actual closing seams and identification of the outer radial banks |
| `Unfoldings.Cone.AngularCoordinates` | Closed headings, bank coordinates and full-plane coverage |
| `Unfoldings.Cone.AngularFibers` | All closed-bank fibers at one full turn |
| `Unfoldings.Cone.AngularInjective` | Boundary-inclusive development injectivity below a full turn |
| `Unfoldings.Cone.AngularSector` | Exact Euclidean sector metric when total angle is less than pi |
| `Unfoldings.Cone.SectorShortcut` | Strict chord shortcuts for nonzero points of pointed sectors |
| `Unfoldings.Cone.AngularShortcut` | Strict intrinsic shortcuts and apex avoidance in convex angular fans |
| `Unfoldings.Cone.AngularChord` | Exact intrinsic lengths of covered chords in reentrant fans |
| `Unfoldings.Cone.HeadingSector` | Convex rotated sectors with closed real heading bounds |
| `Unfoldings.Cone.HeadingEquality` | Real heading uniqueness across overlapping pointed intervals |
| `Unfoldings.Cone.HeadingLift` | Isometric lifts of selected heading sectors in arbitrary overlapping fans |
| `Unfoldings.Cone.HeadingShortcut` | Strict shortcuts on selected sheets, preserved by radial nonexpansion |
| `Unfoldings.Cone.AppendFirst` | A repeated first sector with exact continued real headings |
| `Unfoldings.Cone.AppendMap` | Nonexpanding cyclic maps continued across their closing bank |
| `Unfoldings.Cone.HeadingInterval` | Positive pointed intervals enclosing nearby headings, including equality |
| `Unfoldings.Cone.CellShortcut` | Strict shortcuts between specified cell representatives on the selected sheet |
| `Unfoldings.Cone.CyclicShortcut` | Shortcuts on either side of a cyclic fan, including across its slit |
| `Unfoldings.Cone.TangentShortcut` | Strict apex shortcuts for all actual positive-curvature tangent pairs |
| `Unfoldings.Cone.VertexAvoidance` | Original intrinsic geodesics avoid positive-curvature interior vertices |
| `Unfoldings.Cone.AngularHeadingShortcut` | Strict shortcuts across multiple angular pieces |
| `Unfoldings.Cone.LinkShortcut` | Strict angular shortcuts transferred to actual tangent metrics |
| `Unfoldings.Cone.CyclicDevelopment` | Constructed surjective planar map of full-turn actual fans |
| `Unfoldings.Cone.CyclicIsometry` | Full-turn cyclic tangent fans isometric to the Euclidean plane |
| `Unfoldings.Cone.FlatCharts` | Whole intrinsic Euclidean charts at actual flat interior vertices |
| `Unfoldings.Cone.FlatGeodesics` | Constructed shortest paths, straight coordinates and local ambient uniqueness |
| `Unfoldings.Cone.SmallDilation` | One positive scale places any two tangent points in an apex ball |
| `Unfoldings.Cone.SpatialEmbedding` | Proper tangent folding and closed spatial embeddings of actual uncut fans |
| `Unfoldings.Metric.Excision` | Whole-ball isometries when cutting distant seams |
| `Unfoldings.Complex.Excision` | Metric excision and preserved triangle-complex point classes |
| `Unfoldings.Complex.Star` | Actual vertex stars, conserved angles and local metric comparisons |
| `Unfoldings.Complex.EmbeddedStars` | Unique per-cell centers supplied by spatial foldings |
| `Unfoldings.Geometry.Corner` | Supporting wedges and actual corner wedge-ball geometry |
| `Unfoldings.Topology.PairedInvolutions` | Generic finite interval/cycle order from two involutions |
| `Unfoldings.Geometry.Endpoints` | Endpoint permutations induced by full-edge isometries |
| `Unfoldings.Complex.Germs` | The two corner edge germs and their retained seam crossings |
| `Unfoldings.Complex.GermEndpoints` | Actual far corners and complementary endpoint transport |
| `Unfoldings.Complex.Links` | Vertex-link involutions and boundary fixed germs |
| `Unfoldings.Complex.LinkConnectivity` | Germ components are exactly metric vertex classes |
| `Unfoldings.Complex.LinkOrdering` | Constructed link orders and their Euclidean angle sums |
| `Unfoldings.Complex.Vertices` | Actual cut vertex classes, boundary incidence and copy maps |
| `Unfoldings.Geometry.Angles` | Positive Euclidean corner angles and triangle angle sums |
| `Unfoldings.Complex.Angles` | Total angles and conservation across cut vertex copies |
| `Unfoldings.Complex.Folding` | Spatial rigid placements and embedded surface topology |
| `Unfoldings.Complex.Geodesics` | Straight face traces and closed interval face visits |
| `Unfoldings.Polyhedron.Convex` | Geometric convex-boundary adapter and derived geodesics |
| `Unfoldings.Polyhedron.Chords` | Exact boundary-chord distances and unique intrinsic geodesics |
| `Unfoldings.Geometry.BoundaryChord` | A chord through an interior boundary point stays on the convex frontier |
| `Unfoldings.Polyhedron.ExtremeVertices` | Positive-curvature vertices are actual spatial extreme points |
| `Unfoldings.Geometry.ExtremeSeparation` | Strict finite-hull supporting functionals with a uniform margin |
| `Unfoldings.Geometry.RadialSlice` | Actual compact convex level sections and radial generator projections |
| `Unfoldings.Polyhedron.VertexSlice` | Constructed nonempty transverse sections at spatial extreme vertices |
| `Unfoldings.Geometry.SliceInterior` | Transverse sections meet the ambient interior of the convex body |
| `Unfoldings.Polyhedron.VertexSliceInterior` | Actual vertex sections with a spatial interior center |
| `Unfoldings.Geometry.FunctionalPlane` | Constructed affine Euclidean coordinates on nonzero functional level planes |
| `Unfoldings.Polyhedron.VertexFigure` | Compact convex planar vertex figures, finite hulls, interior centers and circular boundaries |
| `Unfoldings.Geometry.AffineMaximum` | Local maxima force affine functionals to be constant |
| `Unfoldings.Polyhedron.FaceSupport` | Actual original face planes support the convex body |
| `Unfoldings.Polyhedron.FigureBoundary` | The figure boundary is exactly the sliced spatial surface |
| `Unfoldings.Polyhedron.FigureIncidence` | Every figure-intersecting original face has a corner at the chosen vertex |
| `Unfoldings.Polyhedron.FigureEdges` | Exact radial section segments of incident faces cover the figure boundary |
| `Unfoldings.Polyhedron.GermSpatial` | Spatial far endpoints preserved by actual seam crossings |
| `Unfoldings.Polyhedron.FigureGerms` | Constructed planar germ points and their boundary segments |
| `Unfoldings.Polyhedron.FigureGermAngles` | Actual apex angles and nondegenerate figure edges |
| `Unfoldings.Polyhedron.FigureChain` | Consecutive and closing endpoint agreement; exact boundary coverage |
| `Unfoldings.Polyhedron.GermEdges` | Actual edge incidence determines equal or seam-mate link germs |
| `Unfoldings.Polyhedron.FigureGermIncidence` | Figure endpoints agree exactly for equal germs or seam mates |
| `Unfoldings.Polyhedron.FigureSimpleChain` | Distinct initial endpoints in the actual cyclic figure chain |
| `Unfoldings.Geometry.EdgeChordInterior` | Chords between different edge interiors enter a triangle interior |
| `Unfoldings.Polyhedron.FaceIncidence` | Embedded original face interiors meet no other original face |
| `Unfoldings.Polyhedron.FigureEdgeInteriors` | Open sections lie in original face interiors and miss other sections |
| `Unfoldings.Geometry.PolygonEdges` | Open-edge separation allowing collinear subdivisions; at least three vertices |
| `Unfoldings.Polyhedron.FigurePolygon` | Actual simple Mathlib polygon, exact boundary and genuine strict angle budget |
| `Unfoldings.Geometry.FiniteAngles` | Every nonempty finite point list has a nonstraight chosen corner |
| `Unfoldings.Geometry.TransversePyramid` | Strict transverse pyramid budget without an extra corner assumption |
| `Unfoldings.Geometry.ConvexBoundaryEdges` | Supporting functionals of boundary segments and noncollinear interior centers |
| `Unfoldings.Geometry.ConvexBoundaryRays` | Unique convex-frontier point on a positive ray from an interior origin |
| `Unfoldings.Polyhedron.FigureCenter` | Genuine central triangles and their constructed positive-angle fan |
| `Unfoldings.Geometry.FrontierRays` | Gauge-normalized frontier rays and disjoint positive radial hulls |
| `Unfoldings.Polyhedron.FigureRadialCover` | Actual central cones cover the punctured plane and have separated open sectors |
| `Unfoldings.Geometry.PlanarCollinearity` | Signed-area zero is equivalent to affine collinearity |
| `Unfoldings.Geometry.BoundaryHalfplanes` | Every convex boundary edge supports its whole planar body |
| `Unfoldings.Geometry.AdjacentBoundaryEdges` | Simple convex boundary edges keep the same radial orientation |
| `Unfoldings.Geometry.AffineOrientation` | Affine signed-area scaling and rigid preservation of relative signs |
| `Unfoldings.Polyhedron.FigureOrientation` | Global consistency of the actual central triangle orientations |
| `Unfoldings.Polyhedron.FigureFrames` | Constructed normalized rigid frames of the actual central triangles |
| `Unfoldings.Geometry.ComplexArea` | Signed area in standard complex orthonormal coordinates |
| `Unfoldings.Polyhedron.FigureGlobalFrame` | Positive successive turns in one global normalized complex frame |
| `Unfoldings.Geometry.ComplexTurn` | Exact positive angular successor formula with unreduced headings |
| `Unfoldings.Polyhedron.FigureHeadings` | Actual cumulative headings and exact outer-ray closure |
| `Unfoldings.Polyhedron.FigureFullTurn` | Proved nonoverlap and exactly one turn of the actual central fan |
| `Unfoldings.Geometry.BoundaryCornerAngle` | Exact splitting of convex boundary corner angles by an interior center |
| `Unfoldings.Polyhedron.FigureAngleSum` | Actual polygon angle sum and strict angle bound at interior extreme vertices |
| `Unfoldings.Polyhedron.ExtremeCurvature` | Interior extremality iff positive curvature; extreme-vertex geodesic avoidance |
| `Unfoldings.Geometry.FrontierProjection` | Continuous gauge projection from an actual body interior point |
| `Unfoldings.Polyhedron.EdgeExposure` | Other convex-boundary points occur arbitrarily near every triangle edge |
| `Unfoldings.Polyhedron.Closedness` | Derived seam pairing of every original edge and cyclicity at every vertex |
| `Unfoldings.Polyhedron.ConvexCurvature` | Extremality iff positive curvature and avoidance, with no interior premise |
| `Unfoldings.Geometry.TriangleBoundary` | Every noninterior closed triangle point lies on an actual edge |
| `Unfoldings.Complex.RegularEdges` | Constructed edge charts from either seam bank |
| `Unfoldings.Polyhedron.RegularPoints` | Every actual nonvertex convex-boundary point is regular |
| `Unfoldings.Geometry.SpatialPlane` | A rigid spatial plane equals its containing nonzero functional level |
| `Unfoldings.Geometry.SupportingChord` | Support levels extend from an interior chord point to both endpoints |
| `Unfoldings.Polyhedron.NonextremeAxis` | All incident planes at a nonextreme vertex share a nonzero direction |
| `Unfoldings.Geometry.PlaneIntersection` | Distinct spatial planes intersect in their shared nonzero direction line |
| `Unfoldings.Polyhedron.GermDirections` | Actual radial directions, mate invariance and exact crease intersections |
| `Unfoldings.Polyhedron.NonextremeCreases` | Every genuine crease at a nonextreme vertex lies along one common axis |
| `Unfoldings.Geometry.EdgeParameters` | Strict edge interpolation avoids all original triangle vertices |
| `Unfoldings.Complex.GermSegments` | Local edge endpoints in the actual orientation of each germ |
| `Unfoldings.Polyhedron.GermRays` | Equal spatial unit directions classify equal germs and seam mates |
| `Unfoldings.Geometry.UnitLine` | A nonzero real line has two opposite unit directions |
| `Unfoldings.Polyhedron.LinkDirections` | Distinct initial radial directions in an embedded cyclic link |
| `Unfoldings.Polyhedron.NonextremeCreaseCount` | At most two genuine creases at a nonextreme vertex |
| `Unfoldings.Topology.CyclicLabels` | Nonconstant cyclic lists have no more labels than changes |
| `Unfoldings.Polyhedron.NonextremePlanes` | At most two actual incident face planes at a nonextreme vertex |
| `Unfoldings.Geometry.AffinePlaneRange` | Common-point affine planes agree when their linear directions agree |
| `Unfoldings.Polyhedron.VertexNeighborhood` | Small spatial vertex stars and two-plane neighborhoods |
| `Unfoldings.Geometry.LocalHingeBoundary` | A locally two-plane convex frontier equals the actual supporting hinge |
| `Unfoldings.Polyhedron.VertexHinge` | Constructed local support hinges at nonextreme vertices, allowing coincident planes |
| `Unfoldings.Metric.BallParametrization` | Whole-ball charts from isometric parametrizations with ball coverage |
| `Unfoldings.Polyhedron.PlanarPatch` | Whole intrinsic charts from actual planar spatial patches |
| `Unfoldings.Polyhedron.LocallyPlanar` | Derived regularity when a vertex's incident planes coincide |
| `Unfoldings.Geometry.RadialLocality` | Local equality of positive radial cones implies global equality |
| `Unfoldings.Geometry.FunctionalHomothety` | Positive homotheties preserve support levels and half-spaces |
| `Unfoldings.Cone.SpatialRange` | Exact radial homogeneity of the actual tangent image |
| `Unfoldings.Polyhedron.TangentHinge` | The whole actual tangent image equals the constructed spatial support hinge |
| `Unfoldings.Cone.SpatialConvexLift` | Isometric inverse tangent folding on every convex spatial subset |
| `Unfoldings.Cone.SpatialParametrization` | Finite piecewise rigid spatial parametrizations give intrinsic tangent isometries |
| `Unfoldings.Cone.ParametrizedChart` | Whole vertex charts from constructed planar tangent parametrizations |
| `Unfoldings.Geometry.EdgeLine` | Affine edge agreement extends to the entire supporting line |
| `Unfoldings.Geometry.SpatialHinge` | Injective piecewise rigid parametrizations of entire support hinges |
| `Unfoldings.Geometry.StrictHingeSupport` | Distinct support planes strictly separate their opposite corners |
| `Unfoldings.Cone.SpatialHinge` | Transfer entire spatial hinge parametrizations to intrinsic metric charts |
| `Unfoldings.Polyhedron.IncidentCrease` | Distinct incident planes force an actual crease in the cyclic link |
| `Unfoldings.Polyhedron.PrescribedHinge` | Construct support hinges with prescribed actual incident planes |
| `Unfoldings.Polyhedron.NonextremeRegular` | Euclidean ball charts at every nonextreme subdivision vertex |
| `Unfoldings.Polyhedron.GeodesicRegularity` | Every interior geodesic point is regular, giving unique continuation |
| `Unfoldings.Geometry.RadialSliceAngles` | Positive radial slicing preserves affine apex angles |
| `Unfoldings.Geometry.SliceHull` | The whole transverse section is the finite hull of projected generators |
| `Unfoldings.Geometry.RaySection` | Exact wedge sections and preservation of their genuine apex angles |
| `Unfoldings.Geometry.AngleSeparation` | Strict angular inequality through a direction outside a level plane |
| `Unfoldings.Geometry.PyramidAngles` | Lateral pyramid angle budgets, including strictness for transverse apices |
| `Unfoldings.Path.Straight` | Affine straightness of saturated geodesic images |
| `Unfoldings.Path.Restriction` | Codomain restriction preserving length and geodesics |
| `Unfoldings.Path.Subpath` | Affine constant-speed subpaths, including reversed intervals |
| `Unfoldings.Path.Chart` | Straight coordinates and uniqueness in isometric charts |
| `Unfoldings.Path.ConvexChart` | Geodesic construction in convex charts and ball confinement |
| `Unfoldings.Path.LocalShortcut` | Geodesic injectivity and avoidance of centers with local strict shortcuts |
| `Unfoldings.Path.Continuation` | Unique geodesic continuation from a common initial interval through charts |
| `Unfoldings.Metric.BallChart` | Whole metric-ball charts in a named model space |
| `Unfoldings.Complex.Regular` | Constructed regular points and unique intrinsic geodesic continuation |
| `Unfoldings.Complex.Connectivity` | Finite metrics and geodesics for connected face incidence |
| `Unfoldings.Complex.HingeCharts` | Constructed Euclidean metric balls at retained edge interiors |
| `Unfoldings.Complex.HingeCoordinates` | Local hinge frames and exact local distances |
| `Unfoldings.Complex.Hinge` | Intrinsic upper bounds from local unfolded hinge chords |
| `Unfoldings.Boundary` | Boundary-edge labels, bank maps, and restoration of banks |
| `Unfoldings.Boundary.Exact` | Metric separation of distinct cut-bank interiors |
| `Unfoldings.Boundary.Charts` | Constructed half-ball metric charts at boundary edge interiors |
| `Unfoldings.Development` | Facewise placements, nonoverlap, multiplicity, and metric descent |
| `Unfoldings.Development.Hinge` | Nonoverlapping developments of arbitrary two-triangle hinges |
| `Unfoldings.Path.Length` | Continuous-path length and its composition laws |
| `Unfoldings.Path.Reparameterization` | Bounded-speed replacements preserving the curve image |
| `Unfoldings.Path.Shortest` | Compact families, lower semicontinuity, and shortest paths |
| `Unfoldings.Path.FiniteComponent` | Length-preserving lifts to finite-distance components |
| `Unfoldings.Path.EMetricShortest` | Shortest paths in compact extended metric spaces |
| `Unfoldings.Path.Geodesic` | Metric geodesics and endpoint-saturating speed bounds |
| `Unfoldings.Path.Distance` | Intrinsic distance as an infimum of continuous-path lengths |
| `Unfoldings.Path.Segment` | Length and speed of Euclidean straight segments |
| `Unfoldings.Path.EMetricGeodesic` | Geodesic criterion in extended metric spaces |
| `Unfoldings.Geometry.Separation` | Corner certificates for whole-cell separation |
| `Unfoldings.Geometry.Hinge` | Opposite sides imply adjacent-cell nonoverlap |
| `Unfoldings.Source.Radial` | Injectivity from uniqueness of radial lifts |
| `Unfoldings.Path.MetricGeodesic` | Real distance formulas for actual constant-speed geodesics |
| `Unfoldings.Path.InitialChart` | A positive chart sample determines the whole initial interval |
| `Unfoldings.Source.Coordinates` | Constructed full-length source vectors and exact radial norms |
| `Unfoldings.Source.ShortestPath` | All actual shortest paths, retaining endpoint ties |
| `Unfoldings.Source.ConvexCoordinates` | Planar vectors distinguish all convex-boundary shortest paths |
| `Unfoldings.Source.CompactPaths` | Compactness of the complete shortest-path space by Arzela--Ascoli |
| `Unfoldings.Source.ContinuousCoordinates` | Continuous source vectors in the uniform path topology |
| `Unfoldings.Source.Domain` | Compact planar path images and continuous endpoint projection |
| `Unfoldings.Source.ConvexDomain` | Actual convex-boundary path-space homeomorphisms and surjective projection |
| `Unfoldings.Source.SampleLine` | Exact initial chart straightness of the full-length source vector |
| `Unfoldings.Source.CutLocus` | Closed source cut locus and exclusion of a whole source ball |
| `Unfoldings.Source.ConvexCutLocus` | Unique shortest paths off the closed source cut locus |
| `Unfoldings.Source.Prefixes` | Actual normalized shortest-path prefixes, including both endpoints |
| `Unfoldings.Source.RadialDomain` | Exact prefix-vector scaling and star-shaped planar source images |
| `Unfoldings.Path.Splice` | Actual constant-speed geodesics after alternative shortest-prefix replacement |
| `Unfoldings.Source.PrefixUniqueness` | Every proper prefix is unique, by continuation from the unchanged tail |
| `Unfoldings.Topology.FiniteIntervalCover` | Bounded subdivisions subordinate to finite closed interval covers |
| `Unfoldings.Path.Partition` | Exact additive distances along finite monotone geodesic partitions |
| `Unfoldings.Complex.FaceRoutes` | Bounded finite face partitions with affine pieces and exact chord lengths |
| `Unfoldings.Source.UniqueProjection` | A homeomorphism selecting the unique shortest path continuously off the cut locus |
| `Unfoldings.Source.OffCutCoordinates` | Continuous injective source coordinates on the cut-locus complement |
| `Unfoldings.Source.ConvexOffCutCoordinates` | Constructed coordinates from convex-boundary input and a regular source |
| `Unfoldings.Source.SourceBall` | The constructed coordinates are isometric on the whole source chart ball |
| `Unfoldings.Geometry.IsometryOnConvex` | Isometric maps to strictly convex spaces preserve affine segment parameters |
| `Unfoldings.Geometry.BallRigidity` | Actual isometric open-ball maps extend to whole affine isometries |
| `Unfoldings.Metric.OpenChart` | Recenter open isometric charts on whole ambient balls |
| `Unfoldings.Metric.RigidChartTransition` | Construct rigid affine transitions between actual overlapping metric charts |
| `Unfoldings.Metric.RegularLocus` | Metric regularity is open and open charts recenter to whole metric balls |
| `Unfoldings.Geometry.RealAffine` | Two distinct real samples determine an affine map |
| `Unfoldings.Path.AffineSamples` | Continue geodesic coordinate identities across a whole chart interval |
| `Unfoldings.Path.ChartPartition` | Finite strictly ordered chart partitions of actual regular paths |
| `Unfoldings.Source.PathNeighborhood` | Uniform stability in charts on whole compact time intervals |
| `Unfoldings.Source.ChartTrace` | Construct the next affine chart trace for every nearby shortest path |
| `Unfoldings.Source.InitialTrace` | Construct actual affine source traces on a whole path neighborhood |
| `Unfoldings.Source.TerminalTrace` | Finite continuation constructs a terminal affine chart from regularity |
| `Unfoldings.Source.EndpointChart` | An actual affine endpoint formula for all nearby shortest paths |
| `Unfoldings.Source.EndpointStability` | Singleton fibers control every shortest path to nearby endpoints |
| `Unfoldings.Source.RegularUnique` | Unique paths to regular endpoints avoid the closed source cut locus |
| `Unfoldings.Source.PrefixCutAvoidance` | Every proper shortest-path prefix avoids the closed cut locus |
| `Unfoldings.Source.LocalIsometry` | Actual local distance preservation from constructed terminal charts |
| `Unfoldings.Source.ConvexLocalIsometry` | Local source isometries at every regular retained convex-surface point |
| `Unfoldings.Source.RetainedRadials` | Construct all retained radial geodesics and prove exact developed straightness |
| `Unfoldings.Metric.RegularGeodesic` | A whole regular chart supplies a nonconstant geodesic through its center |
| `Unfoldings.Polyhedron.RegularClassification` | Regular points are exactly the complement of true extreme vertex points |
| `Unfoldings.Geometry.AffineEnd` | Finite-dimensional rigid self-embeddings are surjective and open |
| `Unfoldings.Geometry.RadialInterior` | Interior points extend slightly outward along their radial lines |
| `Unfoldings.Source.DomainInterior` | Regular unique endpoints give actual interior source vectors |
| `Unfoldings.Source.ConvexDomainInterior` | Exact characterization of source-domain interior by regular retained endpoints |
| `Unfoldings.Source.DomainDensity` | Every proper radial prefix is interior; its closure is the whole compact domain |
| `Unfoldings.Source.DomainBoundary` | Exact boundary projection onto the closed cut union singular points |
| `Unfoldings.Source.RegularRegion` | The flat retained region and explicit closed singular slit set |
| `Unfoldings.Source.InteriorHomeomorph` | The actual flat retained surface is homeomorphic to the planar domain interior |
| `Unfoldings.Source.RegularDevelopment` | Constructed nonoverlapping local isometries and radial geodesics on the retained interior |
| `Unfoldings.Metric.Polygonal` | Constructed intrinsic metrics from allowed straight steps and nonexpanding inclusions |
| `Unfoldings.Metric.PolygonalStar` | Radial contraction identifies intrinsic and ambient topology through the boundary |
| `Unfoldings.Metric.PolygonalCompletion` | Isometric dense interior inclusion and complete compact closed-domain model |
| `Unfoldings.Metric.PolygonalPaths` | Straight-step geodesics and equality of route and continuous-path distance |
| `Unfoldings.Metric.PolygonalLocal` | Isometric neighborhoods for the development and its inverse on open regions |
| `Unfoldings.Geometry.ConvexLocalBounds` | Convex subtype center bounds imply global nonexpansion |
| `Unfoldings.Metric.PolygonalMap` | Local center bounds descend to intrinsic polygonal metrics |
| `Unfoldings.Metric.LocalInverse` | Constructed isometric inverse neighborhoods |
| `Unfoldings.Metric.LocalComposition` | Compose local isometries and obtain local center bounds |
| `Unfoldings.Path.LocalDistance` | Local nonexpansion preserves intrinsic path-distance inequalities |
| `Unfoldings.Source.CutMetric` | Actual source cut metrics, completion, boundary copies and boundary projection |
| `Unfoldings.Source.CutIntrinsic` | Cut metric equals path distance in the original retained surface |
| `Unfoldings.Source.CutProjection` | The whole completed projection does not increase surface distance |
| `Unfoldings.Topology.CommonFibers` | Compact quotient maps with the same fibers identify their targets |
| `Unfoldings.Geometry.RadialBody` | Each ray meets the boundary once, and normalization gives a sphere homeomorphism |
| `Unfoldings.Geometry.RadialCone` | A nonconvex radial body is a closed ball, with exactly matching boundaries |
| `Unfoldings.Source.Disk` | Constructed disk and boundary-circle homeomorphisms for the actual source completion |
| `Unfoldings.Source.CompletedRadials` | Completed radial geodesics project to all original shortest paths, preserving source distance |
| `Unfoldings.Geometry.PlaneSphere` | The planar circle is connected, nontrivial and perfect |
| `Unfoldings.Topology.PerfectProjection` | A perfect boundary cannot project injectively to finite exceptions outside a closed set |
| `Unfoldings.Source.ConeLeaves` | All singular endpoints belong to the closure of actual ties; the slit set equals the cut locus |
| `Unfoldings.Source.ActualCut` | The actual cut complement, exact cut-locus boundary projection and constructed source-disk properties |
| `Unfoldings.Topology.FiberGraph` | Equivalence chains in finite fibers yield short simple graph paths |
| `Unfoldings.Complex.PointFiber` | Exact point fibers have at most one copy per original face and bounded seam paths |
| `Unfoldings.Complex.PointSeamRoute` | Actual bounded oriented seam routes, including at vertices |
| `Unfoldings.Complex.SeamFaceRoute` | Constructed entry/exit points and bounded seam resolutions of all face-route junctions |
| `Unfoldings.Complex.SeamWord` | Finite oriented words construct rigid hinge placements agreeing at actual crossing points |
| `Unfoldings.Geometry.ConvexRigidity` | Actual isometries on convex sets with interior extend rigidly through the boundary |
| `Unfoldings.Source.FacePlacement` | Constructed source-face motion agrees with all source vectors in the source ball |
| `Unfoldings.Source.LocalFacePlacement` | Constructed rigid face patches at all retained points, including edges and flat vertices |
| `Unfoldings.Geometry.ConvexPatchRigidity` | Overlapping convex face patches force equality of their whole rigid motions |
| `Unfoldings.Source.FaceAtlas` | Actual face motions are locally constant and develop every connected retained face region rigidly |
| `Unfoldings.Examples.*` | Recovery, disconnectedness, shortcuts, contact, and overlap |
| `Audit` | Transitive axiom check for all imported library declarations |

Embedded-graph and cellulation theory is planned separately under
`Unfoldings/Topology/`, with no dependency on unfolding geometry, for possible
upstreaming to Mathlib.

## Build and proof audit

The project pins Lean and Mathlib **4.35.0**. Install the toolchain through elan,
then fetch Mathlib artifacts before building:

```sh
lake exe cache get
lake build
```

`lake build` checks both the library (including its examples) and `Audit`. The
audit rejects any dependency other than `propext`, `Classical.choice`, and
`Quot.sound`; in particular, it rejects `sorryAx` and native-decision axioms.

On a machine with limited disk space, fetch only the needed import closures:

```sh
lake exe cache get Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.Analysis.Convex.Topology \
  Mathlib.Analysis.Normed.Affine.AddTorsorBases \
  Mathlib.Analysis.Normed.Affine.Isometry \
  Mathlib.Analysis.Normed.Operator.Banach \
  Mathlib.Analysis.Convex.StrictConvexBetween Mathlib.Analysis.InnerProductSpace.Convex \
  Mathlib.Analysis.InnerProductSpace.Projection.Reflection \
  Mathlib.Topology.EMetricSpace.Lipschitz \
  Mathlib.Logic.Relation Mathlib.Topology.Separation.Hausdorff \
  Mathlib.Topology.UniformSpace.Cauchy \
  Mathlib.Topology.MetricSpace.HausdorffDistance Mathlib.Topology.MetricSpace.Lipschitz \
  Mathlib.Topology.EMetricSpace.BoundedVariation \
  Mathlib.Analysis.ConstantSpeed Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli \
  Mathlib.Topology.MetricSpace.Equicontinuity Mathlib.Topology.Semicontinuity.Basic \
  Mathlib.Topology.IsLocalHomeomorph \
  Mathlib.Topology.Instances.Real.Lemmas \
  Mathlib.Tactic.FinCases Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination
lake build
```

To skip Mathlib's automatic full-cache hook when updating dependencies, use
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`, followed by the selected cache fetch.

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
