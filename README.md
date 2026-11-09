# Unfoldings

A Lean library for polyhedral metrics, cuts, and planar developments, with source
unfolding of convex polyhedra as its first major target. Overlapping developments
are supported; nonoverlap is a separate property and permits boundary contacts.

The design and feature checklist are in [PLAN.md](PLAN.md). The source-unfolding
construction and the sphere/disk cut-graph characterizations remain future work.
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
- `SpatialFolding` gives compatible rigid placements into three-dimensional
  space. Every original face is isometric for every cut metric. Spatial
  injectivity is separate and gives a homeomorphism onto the triangle union.
  `SpatialFolding.ConvexBoundary` requires that this union be the frontier of
  its actual finite corner hull, with nonempty spatial interior. Sphere topology,
  connectedness, finite intrinsic distance and geodesics are derived. Flat
  subdivision corners are allowed; a separate maximal-facet API remains open.
- Shortest paths on embedded surfaces cannot leave and re-enter a closed original
  face: each face visit is one closed parameter interval. Saturated nonexpanding
  images of geodesics are proved to be affine straight paths.
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
Vertex charts, self-paired-edge charts, and the full manifold conditions remain open.

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
| `Unfoldings.Cone.AngularHeadingShortcut` | Strict shortcuts across multiple angular pieces |
| `Unfoldings.Cone.LinkShortcut` | Strict angular shortcuts transferred to actual tangent metrics |
| `Unfoldings.Cone.CyclicDevelopment` | Constructed surjective planar map of full-turn actual fans |
| `Unfoldings.Cone.CyclicIsometry` | Full-turn cyclic tangent fans isometric to the Euclidean plane |
| `Unfoldings.Cone.FlatCharts` | Whole intrinsic Euclidean charts at actual flat interior vertices |
| `Unfoldings.Cone.FlatGeodesics` | Constructed shortest paths, straight coordinates and local ambient uniqueness |
| `Unfoldings.Metric.Excision` | Whole-ball isometries when cutting distant seams |
| `Unfoldings.Complex.Excision` | Metric excision and preserved triangle-complex point classes |
| `Unfoldings.Complex.Star` | Actual vertex stars, conserved angles and local metric comparisons |
| `Unfoldings.Complex.EmbeddedStars` | Unique per-cell centers supplied by spatial foldings |
| `Unfoldings.Geometry.Corner` | Supporting wedges and actual corner wedge-ball geometry |
| `Unfoldings.Topology.PairedInvolutions` | Generic finite interval/cycle order from two involutions |
| `Unfoldings.Geometry.Endpoints` | Endpoint permutations induced by full-edge isometries |
| `Unfoldings.Complex.Germs` | The two corner edge germs and their retained seam crossings |
| `Unfoldings.Complex.Links` | Vertex-link involutions and boundary fixed germs |
| `Unfoldings.Complex.LinkConnectivity` | Germ components are exactly metric vertex classes |
| `Unfoldings.Complex.LinkOrdering` | Constructed link orders and their Euclidean angle sums |
| `Unfoldings.Complex.Vertices` | Actual cut vertex classes, boundary incidence and copy maps |
| `Unfoldings.Geometry.Angles` | Positive Euclidean corner angles and triangle angle sums |
| `Unfoldings.Complex.Angles` | Total angles and conservation across cut vertex copies |
| `Unfoldings.Complex.Folding` | Spatial rigid placements and embedded surface topology |
| `Unfoldings.Complex.Geodesics` | Straight face traces and closed interval face visits |
| `Unfoldings.Polyhedron.Convex` | Geometric convex-boundary adapter and derived geodesics |
| `Unfoldings.Path.Straight` | Affine straightness of saturated geodesic images |
| `Unfoldings.Path.Restriction` | Codomain restriction preserving length and geodesics |
| `Unfoldings.Path.Subpath` | Affine constant-speed subpaths, including reversed intervals |
| `Unfoldings.Path.Chart` | Straight coordinates and uniqueness in isometric charts |
| `Unfoldings.Path.ConvexChart` | Geodesic construction in convex charts and ball confinement |
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
