# O'Rourke's nearly flat cap theorem

Target: Joseph O'Rourke, *Edge-Unfolding Nearly Flat Convex Caps*,
[2021 extended version](https://arxiv.org/abs/1707.01006v4), Theorem 1.
This is a proof-development checklist; unchecked claims are not Lean declarations.
**Original-edge face-interior nonoverlap is proved. The paper's stronger
simple-polygon boundary conclusion remains open.**

Current entry points:

- [EdgeUnfolding](../Unfoldings/Cap/EdgeUnfolding.lean),
  `exists_uniform_nonoverlapping_edge_unfolding`, chooses a positive tilt threshold
  depending only on the acute margin, before the face type and entire mesh.
  It constructs cuts using original seams, a boundary-rooted cut forest, an
  intrinsic closed cut disk, and a development with disjoint face interiors
  and local isometry throughout the open disk. Flat caps and caps without
  interior vertices are included. It does not assert boundary injectivity,
  the paper's numerical threshold, or its quadratic running-time bound.
  Its construction now removes every zero-curvature descendant subtree.
- [UniformOriginalNonoverlap](../Unfoldings/Cap/UniformOriginalNonoverlap.lean)
  proves nonoverlap for every development of a qualifying original sector
  forest. The constructed auxiliary roof is deep enough to cover the entire
  original footprint inside the proved separation ball.

- [UniformExtendedFaceSeparation](../Unfoldings/Cap/UniformExtendedFaceSeparation.lean)
  chooses a positive tilt threshold before both meshes and separates actual
  roof-face interiors in a controlled source ball. All circle geometry and
  finite exceptional-radius avoidance are discharged. The actual original-face
  subdivision and both directions of retained-seam transfer are proved below.

- [AllSectorCircleSeparation](../Unfoldings/Cap/AllSectorCircleSeparation.lean)
  proves pairwise separation of every actual strip-circle image across all
  five sectors from the constructed waterfall geometry. The proof derives
  extreme survivors, removed boundary runs, maximal terminals, bank candidates,
  and comparison margins. Uniform instantiation is proved below; original-face
  transfer is proved below.

- [OuterCircleCaps](../Unfoldings/Cap/OuterCircleCaps.lean) and
  [BoundaryRunCircleCaps](../Unfoldings/Cap/BoundaryRunCircleCaps.lean) separate
  actual adjacent outer-bank circle portions, with or without a disappearing
  boundary run. Shared physical rays may contain cuts. The finite assembly
  for arbitrary surviving pairs is proved by the all-sector theorem.
- [WaterfallCircleSurvivorOrder](../Unfoldings/Cap/WaterfallCircleSurvivorOrder.lean)
  retains all actual surviving bank endpoint order, and
  [WaterfallCircleNonempty](../Unfoldings/Cap/WaterfallCircleNonempty.lean)
  proves every controlled sector circle has a survivor.

- [SectorBoundaryCircleBankOrder](../Unfoldings/Cap/SectorBoundaryCircleBankOrder.lean)
  derives cross-frame order for circle endpoints on actual radial boundary
  cuts. Boundary classification and the comparison quadrants are proved from
  the cap geometry; global cyclic interval assembly is proved below.
- [ExtendedSectorCircleGeometry](../Unfoldings/Cap/ExtendedSectorCircleGeometry.lean)
  chooses a uniform positive tilt threshold before both meshes and separates
  all actual waterfall strip-circle images within each sector. Separation
  across all sectors is available in the all-sector theorem under its geometric inputs.
- [SubdivisionNonemptyCells](../Unfoldings/Geometry/SubdivisionNonemptyCells.lean)
  removes wholly empty physical cells while preserving exact bank contact on
  the controlled closed slab.
- [EmptyStripRunContactSeparation](../Unfoldings/Cap/EmptyStripRunContactSeparation.lean)
  proves actual endpoint order and disjointness across arbitrary disappearing
  runs using only those local contacts.
- [ContactSeparatorCircleOrder](../Unfoldings/Cap/ContactSeparatorCircleOrder.lean)
  proves actual endpoint order when no physically nonempty intermediate strip
  remains. The full survivor list is assembled below.
- [ForestExistence](../Unfoldings/Cap/ForestExistence.lean) constructs an actual
  original-edge rooted forest for uniformly small positive tilt.
- [ForestDevelopment](../Unfoldings/Cap/ForestDevelopment.lean) constructs its
  intrinsic cut disk and a locally isometric development, allowing overlap.
- [ExtendedPathWedges](../Unfoldings/Cap/ExtendedPathWedges.lean) derives acute
  fine-seam paths and mesh-independent crossing bounds on the constructed roof
  extension. Flat auxiliary branches need no acuteness assumption.
- [ExtendedDirectionControl](../Unfoldings/Cap/ExtendedDirectionControl.lean)
  bounds all actual developed roof-face directions in one projection-calibrated
  frame, using a tilt threshold chosen before the original and auxiliary meshes.
- [ExtendedBankChainSeparation](../Unfoldings/Cap/ExtendedBankChainSeparation.lean)
  compares entire opposite banks along every actual outward cut path, including
  sibling displacements at branches. Regular interior contact is on the same
  edge and physical parameter, with zero whole-subtree curvature. This does not
  yet compare different cut paths or developed strips globally.
- [ExtendedWaterfallInjective](../Unfoldings/Cap/ExtendedWaterfallInjective.lean)
  constructs finite waterfall subdivisions of the actual deep roof. Their strict
  interiors avoid every cut, and the actual developed map is injective on every
  positive-width height slab. Chart selection and continuity are proved.
  Global face-interior separation across the five sectors is proved below.
- [GnomonicArea](../Unfoldings/Cap/GnomonicArea.lean) proves a mesh-independent
  positive tilt threshold for arbitrarily small total spherical normal-image
  area, bounded by the actual planar normal-polygon areas.
- [NormalCone](../Unfoldings/Cap/NormalCone.lean) identifies these spherical
  polygons with all upward supporting unit normals at interior cap vertices.

- [AngularCurvature](../Unfoldings/Cap/AngularCurvature.lean) proves the actual
  intrinsic angular-defect/solid-angle identity, including flat vertices.
- [UniformCurvature](../Unfoldings/Cap/UniformCurvature.lean) gives a positive
  total-curvature threshold quantified before the entire input mesh.

The intended statement takes the cap's acute input triangulation as given.
For every fixed positive acuteness margin, there is a positive normal-tilt
threshold, uniform in the number of vertices, below which an original-edge
nonoverlapping unfolding exists. The rim is planar and its projection convex.
We first prove a rigorous positive threshold; the approximate numerical
constant in the paper is not a substitute for an exact inequality.

## Inputs and outputs

- Use actual closed triangles, full-edge seam isometries, and `SpatialFolding`.
- Specify the cap by upward unit supporting normals, a convex projected domain,
  vertical projection injectivity, and a horizontal rim. Supporting inequalities
  apply to the entire surface and must imply the required convex roof geometry.
- Acuteness is measured in the spatial triangles of the given cap mesh.
- Cuts use only original input seams. Construction of a separate acute
  triangulation is outside this theorem.
- Cut forests must have one boundary root per component and include every
  nonflat interior vertex. An auxiliary construction may also span flat vertices.
- A development and disk topology do not imply nonoverlap. Prove actual disjoint
  face interiors. Keep proper boundary crossing, boundary contact, and a simple
  polygon boundary distinct; zero-curvature cuts can produce redundant slits.
- Do not assume radial monotonicity, safe cuts, a forest, or nonoverlap as part
  of the cap input. Conditional lemmas may take a specified forest and explicit
  geometric hypotheses, then the final theorem must construct them.

## Existing infrastructure to reuse

- Intrinsic triangle route metrics and exact finite seam equivalence classes.
- Rooted-forest iff cut disk for an actual disk, including empty cuts.
- Flat-disk developing maps, strict opening, and normalization uniqueness.
- Supporting heights, planar orientation, rotations, and finite convex covers.
- Convex-boundary local geometry, angle links, and source developments.

The source-unfolding theorem does not make an arbitrary edge forest safe.
The remaining nonoverlap argument must be proved independently.

## Proof milestones

### Cap inputs and calibration

- [x] Geometric cap inputs without cuts or nonoverlap assumptions.
- [x] Derive actual disk topology from the convex injective projection.
- [x] Identify the projected footprint frontier with intrinsic boundary banks
  and original boundary vertex classes, including every boundary copy.
- [x] Derive the actual concave roof from supporting inequalities.
- [x] Prove uniform intrinsic projection bounds, with inverse constant `1/c`
  for minimum normal height `c`, independent of the number of triangles.
- [x] Prove the flat case: an injective nonoverlapping development with no cuts.

### Polygonal chains

- [x] Define finite polygonal chains and positions throughout their edges.
- [x] Prove whole-segment radial monotonicity iff an outward scalar product.
- [x] Show a common wedge of width at most pi/2 gives pairwise nonnegative
  edge scalar products, hence radial monotonicity from every earlier vertex.
- [x] Extend to earlier points inside edges, strict radial distance for genuine
  edges, and uniqueness of intersections with concentric circles.
- [x] Give examples distinguishing endpoint distances from whole-edge behavior.

### Two-bank developments and trees (Sections 7--8, Appendix A.4)

- [x] Construct actual paired chains from edge lengths and cumulative
  nonnegative opening angles; bound every prefix by the total budget.
- [x] Prove equal-horizontal-coordinate and equal-radius bank order when both
  unwrapped heading families lie in a common open quadrant. Finite endpoints
  require no extension in this conditional comparison.

- [x] Derive actual developed interval-link headings from original corner
  angles and opposite-side hinge separation. No global nonoverlap is needed.
- [x] At every childless internal forest vertex, prove that its one selected
  cut seam opens one original cyclic-link pair and preserves the complete
  corner angle. The actual equal-length terminal bank vectors differ by a
  rigid rotation of the vertex curvature, with exact aperture for curvature
  at most pi and contact allowed at zero.
- [x] Construct one covering actual boundary contour and one consistent developed
  orientation frame, even when the planar boundary crosses itself.
- [x] For every nonroot descendant subtree, derive the two actual parent-seam
  bank exits and exact aggregate boundary-turn sum from cut-copy incidence.
- [x] Prove that the actual equal-length parent banks rotate in that shared
  frame by the sum of all descendant curvatures. This sum lies between zero
  and total cap curvature; when it is at most pi it is the genuine aperture.
  Zero curvature allows contact. See [SubtreeOpening](../Unfoldings/Cap/SubtreeOpening.lean).
- [ ] Represent matched edge lengths and signed opening angles by actual rigid
  planar motions, retaining unwrapped real heading information.
- [ ] Define the left-of relation at equal radii without conflating touching
  with crossing or taking circular order to be a linear order globally.
- [ ] Prove Theorem 9 under all its hypotheses: radial monotonicity of both
  banks, nonnegative openings with total below pi, and cone measures below pi.
- [ ] Check the backward-induction argument against the 2021 clarification,
  including finite endpoints and every intermediate suffix.
- [ ] Prove branching-bank noncrossing, including the altered opposite bank
  (Corollary 10). The actual whole-subtree rotation, strict quadrant headings,
  and individual paired-seam separation are checked. Comparing different
  original edges and complete branching banks remains open.

A stronger special-case route is also checked: matched banks whose unreduced
headings are ordered in a common open quadrant are ordered at every equal
horizontal coordinate and at equal radii from their common start. This follows from scalar coordinate increments and
includes whole edges. It may replace the full Theorem 9 for a conservatively
smaller acute-cap threshold, provided the geometric heading, branching, and
global strip hypotheses are constructed. It is not a proof of Theorem 9.

### Planar forest construction (Section 5)

- [x] Construct the actual projected triangles, prove their nondegeneracy,
  disjoint interiors, seam agreement, and exact footprint coverage.
- [x] Obtain an empty forward halfplane, hence an empty positive cone gap,
  at a maximizer of a linear functional on a nonempty finite vertex set.
- [x] Choose a positive shear uniformly from an acute margin. Pulling back a
  quadrant gives a direction wedge of width strictly less than pi/2.
- [x] Prove local outgoing-edge existence in an acute triangle and finite
  mesh, then apply it to the actual projected cap vertex classes. The same
  argument gives outgoing original edges in a sheared acute wedge.
- [x] Prove that local outgoing-edge choices preserving a sector label and
  increasing its potential construct an actual original-edge rooted forest.
  Edge names are retained and distinct choices cannot select the same edge.
- [x] Choose the source at an internal horizontal extremum. Three acute
  near-quadrants cover the backward halfplane, have disjoint interiors, and
  assign every interior vertex a sector label. Actual outgoing original-seam
  choices preserve these labels, including positions on sector banks.
- [x] Construct this source-centered forest, its original-edge radially monotone
  paths and boundary roots, an empty forward gap, the actual cut disk, and a
  locally isometric development. Choose tilt and sector parameters before the
  entire mesh, and combine them with any requested total-curvature budget.
- [x] Construct a boundary-rooted original-edge forest whose paths all lie in
  one fixed acute wedge. Choose tilt and shear parameters before the cap.
  Stop each path at its first rim vertex; prove actual seam incidence,
  angle-monotonicity, and whole-edge radial monotonicity.
- [x] Transport selected edge names to the canonical relative cut graph. Prove
  that it is rooted, construct the intrinsic cut disk, and prove every cut
  vertex copy is a boundary vertex.
- [x] Handle the cap with no interior vertices: all face heights vanish,
  normals are vertical, and uncut projection is an injective nonoverlapping
  development, without any angle restriction.

### Uniform geometric estimates (Sections 4 and 6)

- [x] Bound orthogonal projection angle distortion using the maximum normal tilt.
  The checked existential threshold is uniform over all unit tangent directions.
  It uses compact-annulus angle continuity rather than the paper’s explicit formula.
- [x] Define actual planar normal polygons from incident supporting slopes.
  Prove they support the concave roof, have disjoint interiors, and lie in
  the disk of radius `sqrt(1-c²)/c` for minimum normal height `c > 0`.
- [x] Bound the sum of their actual Lebesgue areas by that disk's area.
  Derive a positive tilt threshold for any requested positive area budget,
  independent of vertex count. Inverse gnomonic coordinates recover the
  actual unit upward face normals.
- [x] Prove inverse gnomonic projection is nonexpansive for chord distance.
  Normalized Euclidean Hausdorff measure gives actual spherical surface area
  at most planar normal-polygon area, including degenerate polygons.
- [x] Identify each interior vertex's spherical polygon with the complete set
  of upward unit normals supporting the actual cap at that vertex. This uses
  separation and local face incidence, without assuming strict curvature.
- [x] Define solid angle by Mathlib's angular measure induced from spatial
  volume. Prove its conical-volume formula, full-sphere measure `4π`, orthogonal
  invariance, and nullity of great circles.
- [x] Prove the azimuth law by Haar uniqueness and the exact spherical lune
  formula `2 * aperture`, including degenerate endpoint apertures.
- [x] Bound each solid normal angle by `81` times its planar slope-polygon area
  when slopes lie in the unit disk. Derive an arbitrarily small total solid-angle
  budget from a positive tilt threshold uniform in vertex count.
- [x] Identify intrinsic angular curvature with the solid angle of its normal
  cone. Actual supporting planes and disjoint projected faces give zero or two
  link crossings; exact hemisphere lune measures give the crossing integral.
  This includes repeated normals, coplanar faces, and zero curvature.
- [x] Derive nonnegative intrinsic curvature and an arbitrarily small total
  curvature budget from a positive tilt threshold quantified before the face
  type, triangle complex, and cap. The bound is independent of mesh size.
- [x] Prove relative angle-defect balance by summing original and projected
  face angles over the actual corner classes.
- [x] Derive projected interior-link flatness from the actual cyclic germ order,
  disjoint original-face direction cones, and the one-full-turn theorem.
  Consequently the actual cap curvature/boundary-angle balance needs no
  assumed projected flatness or Euler identity.
- [x] Prove that each original rim vertex has intrinsic angle at least its
  projected angle, including straight boundary subdivisions. The sum of these
  nonnegative rim excesses is total curvature, so every rim portion is bounded
  by the same mesh-independent budget.
- [x] Prove relative angle balance for every actual union of original faces.
  The aggregate excess on partially included corner stars is bounded by total
  curvature, without a disk-region or Euler-count input.
- [x] Bound actual spatial turning along every finite vertical roof-section
  partition by twice the tilt. Concavity makes secant inclinations telescope;
  this bound is uniform before the complete mesh is supplied.
- [x] Prove signed horizontal-ray crossing counts of magnitude at most one for
  the actual constructed sector root paths, with a half-open endpoint convention.
  Regrouping nested subtree curvatures bounds the weighted signed correction
  by total curvature, independently of mesh size and tree depth.
- [x] Extend the signed crossing budget to arbitrary ray origins and directions.
  Any acute wedge supplies one monotone ambient coordinate in every frame.
- [x] Construct one nonvertex original rim anchor, with a unique original face.
  Every original face has an interior target whose complete section line avoids
  all original vertices. Construct a finite original-face trace with the actual
  anchor and target face labels and actual original-seam transitions.
- [x] Identify the trace's actual face tangent vectors and bound their total
  spatial turning by twice the tilt. Local projection error applies to their
  genuine rigidly developed vectors.
- [x] Derive opposite-side opening for the actual cap projection and a common
  projected-to-developed orientation across every connected retained mesh.
- [x] Derive actual transverse seams for every regular original-face transition.
  Across retained seams, actual developed section turns are at most spatial turns.
- [x] Orient the actual complete boundary contour by cap projection. Its common
  developed frame preserves that projection orientation on every original face.
- [x] Identify actual parent-child endpoint order at subtree entrances and exits.
  In the common frame, actual outward parent vectors differ by the positive
  whole-subtree curvature rotation. Removing that actual phase bounds the
  transverse section turn by the genuine spatial bend, including flat cuts.
- [x] Determine each actual parent-bank phase sign from its geometric transverse
  section determinant. Actual original-face containment gives the sign; retained
  seams have zero phase and each cut seam has its unique selected parent.
- [x] Construct actual seam phases and real unreduced developed headings along
  every regular section trace. The real heading difference minus the signed
  phase sum has absolute value at most twice the tilt.
- [x] Construct interior sample points in every regular face piece; the whole
  open piece lies in that original face interior and avoids every original seam.
- [x] Define the actual weighted ray-crossing curvature potential. Its value is
  bounded by total curvature and telescoped query changes by twice that budget.
- [x] Identify every actual trace phase with its actual weighted ray-potential
  change. All other parent counters stay constant between adjacent samples;
  the whole signed phase sum telescopes and is bounded by twice total curvature.
- [x] Prove a real developed heading bound of `2 * tilt + 2 * totalCurvature`
  for every actual regular section, independently of mesh size. Every original
  face has such an aligned section direction from the same original rim face.
- [x] Choose one positive threshold, before the whole mesh, constructing the
  acute-sector forest and making this actual section-heading budget arbitrarily small.
- [x] Transfer the actual one-direction section alignment to every direction
  on every original face, using consistent orientation and two local angle errors.
- [x] Calibrate one global developed frame to original projection. Actual face
  directions differ by at most `2 * tilt + 2 * totalCurvature + 3 * localError`.
  A positive threshold before the entire mesh makes this uniformly arbitrarily small.
- [x] Apply the calibrated bound to all actual sector directions and reserve
  strict common-quadrant margins under a threshold chosen before the whole mesh.
- [x] Preserve actual signed subtree rotations in these quadrant frames.
- [x] Sum actual contour displacements: a parent-copy gap is precisely the sum
  of all descendant paired-vector differences, including every attached branch.
- [x] Order all matched actual bank points, including both endpoints and the
  straight extensions beyond the parent rim. Positive descendant curvature
  separates the interiors of each seam's two banks; contacts have zero subtree
  curvature and matched parameters.
- [x] Prove immediate-child subtree gap balance and the distinguished internal
  origin's leaf property. Its actual two child-bank endpoints coincide.
- [ ] Compare different original seams and complete branching banks globally.

The section-and-crossing-potential route proves the actual whole-section heading
bound directly. The alternative paper-style prefix-region closures, truncations,
and artificial connecting segments remain unformalized and are not used in this
checked route. Global bank and strip separation still need proofs.

The checked numerical estimate, for `3/4 ≤ c` and all normal heights at least
`c`, is

```text
totalInteriorAngularDefect ≤ 81 * (sqrt (1 - c²) / c)² * pi.
```

The constant is conservative. Continuity at tilt zero gives an arbitrarily
small total-curvature budget uniformly across all meshes. The proof uses
volume-induced solid angle; it does not need an equality with normalized
Hausdorff area. Strict actual sector margins and individual paired-seam separation are checked.
Complete auxiliary-bank comparison and global face-interior nonoverlap are proved below.

### Global assembly (Sections 9--10, Appendices A.5--A.6)

- [x] Construct the actual unbounded supporting-plane envelope. Its closed convex
  active cells cover the plane; the complete roof is homeomorphic to the plane
  and is precisely the frontier of the original supporting-halfspace solid.
- [x] Extend each original rim root radially from the internal sector origin.
  Distinct root tails are disjoint, remain outside the original footprint, and
  lift continuously to the actual roof. Their directions retain the tree sector.
- [x] Construct finite whole-piece active-support traces for all roof segments.
  Each ray eventually stays on one original supporting plane and is exactly straight.
- [x] Derive the flat-or-positive-height dichotomy from geometric cap input.
  Nonflat roofs have precisely the original footprint as their zero superlevel.
- [x] Prove that every interior point has positive roof height in the nonflat
  case, so the actual internal forest origin can be used for radial continuations.
- [x] Construct every finite lower horizontal clip as a compact convex footprint
  with a disk homeomorphism. Its actual roof is a compact spatial disk containing
  the supplied cap; its rim is an exact finite union of support-plane segments.
- [x] Construct compact active-support polygons with exact finite segment rims.
  Remove duplicate support planes; the remaining polygon interiors are disjoint.
- [x] Construct genuine finite triangle partitions from polygon boundary segments,
  after subdividing overlaps. Assemble an exact triangle partition of the entire
  clip and lift each whole triangle by its actual support-face isometry. All
  original normals and the tilt bound are retained.
- [x] Make the resulting triangle partition conforming across support polygons.
  Subdivide all old boundaries together and construct center fans using global
  base labels. Two refined triangles meet in an empty set, a common vertex, or
  a whole shared edge. Pair matching edges using actual spatial isometries;
  the resulting physical triangle complex folds onto exactly the clipped roof.
- [x] Prove the paired metric realization is the actual roof disk.
  Shared-edge compatibility propagates around every vertex via punctured convex
  neighborhoods. The resulting spatial folding is embedded; its intrinsic
  realization is homeomorphic to the clip and the closed disk. Its finite route
  metric has projection bounds depending only on original normal height.
- [x] Identify its actual boundary banks with the horizontal clip rim. Translate
  the rim to zero to construct a full geometric `ConvexCap`, retaining the original
  support normals and tilt. A single numerical threshold bounds total intrinsic
  curvature of every clip and refinement, including all newly introduced vertices.
- [x] Preserve original cut geometry in the extension triangulation. Insert all
  original face supporting lines in one finite arrangement; triangulate its
  chambers and make the result conforming. Every original projected and spatial
  edge is exactly a finite union of whole actual extended-triangle edges.
- [x] Derive face-to-face conformity of the supplied cap's projected input
  triangles directly from injective projection and actual full-edge seam classes.
- [x] Mesh arbitrary prescribed finite genuine segments into the actual roof,
  including both endpoints, while preserving every original cap edge.
- [x] Continue arbitrary finite skirt seeds radially to the outer rim, staying
  outside the original footprint's interior. Merge nested tails into disjoint
  whole segment components and mesh their actual spatial lifts exactly.
- [x] Prove that arbitrary line meshing creates no curvature away from the
  preceding conforming support partition's corners. At a regular old point there
  are at most two old faces; the actual new support slopes are collinear, so
  their intrinsic curvature is zero. Positive curvature stays at old corners.
- [x] Prove that actual clip curvature inside the supplied cap is supported only
  on original cap vertices. At a regular original face point, all original
  support planes active there have collinear slopes, even after extension.
- [x] Select finite skirt seeds from preceding roof corners and original rim
  corners before meshing. Prove that the selected original forest edges and
  the constructed skirt components cover every actual positive-curvature vertex.
- [x] Construct the actual extended retained-seam set by removing whole fine
  edges in the geometric cuts. Every positive-curvature vertex is an endpoint
  of an actual removed seam. All surviving interior vertex copies have full
  angle two pi, while flat auxiliary vertices may remain uncut.
- [x] Prove the general development theorem for a disk whose cuts meet every
  positive-curvature vertex; flat subdivision vertices need no cuts.
- [x] Select a boundary-rooted primal subforest of the actual extended cut seams
  using strictly increasing source distance. Every positive-curvature vertex
  selects an outgoing edge. Unused flat vertices remain uncut. Construct its
  actual cut-disk homeomorphism and locally isometric development.
- [x] Prove direction control for the constructed extended forest paths,
  including independent radial skirt components. Transfer to developed strips
  will follow the construction of their actual boundaries.
- [x] Strengthen the fine-seam selection to whole-edge radial progress. Every
  constructed root path meets each source-centered circle in at most one point.
- [x] Append an entire radial continuation to each original root path without
  increasing its acute wedge width; the extended paths remain radially monotone
  with respect to every earlier path point.
- [x] Complete unused flat vertices using arbitrary actual outward seams, without
  requiring an acute auxiliary triangulation. Preserve all previous cut edges
  and nonroot parents. All added branches outside the prescribed cuts have zero
  descendant curvature and zero bank aperture; the prior development is unchanged.
- [x] Apply the exact subtree bank rotations to completed forests in one common
  projection-preserving frame. Generalize signed crossing budgets so only paths
  starting at positive-curvature vertices need an acute wedge.
- [x] Label complete original-cut and radial components consistently at every
  geometric contact. Show that each component has one acute wedge, and that
  every curvature-carrying completed fine-seam path inherits it. Derive the
  actual uniform crossing-potential bound without any path-wedge certificate.
- [x] Derive actual developed heading bounds for the completed extension from
  geometric signed phases. Actual seam transitions are exact counter changes;
  their signed sum telescopes to the proved crossing potential.
- [x] Calibrate every actual developed roof-face direction in one common frame.
  A positive tilt threshold precedes the entire original mesh, source forest,
  clipping height, and refinement. Derive all path and normal-height conditions;
  no auxiliary acute-triangulation or safe-path certificate is assumed.
- [x] Prove the finite segment-cover direction lemma: an outward fine edge is a
  positive multiple of a genuine covering piece's direction. A common wedge is
  preserved by meshing, without imposing acuteness on auxiliary triangles.
- [x] Preserve the actual original source vertex in the meshed roof. Source
  distance proves that it remains a leaf after flat-vertex completion. Its two
  source-bank ends are the same intrinsic cut vertex and developed point.
- [x] Cover all extended-roof directions by five acute sectors, adding two in
  the old forward gap. Construct one positive shared tolerance and five actual
  calibrated quadrant frames before either cap mesh. Bank rotations preserve
  their signs in every frame.
- [x] Extend positional bank-gap order to entire curvature-carrying completed
  subtrees, allowing arbitrary zero-curvature completion branches. Prove that
  every flat subtree has coincident bank positions, not merely parallel vectors.
- [x] Prove injectivity within a coherent monotone strip from actual affine face
  placements and one mesh-independent tilt threshold. Clamped connectors handle
  comparable endpoints; mixed-coordinate rectangles handle the other case.
  Continuous finite selections preserve the cone estimates even with infinitely
  many face switches along a connector. This conditional result still needs
  actual covering strips and continuous compatible lifts from the cut surface.
- [x] Represent complete monotone polygonal paths by exact height graphs.
  Construct a strictly internal monotone connector to a target, splice it to
  an existing tail, and split the old strip with proved coverage and boundary
  intersection. The application must still construct compatible geometric tails
  and prove that each insertion avoids unprocessed cut segments.
- [x] Treat bounded-height strips directly, with no continuation of their maps
  beyond the actual clip. Connecting paths remain in the endpoint height slab.
- [x] Prove that a skirt tail meeting the old rim begins at that meeting point.
  Attached components correspond bijectively to old rim vertices.
- [x] Model the complete original-and-skirt geometric cut set as an explicit
  finite parent forest, including independent skirt leaves and degenerate tips.
  Prove exact carrier coverage, distinct vertex positions, endpoint incidence,
  and that distinct edges meet only at common endpoints.
- [x] Give each whole geometric component a fixed sector and represent every
  complete root path by an exact monotone height graph. Every geometric edge
  point lies above a childless descendant whose path contains that edge.
  This supplies the support lemma for processing leaves in height order.
- [x] Prove unique forward continuation at every nonterminal geometric cut
  point using half-open parent edges. Derive permanent merging of covered
  height graphs from finite closed-segment activity and increasing heights.
- [x] Construct exact covered tail graphs in a common sector network, including
  distinct components. Prove their coalescence and consistent sweep order on
  common height slabs. Distinct leaves avoid every already active tail.
- [x] Show that inserting a separator between coalescing neighbors preserves
  its entire actual tail up to a common cutoff. Completion below a leaf does
  not affect coalescence on later slabs.
- [x] Construct a finite subdivision from the actual active sector leaves,
  in height order with ties allowed. Preserve every actual tail to the common
  cutoff. Prove exact sector coverage, retained boundaries, and pairwise
  disjoint strip interiors. Every assigned geometric cut edge below the cutoff
  lies on a separator and avoids every strict strip interior.
- [x] Choose component sectors controlling positions as well as directions,
  including rim-only components and degenerate tips. Represent the exterior
  sector rays by monotone graphs; no covering strips are assumed as input.
- [x] Exclude cuts from all other sectors using exact strict-versus-closed
  sector tests. Choose a slab covering the original footprint in every sector
  frame, then a deeper clip, before auxiliary triangulation. Every actual tail
  tip lies beyond that slab; isolated degenerate tips cause no interior contact.
- [x] Construct the actual regular developed map and prove its continuity by
  finite closed-face gluing. Construct source-centered chart selections. These
  are derived from the given development, without compatible-lift hypotheses.
- [x] Prove uniform injectivity of the actual maps on every positive-width
  height slab of every constructed waterfall strip. Inset strips avoid assuming
  continuity through bank copies on a coincident projected tail.
- [x] Construct internal contour prefixes and suffixes between actual copies
  of a branch vertex. Every selected edge appears in paired banks; their exact
  displacement is the sum of whole sibling openings. Derive the right/down
  jumps of right banks and left/up jumps of left banks.
- [x] Compare entire opposite banks along every actual outward path. Both the
  whole-edge directions and all curvature-carrying subtrees share one derived
  sector. Regular interior contact has the same edge and parameter and zero
  subtree curvature, uniformly before both meshes. Branch vertices and different
  cut paths still require the global separation argument.
- [x] Prove coherence at every actual geometric leaf, including the source.
  Geometric leaves are local radial minima; outward fine cuts cannot enter them.
  Proper completed descendants are flat, so all actual developed copies agree
  even when extra flat cuts create several intrinsic vertex copies. Every such
  endpoint survives meshing and lies strictly inside the physical roof clip.
  The actual map is continuous on its proved coherent domain, including these
  pinches; no identification of distinct intrinsic copies is made.
- [x] Extend the actual map comparison across coherent reopening pinches.
  Permanently merged banks need no common map value. Prove a local insertion
  invariant that a separator creates no reopening pinches except at its target,
  once its pretarget strictness and posttarget wall persistence are established.
  Derive strict coordinate progress of actual whole cut tails, enclosing rays,
  connectors, and spliced walls, including targets on an exterior sector bank.
  Every nonterminal geometric node on a sector bank is a childless leaf.
- [x] Compare different positive-width components of every actual constructed
  waterfall strip across its possible pinches. Derive permanent exterior-bank
  contacts from exact radial graphs and forward uniqueness. Construct the finite
  waterfall preserving strict coordinate progress and proving that every
  reopening pinch is its source or an actual geometric leaf. Combine their
  proved coherence with regular strict interiors to obtain uniform injectivity
  on each entire physical strip slab, with tilt chosen before either mesh.
- [x] Classify closed-edge contacts of opposite complete banks, including branch
  endpoints. Different edges meet only at a common endpoint of adjacent edges,
  with the earlier subtree flat. Matched contacts have zero subtree curvature
  except possibly at the child endpoint. Every actual closed bank contact
  represents the same projected surface point, uniformly before both meshes.
- [x] Derive arbitrarily small linear chart error from actual angular and
  projection-length bounds, in the same calibration as the bank-order data.
  Pass quantitative error through continuous finite chart selections and inset
  source connectors, including coherent pinches. Obtain uniform actual
  whole-strip injectivity and source-position control together. Every such strip
  stays in its open sector quadrant relative to the common developed source.
- [x] Construct actual one-sided strip boundary traces. Uniform affine norm
  bounds survive arbitrary continuous face changes and coherent reopening
  pinches, giving an 8-Lipschitz actual map on every strict bounded strip.
  A continuous extension gives unique closure values; finite closed-face
  selection proves each value is an actual containing-face placement. The
  waterfall is chosen before its development and calibration. Bank matching,
  full boundary-curve parametrization, and global separation remain open.
- [x] Parametrize both complete actual bank traces from the common source up
  to every active positive-width height. Finite coherent pinches imply all
  those bank points lie in the strict-strip closure. Each trace value is
  approached through its own containing face, and the source value is its
  actual coherent developed value. Permanently collapsed continuations are
  not identified with these one-sided traces.
- [x] Transfer position estimates to every actual containing-face copy. Finite
  waterfall walls are closed nowhere dense, so strict cells are dense within
  each projected face in the open comparison region. Facewise continuity
  extends the estimate to every bank and branch copy in the same bank-order
  calibration, with the tilt threshold chosen before either mesh.
- [x] Keep every actual containing-face copy uniformly within its assigned
  sector quadrant relative to the common developed source. The positive
  coordinate margin is proportional to source distance and depends only on
  the sector parameter; branch copies need not coincide.
- [x] Identify every named complete-bank point with its own actual incident-face
  placement and transfer the common-source error and coordinate bounds to it.
  Opposite branching banks lying in a common source quadrant have the correct
  equal-radius order, without radial monotonicity assumptions on branch jumps.
- [x] Prove the local facing-face criterion: a regular projected seam point
  has exactly its two actual incident-face labels. A trace approached strictly
  from one side cannot use the opposite closed face. Apply this criterion to
  locally matching lower and upper strip walls. Prove covered finite-network
  tails agree locally with their actual straight edge away from network vertices.
- [x] Instantiate local straight-edge agreement for actual geometric sector
  tails: regular interior mesh points avoid every geometric network vertex.
  Derive one-sided strip approach directly from positive width and local cut
  avoidance, including a wall that only touches the cut.
- [x] Derive physical entrance/exit face signs in the actual sector frames.
  Construct the parent edge's exact height graph and local cut interval.
  Regular positive-width lower/upper strip traces select the actual named
  entrance/exit charts from cut avoidance, without supplied side certificates.
- [x] Derive positive width at actual regular bank points before any later
  active height. Every possible reopening pinch is a preserved mesh vertex,
  so regular points avoid the constructed pinch set.
- [x] Retain geometric cut avoidance, pinch control, all-development coherence,
  and complete one-sided bank traces for the same constructed waterfall.
  Earlier public theorem statements follow unchanged from these stronger
  constructors, with no duplicated construction proofs.
- [x] Keep the full closed strip, including both banks, within the deep sweep
  ball. Subdivision bounds now derive regular bank width without a separate
  interior-location hypothesis.
- [x] Construct matched regular-bank traces for the actual roof waterfall,
  before its development or calibration. Width, cut avoidance, and one-sided
  values are derived for the same subdivision. Every regular parent-edge
  portion has its actual entrance/exit chart, without supplied matching data.
- [x] Extend actual source-position error to all visible trace points by
  continuity. Derive positive radial inner-product tests from quantitative
  sector margins and linear chart error. Actual visible monotone-bank traces
  progress strictly radially under these numerical bounds, allowing arbitrary
  face switches and coherent branch points.
- [x] Construct radial bank traces uniformly before both meshes. One actual
  bank-order calibration gives the same curves their named regular-bank
  matching, whole-strip injectivity, and arbitrarily small position error.
  Radial progress includes all coherent branch points before an active height.
- [x] Bound every actual containing-face copy at a branch between its named
  entrance and exit banks. Visible strip traces retain these bounds at the
  vertex, using the actual contour copy without identifying distinct copies.
- [x] Prove actual branch gaps are zero if their controlling coordinate is
  zero, and prove controlling-coordinate injectivity for weakly monotone
  chains whose zero-coordinate steps are flat.
- [x] Construct paired comparison chains from every actual branch copy along
  the entire outward parent path, with explicit straight branch-gap segments.
  Prove their controlling-coordinate injectivity and opposite-bank circle
  order in a common source quadrant, retaining zero-length gaps.
- [x] Transfer one geometric component sector to all physical fine path
  positions, outward directions, and curvature-carrying descendant openings.
  Whole original and radial cut pieces retain the same sector data.
- [x] Construct exact physical cut-path prefixes ending on a prescribed source
  sphere before the far clip boundary. Every preceding physical point lies in
  that source ball, with the component position and direction sectors retained.
  Identify original comparison edges and branch gaps with actual face values.
- [x] Derive common developed source-quadrant bounds for all points of the
  finite comparison prefixes, including straight branch-gap chords. Discharge
  their circle-order quadrant hypotheses and bound both endpoint margins in
  terms of the physical stopping radius.
- [x] Retain strict roof curvature and all calibrated bank geometry at one
  uniform tilt. Represent actual visible branch trace values by their own
  contour copies for the comparison continuation's initial value.
- [x] Prove paired-bank circle order with only rightward right-bank and upward
  left-bank progress. Straight branch-gap steps may decrease the other
  coordinate; no radial monotonicity of these steps is required.
- [x] Retain one uniform actual calibration for all face-copy source quadrants,
  radial matched traces, injective strips, and position errors. Derive two-sided
  source-distance bounds for all face copies. Straight segments between copies
  at the same branch retain the positive source-quadrant margins.
- [x] Construct continuous paths with the whole comparison-bank images and
  graph homeomorphisms to their controlling-coordinate intervals. Strict
  endpoint progress gives simple arcs despite flat gaps and repeated vertices.
  The visible trace supplies their exact common initial value. First-crossing
  initial subpaths stay strictly inside a source circle before their endpoint.
- [x] Derive strict endpoint progress from the physical stopping radius and
  construct paired simple comparison subarcs to one source circle, retaining
  their actual comparison-bank images and their order at all common radii.
  Each nonterminal arc point stays strictly inside the ball. Separation from
  the developed strip interiors is not asserted here.
- [x] Construct these proper comparison arcs uniformly in the same actual
  radial matched-bank calibration, with margin and tilt preceding both meshes.
  Retain the physical stopping seam, bounded prefix, component sector, contour
  start, actual bank-image inclusion, and whole-arc quadrant/circle order.
- [x] Prove quantitative lower distance bounds through coherent reopening
  pinches and extend them to the actual trace closure. Construct the complete
  visible bank trace injectively on that closure, including terminal pinches;
  permanently collapsed future tails stay excluded.
- [x] Construct full closed-trace injectivity together with radial matched
  banks and position errors at one uniform tilt, retaining strict roof curvature
  and normal-height bounds. Preserve the existing radial-bank theorem statement.
- [x] Prove exact frontier transport for open planar sets with compact closure
  under a continuous map injective on that closure.
- [x] Prove compactness of bounded strip slabs and their open-slab closures.
  The physical frontier consists only of banks and end levels, including
  reopening pinches. Transfer this to the whole developed strip-image frontier
  using closed-trace injectivity, with no unaccounted boundary components.
- [x] Extend radial progress to approached terminal bank heights and prove
  positive-circle bank uniqueness there. Parametrize source-quarter circles
  by a real coordinate. Prove the single-interval criterion from closed-trace
  injectivity, radial banks, source normalization, quadrant bounds, and
  end-level avoidance, retaining actual bank endpoints and the empty case.
- [x] Derive every circle-interval hypothesis for the same uniformly constructed
  strips. Retain their coherent pinches, source normalization, visibility, radial
  progress, and closed injectivity together. Every positive source circle below
  one quarter of the cutoff meets each strip in at most one bank-bounded
  interval, with the tilt chosen before both meshes. Only approached end-level
  points require distance bounds; permanently collapsed tails are excluded.
- [x] Realize both endpoints of every nonempty controlled circle slice at actual
  approached bank heights and prove their developed values distinct. Recover
  a face approached from the same strip at every closed trace point, including
  terminal pinches with no later active height.
- [x] Prove strict lower/upper order within each nonempty circle slice. Comparable
  physical points move strictly outward; mixed-coordinate moves increase the
  signed developed coordinate. Finite recoverable pinches keep the connecting
  paths in the approached closure. The uniform oriented-circle construction
  derives every margin and chart bound before both meshes.
- [x] Prove nonempty controlled circle slices meet their physical banks at
  positive width and heights strictly between source and cutoff. This supplies
  direct named entrance/exit matching at every regular circle endpoint.
- [x] Compare adjacent equal-radius bank endpoints on a specified coherent
  shared prefix: they either coincide at the same prefix height or both lie
  beyond it. Deriving the needed prefix and tail correspondences for every
  actual adjacent pair remains part of the global separation argument.
- [x] Track every actual geometric leaf tail along the constructed fine outward
  parent path up to the deep cutoff. Original and radial pieces belong to the
  same deterministic sector network; its forward uniqueness identifies coarse
  tail points with whole fine-edge points. The actual construction supplies
  component labels, edge support, nonzero outward directions, and far endpoints.
- [x] Retain leaf/separator provenance for the same developed subdivisions:
  every separator completes a named actual leaf tail, every active leaf is
  represented, and both walls retain strict coordinate progress. One uniform
  calibration supplies the same subdivision its complete radial strip data.
- [x] Exclude all actual vertex-copy values using one finite exceptional radius
  set for every strip and sector. Prove open overlap cannot hide on a finite
  family of exceptional source circles.
- [x] Identify regular circle endpoints on actual parent paths with their named
  complete comparison banks. Derive their facing order and separate the open
  circle slices, permitting boundary contact when the gap is flat.
- [x] Prove actual tail-circle separation after a common constructed leaf.
  Leaf tracking and the specified leaf sector supply both complete path banks
  and all curvature-carrying descendant directions; no gap-order certificate
  or comparison-curve separation is an input.
- [x] Derive coherent shared prefixes for actual adjacent separators. Reopening
  wall contacts lie in the coherent pinch set; a leaf cannot lie on an earlier
  distinct tail. Both exterior-ray contacts and collapsed neighbors with later
  positive width are included. No supplied shared-prefix coherence is needed.
- [x] Uniformly construct one radial trace family with disjoint neighboring
  strip-circle slices off the finite vertex-radius set. Tilt and error bounds
  precede both meshes, and all prefix, tail, leaf-copy, curvature-sector, and
  chart-matching hypotheses are derived for this same subdivision.
- [x] Prove empty nonexceptional circle slices place the entire approached
  closure strictly inside the circle. A nonempty strip absent from a controlled
  circle has a permanent terminal pinch below the cutoff, with an actual
  one-sided face trace inside. Pinch radii and the maximal closure radius add
  only finitely many exceptions.
- [x] Classify every approached zero-width pinch of the actual waterfall as
  a geometric vertex, including terminal contacts and exterior sector rays.
  Preserve it as a fine cut vertex in the same uniform radial and adjacent
  circle construction. A disappearing strip supplies its own actual contour
  copy strictly inside the source circle.
- [x] Continue every disappearing nonempty strip from its own terminal contour
  copy by a pair of simple proper comparison arcs, with ordered source-circle
  ends. The actual trace family supplies all-face quadrant margins in the same
  calibration. One uniform threshold before both meshes supplies these arcs
  and neighboring-strip separation together. Separation of the continuation
  arcs from other strips is not yet proved.
- [x] Prove the closing density argument: global circle separation in the common
  developed plane implies separation of actual face-interior images in the
  controlled physical region. Strip images are open and individually injective;
  finite exceptional circles and physical subdivision walls cannot hide open
  overlap. Combine every vertex-copy and disappearing-strip exception in one
  finite radius set. This is conditional on the remaining global separation.
- [x] Prove every permanently merged positive bank pair follows a named
  actual geometric leaf tail, with that leaf starting no later than the tested
  height. Fresh leaf avoidance gives positive insertion width, including tied
  heights and source insertions. Retain these tail witnesses in the same
  uniform circle construction. Every geometric vertex reached on a tail is
  an ancestor in that same component.
- [x] Track completed fine parent paths from an arbitrary intermediate geometric
  tail height, retaining the specified sector and all curved descendant sectors.
  Continue the actual terminal contour copy in that same sector. When both
  surviving crossings occur after an intermediate terminal height, derive their
  actual bank order and separate their open circle images.
- [x] Prove coordinate monotonicity of actual visible traces along geometric
  cut tails, through continuous finite affine-chart selection. Regular approached
  bank points have positive width without requiring a later active height.
  Named parent-bank matching bounds an early left exit horizontally and an
  early right entrance vertically by the intermediate terminal copy. Complete
  comparison-chain increments give the complementary late-crossing bounds.
- [x] Derive that a permanently collapsed strip ends after every actual leaf
  completed by either bank. Extend coherent prefix agreement to independently
  witnessed active heights. An empty neighbor cannot share a surviving
  crossing on that prefix, so the crossing lies strictly after the shared leaf.
- [x] Combine the early and late bounds to separate surviving actual circle
  slices across one nonempty disappearing strip, in all four height cases.
  Both early crossings use an interior terminal corner; mixed cases use one
  coordinate, and both late crossings use their common actual parent path.
- [x] Integrate one-strip separation into the uniform roof construction: the
  same error bound, tilt threshold, calibration, subdivision, and actual trace
  family supply neighboring separation, terminal continuations, and separation
  across one nonempty disappearing strip. All geometric leaf copies, sectors,
  prefix agreements, and matching data are derived before applying the result.
- [x] Retain the ordered physical chain of subdivision cells, including
  zero-width cells. An arbitrary finite run of permanently collapsed strips
  identifies both outside banks with an actual terminal parent path. Separate
  surviving circle slices when both crossings lie beyond that run's terminal
  heights. Early crossings for nonempty physical strips are handled below.
- [x] Remove the circle hypothesis from actual bank progress bounds. Finite
  physical vertex heights and trace continuity extend these bounds to whole
  closed intervals, including branch vertices and terminal endpoint values.
- [x] Prove individual developed coordinate order across each closed physical
  strip level. Every regular common bank point strictly inside a sweep sector
  lies on an actual leaf tail in that sector, so its fine parent-bank gap order
  is derived even across intervening collapsed cells.
- [x] Contract zero-width cells from the actual ordered cell chain at a tested
  height while retaining original cell membership. All surviving developed
  bank intervals are ordered pairwise at every regular physical height.
  Finite vertex heights and continuity extend this order to any two approached
  banks in subdivision order, including terminal vertex copies. This compares
  equal physical heights; global equal-radius separation still remains.
- [x] Propagate actual terminal coordinates through strict height records to
  the first and last maximal terminal heights. Compare tied maxima using the
  actual approached-level theorem. First/last threshold crossings derive both
  early circle bounds, while collapsed bank chains derive both late bounds.
- [x] Separate surviving actual circle slices across an arbitrary finite run
  of disappearing strips with nonempty physical interiors, in all four height
  cases. Every strip retains its own actual terminal copy and continuation;
  no synthetic curve avoidance or supplied developed gap order is assumed.
- [x] Remove entirely empty physical open slabs, retaining exact bank contacts
  on the controlled closed height interval. Transfer actual prefix values,
  completed tails, terminal records, and circle endpoint order across them.
- [x] Extract every finite removed run, including the empty run, and assemble
  pairwise separation of all actual strip-circle images within one sector.
  Restore empty image entries. Package this with a uniform tilt threshold
  quantified before both meshes in
  [ExtendedSectorCircleGeometry](../Unfoldings/Cap/ExtendedSectorCircleGeometry.lean).
- [x] Classify actual boundary cuts as radial skirt components or coherent
  leaf endpoints. Prove boundary components have no attached original trees
  and support actual parent-bank comparison in either neighboring sector.
- [x] Match actual circle endpoints from different frames with their named
  bank points in one developed plane, and derive their cross-frame order on
  a boundary component using uniform face margins and finite vertex radii.
- [x] Retain both original physical sector banks after empty endpoint cells
  are removed. Place a boundary run's highest actual terminal and its suffix
  on the enclosing ray and prove the terminal belongs to an unattached radial
  component, including equality with its geometric leaf height.
- [x] Translate inner-terminal coordinate bounds to argument order and preserve
  equal-radius endpoint order between overlapping oriented quadrant frames.
- [x] Identify the same actual radial component for the extreme disappearing
  runs on both sides of a shared named sector ray, retaining distinct heights
  and terminal contour copies. Match named bank charts through closed mesh
  endpoints and track every intermediate component position on an actual fine
  parent path ending at the genuine outer tip.
- [x] Prove the actual five-sector fan makes exactly one turn, its frame
  margins sum to π/4, and every nonadjacent pair of open comparison quadrants
  is disjoint, including across the argument seam. Separate their actual
  developed strip images with a positive trace-error bound chosen before
  any mesh or subdivision, deriving each physical cell margin.
- [x] Approach first/last maximal boundary-run terminals along the actual
  enclosing bank from below. Match these copies through fine vertices with
  named incoming parent banks. Derive fine ancestry, actual incoming edges,
  sector directions, and their positive boundary-ray heights from shared
  radial-component positions.
- [x] Prove a cross-frame bank-chain separation theorem for points inside or
  on the source circle. Actual fine-path order selects the useful coordinate
  in its own sector frame. Derive strict bounds for every open strip-circle
  point and apply the theorem to actual trace images, conditional on their
  own terminal/circle endpoint bounds on that common bank chain.
- [x] Derive a single actual fine bank chain for two named edges on a shared
  unattached radial component, including both sector geometries and the
  cross-frame coordinate comparison. Transfer uniform physical face margins
  and inner-radius bounds to the actual approached terminal copies.
- [x] Extend early-crossing bounds to every maximal terminal copy, retaining
  actual subdivision order at tied heights. Preserve the component assignment
  in boundary-terminal witnesses and rule out disappearing boundary runs on
  both sides of a shared sector ray.
- [x] Retain the exact leaf supporting an actual boundary terminal. Prove
  that every nonroot geometric node of its unattached component is the seed,
  represent that seed by a coherent fine vertex, and derive actual fine
  ancestry to the terminal. Each terminal is coherent or has an actual
  incoming fine bank with positive boundary height and derived sector control.
- [x] Cover every boundary-prefix position by an approached bank of an
  actual disappearing-run strip. Exclude a coherent contact there with a
  neighboring source-circle trace. The cut classification and terminal tail
  then place every neighboring boundary-circle crossing on the same actual
  radial component as the terminal, in either boundary orientation.
- [x] Recoordinate shared physical bank points exactly in either neighboring
  frame. Cover all nontip component positions by the actual fine seed path.
  Bound approached circle points in a physical source ball and match their
  actual entrance/exit fine banks, retaining component membership and exact
  source radii with only finite vertex-radius exclusions.
- [x] Identify both named bank values at coherent physical points. Combine
  coherent terminal vertices and derived incoming banks into one actual
  terminal candidate theorem, retaining the fine edge, parameter, component,
  exact trace value, and strict inner-radius bound in either orientation.
- [x] Apply component-derived bank comparison directly to actual strip-circle
  images, constructing the common fine path and both sector geometries from
  the candidates. Derive strict cross-frame circle quadrants from uniform face
  margins. The remaining inputs bound each strip by its own actual candidate.
- [x] Construct both candidates for a one-run boundary comparison from actual
  data: the neighboring surviving circle endpoint and an early-or-late run-side
  bank bound. Derive shared coordinates, component membership, fine path, bank
  names, parameters, and radii. Retain the run-side candidate trace origin for
  subsequent comparison-margin estimates.
- [x] Derive both comparison-frame margins from the candidates' actual
  approached terminal or circle traces on the shared physical ray. Prove
  actual neighboring circle-image separation across either upper or lower
  disappearing boundary run, including early and late crossings and ties.
- [x] Prove adjacent outer-circle separation with no disappearing run.
  Account for different sector height scales and actual radial cuts on the
  shared ray: the endpoints coincide coherently or lie on one component,
  whose coherent fine seed, bank candidates, and margins are constructed.
- [x] Retain full survivor-bank endpoint order, with arbitrary actual slice
  choices, and prove that every sector circle has a survivor. Strengthen
  outer-bank and disappearing-run separation to whole circle portions bounded
  by the actual bank coordinates, preserving existing image-separation APIs.
- [x] Assemble actual extreme survivors and indexed removed boundary runs.
  Derive every within-sector endpoint bound in both coordinates and prove
  pairwise separation of all actual strip-circle images across all five sectors,
  including arbitrary adjacent-sector cells and empty images.
- [x] Instantiate all-sector separation uniformly from a positive tilt threshold
  chosen before both meshes. Apply finite-radius avoidance and common-source
  position estimates to actual roof-face interiors in a controlled physical ball.
- [x] Prove nonoverlap invariance under normalization and transfer from any
  development of a connected conforming refinement to a coarse development.
- [x] Build the actual original-face restriction and isometric subdivision.
  [ClipOriginalSubdivision](../Unfoldings/Cap/ClipOriginalSubdivision.lean)
  proves unique original parents, actual rigid coordinates, and coverage of
  every closed original face.
- [x] Prove that every retained fine seam maps to an actual retained original
  seam chain. [ClipOriginalRespects](../Unfoldings/Cap/ClipOriginalRespects.lean)
  derives the actual original seam and its retention from the geometric cut set.
  [ClipOriginalCopies](../Unfoldings/Cap/ClipOriginalCopies.lean) identifies all
  fine copies within one original face, including vertices, and
  [ClipOriginalFaceMap](../Unfoldings/Cap/ClipOriginalFaceMap.lean) constructs
  continuous whole-face maps into the retained fine realization.
- [x] Lift every retained original seam chain to the actual fine subdivision.
  [ClipOriginalConforming](../Unfoldings/Cap/ClipOriginalConforming.lean) constructs
  exact retained-seam conformity and the intrinsic metric equivalence, including
  all seam endpoints. [ClipOriginalNonoverlap](../Unfoldings/Cap/ClipOriginalNonoverlap.lean)
  transfers nonoverlap from any fine development of a connected original cut cap.
- [x] Prove that actual exterior skirt cuts leave exactly the original retained
  seams on original faces; see [OriginalCutRestriction](../Unfoldings/Cap/OriginalCutRestriction.lean).
- [x] Prove side-by-side separation of all developed strips and hence all
  distinct original face interiors.
- [x] Apply the cut-disk and flat-development infrastructure to the fixed-wedge
  forest. All vertex copies are on the boundary, so the actual open cut disk
  is flat. Construct a locally isometric development, unique after fixing
  one original face, with overlap permitted.
- [x] Apply the geometric nonoverlap argument to a constructed source-centered
  forest and transfer it from the actual roof mesh to original input faces.
- [x] State uniform original-edge nonoverlap using only cap and acute-margin
  assumptions. The output includes a boundary-rooted forest, actual cut disk,
  and local isometry throughout the open disk; see
  [EdgeUnfolding](../Unfoldings/Cap/EdgeUnfolding.lean).
- [ ] Obtain the paper's full simple-polygon conclusion, including boundary injectivity.
- [x] Remove all zero-curvature descendant subtrees from the original cut forest.
  [FlatSubtreeBanks](../Unfoldings/Cap/FlatSubtreeBanks.lean) proves pointwise
  agreement of the actual whole seam banks, including positional offsets.
  [CurvaturePrunedForest](../Unfoldings/Cap/CurvaturePrunedForest.lean) restores
  precisely these cuts, retains an actual original-edge rooted forest and cut
  disk, and proves that every remaining cut has positive subtree curvature.
  [CurvaturePrunedDevelopment](../Unfoldings/Cap/CurvaturePrunedDevelopment.lean)
  preserves necessary curvature cuts, nonoverlap, and interior local isometry.
- [x] Exclude foreign contacts at face interiors and retained nonvertex hinges,
  both globally and within the actual controlled roof region. Genuine regular
  points with a local isometry have unique developed preimages, including against
  boundary copies. [PrunedInteriorContact](../Unfoldings/Cap/PrunedInteriorContact.lean)
  applies this to the whole pruned cap interior and proves that global injectivity
  is equivalent to injectivity restricted to its intrinsic boundary.
- [x] Every remaining original parent cut has positive subtree curvature; its
  opposite regular bank interiors are strictly separate under the actual bank
  frame and curvature budget.
- [x] Retain possible circle endpoint contacts with weak bank bounds. Actual
  approached closed strip-circle points are either open strip points or named
  bank endpoints; [ClosedStripCircleCaps](../Unfoldings/Cap/ClosedStripCircleCaps.lean)
  derives both actual weak barriers. [ClosedBarrierContact](../Unfoldings/Cap/ClosedBarrierContact.lean)
  identifies every contact with the common actual inner barrier, or with one of
  the two actual ordered bank points.
- [x] Exclude every foreign contact at regular locally isometric roof points
  using only local physical-region separation; see
  [LocalRegularContact](../Unfoldings/Cap/LocalRegularContact.lean).
- [x] Identify both actual bank values at weak circle contacts on an unattached
  radial component, even when comparison points lie inside the circle. Equality
  in the controlling coordinate forces matching parameters or a shared branch
  endpoint. See [CompletedBankCoordinateContact](../Unfoldings/Cap/CompletedBankCoordinateContact.lean)
  and [ComponentBankCircleContact](../Unfoldings/Cap/ComponentBankCircleContact.lean).
- [x] Identify both physical strip-bank coordinates at closed image contacts.
  [ClosedStripCircleContact](../Unfoldings/Cap/ClosedStripCircleContact.lean)
  handles ordered circles in one frame;
  [ComponentClosedCircleContact](../Unfoldings/Cap/ComponentClosedCircleContact.lean)
  handles actual component banks in different sector frames.
- [x] Apply the full finite waterfall survivor order to closed contacts and
  construct both slices from the contact itself; see
  [WaterfallClosedCircleContacts](../Unfoldings/Cap/WaterfallClosedCircleContacts.lean).
  This assembly inherits the existing finite radius exclusions.
- [x] Exclude all nonadjacent closed-sector contacts away from the source,
  including vertex and pinch radii, with no exceptional set; see
  [NonadjacentClosedSeparation](../Unfoldings/Cap/NonadjacentClosedSeparation.lean).
- [x] Classify any approached point on an absent controlled circle as a physical
  pinch and, in the actual mesh, a cut vertex. Thus an approached nonvertex
  circle point always supplies an actual open slice; see
  [ClosedCirclePinches](../Unfoldings/Cap/ClosedCirclePinches.lean).
  The proof uses a local positive-width bank crossing and an explicit path.
- [x] Identify the same physical surface point at actual facing outer-bank
  contacts across adjacent sectors, allowing cuts along the shared ray; see
  [OuterClosedCircleContact](../Unfoldings/Cap/OuterClosedCircleContact.lean).
  Stronger companion lemmas retain coherent physical endpoint equality and
  the exact parameters of named fine banks.
- [x] Identify actual physical endpoints at weak circle contacts across either
  disappearing boundary run; see
  [BoundaryRunClosedCircleContact](../Unfoldings/Cap/BoundaryRunClosedCircleContact.lean).
  Strictly interior terminal candidates cannot contact the circle. Remaining
  candidates retain their exact physical crossing parameters.
- [x] Assemble no-run and disappearing-run cases for adjacent extreme survivors;
  [AdjacentSurvivorClosedCircleContact](../Unfoldings/Cap/AdjacentSurvivorClosedCircleContact.lean)
  identifies both actual developed endpoints and their common physical point.
  Actual maximal terminals are chosen by
  [BoundaryRunClosedConstruction](../Unfoldings/Cap/BoundaryRunClosedConstruction.lean).
- [x] Pass from adjacent extreme survivors to arbitrary approached closed contacts.
  [WaterfallClosedCircleExtremeBounds](../Unfoldings/Cap/WaterfallClosedCircleExtremeBounds.lean)
  excludes foreign contacts at the exposed extreme endpoints, and
  [AdjacentSectorClosedCircleContact](../Unfoldings/Cap/AdjacentSectorClosedCircleContact.lean)
  identifies arbitrary adjacent-sector physical contacts.
- [x] Assemble physical identification across every pair of distinct sectors;
  see [AcrossSectorClosedCircleContact](../Unfoldings/Cap/AcrossSectorClosedCircleContact.lean).
  The circle assembly retains its existing finite radius exclusions.
- [x] Identify physical points at actual same-path circle endpoint contacts;
  see [ParentPathCircleContact](../Unfoldings/Cap/ParentPathCircleContact.lean).
- [x] Identify contacts between consecutive within-sector survivors across a
  shared separator or any removed run; see
  [RemovedRunPhysicalContact](../Unfoldings/Cap/RemovedRunPhysicalContact.lean).
  Strict late coordinate bounds exclude early contacts at an interior terminal.
  The surviving late case identifies two points on one actual parent path.
- [x] Retain physical identifications in the full within-sector survivor order;
  [WaterfallCirclePhysicalOrder](../Unfoldings/Cap/WaterfallCirclePhysicalOrder.lean)
  uses Mathlib's lexicographic order on coordinates and singleton physical
  labels to preserve equality through the complete finite-order argument.
- [ ] Apply that order to arbitrary within-sector closed contacts.
- [ ] Identify all coincident intrinsic boundary copies after pruning, including
  cut vertices, contacts between different trees, and original rim points.
- [ ] Conclude boundary injectivity and state the simple-polygon existence theorem.

## Verification discipline

No `sorry`, extra axioms, circular geometric certificates, or placeholder main
theorem. Check and commit reusable milestones; import each completed module
through `Unfoldings.lean` so the default audit sees its proof dependencies.
