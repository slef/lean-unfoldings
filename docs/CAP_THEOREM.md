# O'Rourke's nearly flat cap theorem

Target: Joseph O'Rourke, *Edge-Unfolding Nearly Flat Convex Caps*,
[2021 extended version](https://arxiv.org/abs/1707.01006v4), Theorem 1.
This is a proof-development checklist; unchecked claims are not Lean declarations.
**The full nonoverlap theorem is not yet proved.**

Current entry points:

- [ForestExistence](../Unfoldings/Cap/ForestExistence.lean) constructs an actual
  original-edge rooted forest for uniformly small positive tilt.
- [ForestDevelopment](../Unfoldings/Cap/ForestDevelopment.lean) constructs its
  intrinsic cut disk and a locally isometric development, allowing overlap.
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
  (Corollary 10). The actual whole-subtree opening identity is checked; safe
  headings and separation remain to be proved.

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
- [ ] Match each trace crossing's signed phase to the actual geometric crossing
  counter, compose the transitions, and assemble the uniform heading bound from
  the common anchor. Local transitions alone do not establish global headings
  or nonoverlap.
- [ ] Prove the geometric subregion identities used in the prefix-turn argument,
  including the truncation and artificial connecting segments.
- [ ] Bound turn distortion for every prefix independently of mesh size.
  Summing an error per vertex is insufficient.
- [ ] Choose a positive tilt threshold depending only on the acute margin that
  leaves all developed path headings in the required wedges.

The checked numerical estimate, for `3/4 ≤ c` and all normal heights at least
`c`, is

```text
totalInteriorAngularDefect ≤ 81 * (sqrt (1 - c²) / c)² * pi.
```

The constant is conservative. Continuity at tilt zero gives an arbitrarily
small total-curvature budget uniformly across all meshes. The proof uses
volume-induced solid angle; it does not need an equality with normalized
Hausdorff area. Uniform prefix-turn control and global nonoverlap remain open.

### Global assembly (Sections 9--10, Appendices A.5--A.6)

- [ ] Construct the cap-specific extension needed to control cut endpoints.
- [ ] Construct the actual waterfall strip partition; prove complete coverage
  and that its artificial boundaries are compatible with the development.
- [ ] Prove side-by-side separation of all developed strips and hence all
  distinct original face interiors.
- [x] Apply the cut-disk and flat-development infrastructure to the fixed-wedge
  forest. All vertex copies are on the boundary, so the actual open cut disk
  is flat. Construct a locally isometric development, unique after fixing
  one original face, with overlap permitted.
- [ ] Apply the geometric nonoverlap argument to a constructed source-centered
  forest and its developed banks.
- [ ] State the full cap theorem using only cap and acute-margin assumptions.
- [ ] Address redundant flat cuts and the precise simple-polygon conclusion.

## Verification discipline

No `sorry`, extra axioms, circular geometric certificates, or placeholder main
theorem. Check and commit reusable milestones; import each completed module
through `Unfoldings.lean` so the default audit sees its proof dependencies.
