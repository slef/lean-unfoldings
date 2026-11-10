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
  The identity with intrinsic angular curvature remains open.

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

- [ ] Represent matched edge lengths and signed opening angles by actual rigid
  planar motions, retaining unwrapped real heading information.
- [ ] Define the left-of relation at equal radii without conflating touching
  with crossing or taking circular order to be a linear order globally.
- [ ] Prove Theorem 9 under all its hypotheses: radial monotonicity of both
  banks, nonnegative openings with total below pi, and cone measures below pi.
- [ ] Check the backward-induction argument against the 2021 clarification,
  including finite endpoints and every intermediate suffix.
- [ ] Extend to branching trees, including the altered opposite bank and
  curvature contributed by attached branches (Corollary 10).

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
- [ ] Orient the near-quadrants about the gap origin, assign every interior
  vertex to one, and prove choices stay in the same quadrant. Apply the local
  progress and selected-forest results to construct the cap's cut seams.
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
- [ ] Identify intrinsic angular curvature with the solid angle of its normal
  cone. The checked normal-cone identity and area bounds do not yet prove this.
  This volume-based route suffices for the cap theorem without first equating
  solid angle with normalized two-dimensional Hausdorff measure.
- [x] Prove relative angle-defect balance by summing original and projected
  face angles over the actual corner classes.
- [x] Derive projected interior-link flatness from the actual cyclic germ order,
  disjoint original-face direction cones, and the one-full-turn theorem.
  Consequently the actual cap curvature/boundary-angle balance needs no
  assumed projected flatness or Euler identity.
- [ ] Prove the geometric subregion identities used in the prefix-turn argument,
  including the truncation and artificial connecting segments.
- [ ] Bound turn distortion for every prefix independently of mesh size.
  Summing an error per vertex is insufficient.
- [ ] Choose a positive tilt threshold depending only on the acute margin that
  leaves all developed path headings in the required wedges.

A sufficient conservative curvature target is to bound each interior angular
defect by the area of its planar normal polygon. The checked packing bound
would then give total curvature at most `pi * tan(tilt)^2`. Proving the
spherical Gauss-image curvature identity is still required. The spherical-to-planar
area comparison is checked; it does not supply the curvature identity.

The next missing local identity, for an original interior vertex `v`, can use
`solidAngleMeasure` in place of normalized Hausdorff measure:

```text
ENNReal.ofReal (2 * pi - C.totalAngle Set.univ v)
  = solidAngleMeasure (K.sphericalNormalPolygon v).
```

`sphericalNormalPolygon_eq_outwardNormalCone` now identifies the
right-hand region from actual supporting geometry. The missing equality must
also handle repeated normals, coplanar incident triangles, and zero curvature.
Once proved, the checked area budget bounds the sum of all interior defects;
no accumulation of per-vertex projection errors is needed.

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
