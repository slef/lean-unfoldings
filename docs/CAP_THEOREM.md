# O'Rourke's nearly flat cap theorem

Target: Joseph O'Rourke, *Edge-Unfolding Nearly Flat Convex Caps*,
[2021 extended version](https://arxiv.org/abs/1707.01006v4), Theorem 1.
This is a proof-development checklist; unchecked claims are not Lean declarations.

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
horizontal coordinate. This follows from scalar coordinate increments and
includes whole edges. It may replace the full Theorem 9 for a conservatively
smaller acute-cap threshold, provided the geometric heading, branching, and
global strip hypotheses are constructed. It is not a proof of Theorem 9.

### Planar forest construction (Section 5)

- [ ] Model the actual projected triangulation and its boundary.
- [ ] Obtain an empty angular gap at a suitable internal vertex and choose
  near-quadrants avoiding degeneracies. Use a conservatively reduced margin.
- [ ] Grow angle-monotone paths until they hit an existing tree or the rim.
  Prove termination, coverage, no cycles, and exactly one root per component.
- [ ] Handle the cap with no interior vertices separately.

### Uniform geometric estimates (Sections 4 and 6)

- [x] Bound orthogonal projection angle distortion using the maximum normal tilt.
  The checked existential threshold is uniform over all unit tangent directions.
  It uses compact-annulus angle continuity rather than the paper’s explicit formula.
- [ ] Relate total cap curvature to the area of its spherical normal region.
- [ ] Prove the polygonal Gauss--Bonnet identity on the required subregions.
- [ ] Bound turn distortion for every prefix independently of mesh size.
  Summing an error per vertex is insufficient.
- [ ] Choose a positive tilt threshold depending only on the acute margin that
  leaves all developed path headings in the required wedges.

### Global assembly (Sections 9--10, Appendices A.5--A.6)

- [ ] Construct the cap-specific extension needed to control cut endpoints.
- [ ] Construct the actual waterfall strip partition; prove complete coverage
  and that its artificial boundaries are compatible with the development.
- [ ] Prove side-by-side separation of all developed strips and hence all
  distinct original face interiors.
- [ ] Apply the cut-disk and flat-development infrastructure to the constructed
  forest, proving flatness at every remaining interior vertex.
- [ ] State the full cap theorem using only cap and acute-margin assumptions.
- [ ] Address redundant flat cuts and the precise simple-polygon conclusion.

## Verification discipline

No `sorry`, extra axioms, circular geometric certificates, or placeholder main
theorem. Check and commit reusable milestones; import each completed module
through `Unfoldings.lean` so the default audit sees its proof dependencies.
