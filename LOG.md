# LOG

## Session Log

### 2026-11-11 — circle order allowing straight branch-gap steps

- Proved matched coordinate-increment bounds give global left-or-above order
  using only right-bank horizontal and left-bank vertical progress. The other
  coordinate may decrease along a branch-gap step.
- Derived equal-radius circle order for such paired chains in a common source
  quadrant, without radial monotonicity assumptions on the gap steps.
- Verification: cache retrieval followed by full `lake build` pass; **8,460
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  whitespace passes. Constructing the complete actual comparison chains and
  global nonoverlap remain open.

### 2026-11-11 — ordered actual copies at branch endpoints

- Represented every intrinsic branch copy by its actual contour index and
  transferred the derived sibling-excursion gap order to it.
- Proved every actual containing-face value at a branch, and every visible
  strip-trace copy there, lies between the named entrance and exit banks.
  Distinct copies need not agree.
- Verification: cache retrieval followed by full `lake build` pass; **8,458
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,191**) and whitespace pass. Complete bank
  continuations beyond collapsed tails and global separation remain open.

### 2026-11-11 — uniform radial matched banks in one actual calibration

- Constructed `exists_uniform_extended_radial_bank_traces`. A positive tilt
  threshold precedes both meshes and gives the actual bank-order calibration
  arbitrarily small linear and source-position error.
- In that same calibration, each constructed strip has an injective actual
  map and continuous one-sided traces that progress strictly radially up to
  every active height and match all regular named parent-bank pieces.
- Verification: cache retrieval followed by full `lake build` pass; **8,455
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,190**) and whitespace pass. Branch endpoint
  copies, collapsed-tail continuations, and global strip assembly remain open.

### 2026-11-11 — radial progress through actual visible bank traces

- Derived quantitative positive inner-product tests from linear chart error
  and source-position margins. Continuous finite affine selections along a
  monotone height graph then progress strictly radially.
- Extended the actual developed source-position estimate to all visible trace
  points by continuity. Applied the radial criterion to actual containing-face
  traces, allowing arbitrary face switches and coherent branch points.
- Verification: cache retrieval followed by full `lake build` pass; **8,453
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,189**) and whitespace pass. Uniform actual
  radial-trace construction, complete continuations, and global assembly remain
  open; the full cap theorem is not proved.

### 2026-11-11 — constructed matched regular-bank traces

- Packaged matching of every regular parent-bank piece before each active
  strip height, retaining the actual entrance/exit face names.
- Constructed `cornerExtendedOutward_exists_matched_bank_traces` for the actual
  roof. The waterfall precedes development and calibration; its cut avoidance,
  regular width, one-sided values, and bank identities are all derived.
- Verification: cache retrieval followed by full `lake build` pass; **8,447
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,185**) and whitespace pass. Branch endpoints,
  radial order, full continuations, and global separation remain open.

### 2026-11-11 — closed banks stay inside the comparison clip

- Proved every point of the closed enclosing strip has norm at most its
  nonnegative diagonal height. Both actual banks therefore stay in the deep
  comparison ball, including sector boundaries.
- Derived regular bank width directly from deep clipping, subdivision bounds,
  and the constructed pinch set; no separate interior-location proof is needed.
- Verification: cache retrieval followed by full `lake build` pass; **8,444
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,183**) and whitespace pass. Full cap
  nonoverlap remains open.

### 2026-11-11 — retain geometry and traces for one actual waterfall

- Strengthened the constructed waterfall output to retain geometric cut
  avoidance together with pinch control and coherence for every development.
- Constructed complete bank traces for this same waterfall while retaining
  those geometric facts, so trace matching can use its actual cut-avoidance
  proof. Refactored the earlier constructors through the stronger results;
  their public theorem statements are unchanged.
- Verification: cache retrieval followed by full `lake build` pass; **8,441
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,181**) and whitespace pass. Global strip
  separation and the cap theorem remain open.

### 2026-11-11 — automatic positive width at regular bank points

- Proved every regular carrier point before a later active strip height has
  positive width if reopening pinches are confined to the designated set.
- Proved actual regular mesh points avoid the source and all geometric leaf
  pinch points. Derived `regular_waterfall_width` for the constructed actual
  pinch set, including both banks.
- Verification: cache retrieval followed by full `lake build` pass; **8,439
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,179**) and whitespace pass. Global strip
  separation and the full cap theorem remain open.

### 2026-11-11 — named entrance/exit strip-trace matching

- Proved positive sector frames preserve physical directed-edge side signs.
  Exact segment height graphs retain both endpoints, the full physical edge,
  strict interior heights, and transported cut avoidance.
- Derived signed-side bounds for the actual complete-bank incident faces from
  the positively oriented contour. Constructed each actual parent cut graph
  and derived its face signs and local cut interval.
- Proved regular positive-width lower and upper strip traces select the named
  entrance and exit charts. Physical cut avoidance supplies the local side
  test; no bank-side or wall-coincidence certificate is assumed.
- Verification: cache retrieval followed by full `lake build` pass; **8,436
  unfolding / 7,243 pinned topology declarations**, standard axioms only.
  Branch endpoints, complete continuations, and global separation remain open.

### 2026-11-11 — actual local tail edges and one-sided cut contacts

- Proved regular interior roof-mesh points avoid every geometric cut vertex:
  nonroots survive meshing, while roots lie on the outer clip boundary.
- Derived `SectorTailGraph.locally_eq_edge` for actual sector tails from the
  finite network, with its genuine coordinate steps and physical edge graph.
- Proved positive strip width and local cut avoidance force the side of an
  approached cut even at a mere wall contact. Added facing-trace criteria
  that use this fact without requiring local coincidence with the wall.
- Verification: cache retrieval followed by full `lake build` pass; **8,401
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  documentation and whitespace checks pass. Actual bank-side signs and global
  strip separation remain open.

### 2026-11-11 — local facing-face and straight-tail criteria

- Classified the actual containing faces of every regular projected seam
  point from exact intrinsic equivalence classes.
- Proved one-sided trace visibility excludes the opposite closed half-plane,
  with lower/upper strip-wall versions requiring only local wall agreement.
- Proved a covered finite-network height graph locally agrees with its actual
  affine edge graph away from network vertices, deriving local agreement from
  finite closed-edge activity and forward uniqueness.
- Verification: cache retrieval followed by full `lake build` pass; **8,393
  unfolding / 7,243 pinned topology declarations**, standard axioms only.
  These are local criteria; their full actual-waterfall instantiation and the
  global nonoverlap theorem remain open.

### 2026-11-11 — actual bank face values and common-source circle comparison

- Proved each complete entrance/exit bank point equals its own incident-face
  chart at the physical parent segment, including closed endpoints. The
  physical point lies in both incident closed faces.
- Transferred facewise source errors and quadrant margins to these named bank
  points. Proved equal-radius order for opposite branching banks in a common
  source quadrant, retaining all intermediate sibling displacements and
  requiring no radial monotonicity of their jumps.
- Verification: cache retrieval followed by full `lake build` pass; **8,384
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,167**) and whitespace pass. Facing strip
  banks, complete continuations, and global separation are still open.

### 2026-11-11 — quadrant margins for every bank and branch copy

- Converted sector coordinate margins to bounds proportional to source
  distance. Proved actual containing-face errors are invariant under centered
  input frames and give quantitative developed coordinate margins.
- Derived `exists_uniform_extended_face_quadrants`: one positive margin and
  tilt threshold precede both meshes, in the actual bank-order calibration.
  Every containing-face copy in its assigned sector satisfies both margins,
  including distinct copies at a branch vertex.
- Verification: cache retrieval followed by full `lake build` pass; **8,375
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,164**) and whitespace pass. Full cap
  nonoverlap remains open.

### 2026-11-11 — source-position control for every actual face copy

- Proved finite monotone waterfall walls closed nowhere dense, and strict
  sector cells dense within each projected face in the open comparison region.
- Proved unique containing-face selection in face interiors and frame
  independence of source-position error. Facewise continuity transfers the
  strict-strip estimate to every containing-face value on cuts and branches.
- Derived `exists_uniform_extended_face_position_control`: arbitrarily small
  relative position error in the actual bank-order calibration, uniformly
  before both meshes. Different branch copies remain distinct.
- Verification: cache retrieval followed by full `lake build` pass; **8,371
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,162**) and whitespace pass. Facing-bank
  identification, complete continuations, and global separation remain open.

### 2026-11-11 — complete source-based bank traces with face visibility

- Proved finite reopening pinches leave both full banks up to every active
  height in the strict-strip closure. This includes the common source and
  isolated leaf pinches, without extending through permanently collapsed tails.
- Strengthened trace values to retain the face approached from the strip
  interior. An arbitrary containing-face choice is insufficient for bank
  matching. Proved equality with actual map values at coherent endpoints.
- Derived `cornerExtendedOutward_exists_waterfall_bank_traces` for the actual
  roof. The constructed curves start at its real developed source and retain
  one-sided face visibility at every bank point up to each active height.
- Verification: cache retrieval followed by full `lake build` pass; **8,352
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,156**) and whitespace pass. Facing cut-bank
  identification and global separation are still open.

### 2026-11-11 — constructed actual one-sided waterfall traces

- Proved uniform Lipschitz bounds for continuous finite affine selections on
  bounded monotone strips. Inset comparisons extend them through coherent
  reopening pinches without identifying permanently merged bank values.
- Constructed continuous planar extensions and proved their values on the
  closure are unique. A finite closed-piece argument retains an actual
  containing-face placement at every boundary point.
- Constructed one actual coherent waterfall before its development or
  calibration. Derived `cornerExtendedOutward_exists_waterfall_traces`: every
  strict physical strip has an 8-Lipschitz actual map and a constructed one-sided
  containing-face trace. The bound is independent of both meshes.
- Verification: cache retrieval followed by full `lake build` pass; **8,341
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  indexed documentation links (**1,151**) and whitespace pass. Parametrizing
  complete boundary curves and identifying their facing banks remain the next
  steps toward global strip separation; the full cap theorem remains open.

### 2026-11-11 — common-source position control in actual bank frames

- Derived exact developed-vector lengths and the normal-dependent two-sided
  metric bounds. Small angular calibration and small length expansion give
  arbitrarily small linear chart error, uniformly before both meshes.
- Constructed the bank-order data and linear-error control in the same actual
  calibrated frame, retaining its anchor and reference provenance.
- Passed quantitative errors through arbitrary continuous finite face-chart
  switches and inset source connectors across coherent reopening pinches.
  Obtained actual whole-strip injectivity and requested source-position control
  together in `exists_uniform_extended_waterfall_control`.
- Proved a positive sector-coordinate margin depending only on its fixed rays.
  Derived `exists_uniform_extended_waterfall_quadrants`: every actual developed
  strict strip stays in its sector quadrant relative to the common developed
  source, in the same calibration as the complete-bank order proofs.
- Added the finite-selection linear-test criterion for radial progress along a
  monotone path. Its geometric hypotheses still need to be instantiated for
  actual one-sided strip boundary traces; global strip separation remains open.
- Verification: cache retrieval followed by full `lake build` pass; **8,328
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  documentation links (**1,143**) and whitespace pass.

### 2026-11-11 — closed opposite-bank contacts at actual branch vertices

- Proved a generic equality criterion for ordered strictly increasing pieces:
  different pieces meet only at the common endpoint of adjacent pieces.
- Classified all closed contacts between opposite complete banks. Matched
  parameters are flat except possibly at their child endpoint; unmatched
  contacts occur only at a shared branch endpoint with the earlier subtree flat.
- Proved every such contact represents the same projected surface point and
  derived the corresponding uniform theorem for actual extended roof forests,
  with no bank-separation premise and tilt chosen before both meshes.
- Verification: cache retrieval followed by full `lake build` pass; **8,306
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  documentation links (**1,130**) and whitespace pass. Separation between
  different developed cut paths and strips remains open.

### 2026-11-11 — uniform injectivity on every whole actual waterfall strip

- Constructed the finite waterfall while preserving strict coordinate progress
  and tracking only pinches that later reopen. A new reopening pinch is inherited
  or lies at the inserted leaf; a permanently merged tail is left unconstrained.
- Proved exterior-bank persistence from actual geometry. Beyond its starting
  leaf a bank contact lies on the radial skirt; exact source-ray graphs are
  covered by actual geometric edges, and forward uniqueness forces the actual
  tail to remain there.
- Classified every reopening pinch of every constructed actual strip as the
  source or a geometric leaf, with no assumed safe-cut or pinch certificate.
  Derived regularity for these same constructed strips from their retained tails.
- Combined the classification with proved coherence at actual leaves to obtain
  `exists_uniform_extended_waterfall_full_injectivity`. Each actual map is
  injective across all positive-width components of its strip on the whole
  physical slab. The tilt is chosen before both meshes. Different strips still
  require global separation; the full cap theorem remains open.
- Verification: cache retrieval followed by full `lake build` pass; **8,299
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  documentation links (**1,127**) and whitespace pass.

### 2026-11-11 — compare strips across coherent reopening pinches

- Proved actual source-centered map continuity on the coherent domain and
  injectivity through coherent zero-width pinches, without positive width
  throughout the entire comparison slab.
- Distinguished reopening pinches from permanently merged banks: only the
  former need coherent developed values. Proved the local separator invariant
  from strict pretarget placement and permanent posttarget wall contacts.
- Derived strict coordinate progress of actual whole cut paths, sector walls,
  averaged connectors, and spliced insertion graphs. The connector result also
  covers targets on an exterior sector bank.
- Proved that every nonterminal geometric cut node on a sector bank is childless.
- Verification: cache retrieval followed by full `lake build` pass; **8,272
  unfolding / 7,243 pinned topology declarations**, standard axioms only;
  documentation links (**1,113**) and whitespace pass. Actual finite-waterfall
  pinch classification and global developed-strip separation remain open.

### 2026-11-11 — coherent developed values at actual leaf pinches

- Extended the actual projected map to its proved coherent domain, including
  slit endpoints where all developed face values agree. Proved continuity by
  finite closed-face gluing and coherence at the distinguished source.
- Proved that flat proper completed descendants create no displacement between
  any actual copies of an endpoint, without identifying those intrinsic copies.
- Proved geometric leaves are local radial minima of the finite closed cut
  network. A genuine outward segment cannot end at such a minimum; every proper
  completed subtree at a geometric leaf is therefore flat.
- Preserved every nonterminal geometric node in the actual roof mesh and proved
  it lies strictly inside the clip. Derived coherence at every actual geometric
  leaf from these facts, including arbitrary redundant flat completion branches.
- Verification: cache retrieval followed by full `lake build` pass; **8,242
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,104 indexed local links resolve.
- Open: classify all reopening strip pinches and apply their coherent values,
  prove separation between different developed strips/paths and no-wrap at the
  source, then transfer nonoverlap. The full cap theorem is not yet complete.

### 2026-11-11 — complete branching-bank order and regular noncrossing

- Constructed oriented cyclic intervals and internal subtree prefixes/suffixes.
  Discrete integration of vertex-region indicators pairs every selected seam's
  two banks in a contour excursion between copies of the same original vertex.
- Proved the exact partial displacement as a sum of whole sibling openings.
  Derived right/down jumps on the actual right bank and left/up jumps on the
  actual left bank, including arbitrary redundant flat completion branches.
- Proved coordinate progress along complete bank chains despite these jumps.
  Whole edges on different path levels retain left-or-above order; an interior
  contact is on the same edge, at the same parameter, with zero subtree curvature.
- Constructed the actual complete parent paths and derived a common sector for
  all their edges and curvature-carrying subtrees. Applied the uniform cap tilt
  threshold before both meshes in `ExtendedBankChainSeparation`.
- Verification: cache retrieval followed by full `lake build` pass; **8,224
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,097 indexed local links resolve.
- Open: branch-vertex contacts, comparisons between different cut paths and
  developed strips, pinches and the common source, and final original-face
  nonoverlap transfer. The full cap theorem is not yet complete.

### 2026-11-11 — actual regular waterfall maps and injectivity

- Proved strict-versus-closed separation for all five sectors and excluded
  geometric cuts from every sector from each waterfall strip interior.
- Chose a source sweep slab covering the original cap in every orthogonal frame,
  then a deeper roof clip, before auxiliary triangulation. Every actual tail tip
  continues beyond the slab. Constructed regular domains in the actual fine roof,
  including exclusion of isolated degenerate tips on the clip boundary.
- Constructed the actual projected developed map and proved continuity away
  from cut seams by finite closed-face gluing. Derived source-centered chart
  selection; no coherent strip map or compatible lift is assumed.
- Proved an inset-strip lemma for open interiors. Applied uniform direction
  control to obtain actual injectivity on every positive-width height slab of
  every constructed roof strip, with the tilt chosen before both meshes.
  This does not identify bank copies on a coincident projected tail.
- Verification: cache retrieval followed by full `lake build` pass; **8,160
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,084 indexed local links resolve.
- Open: compare components across possible strip pinches, account for sibling
  displacement along complete branching banks, prove global developed strip
  separation, and transfer nonoverlap to the original faces. The full cap
  theorem is not yet complete.

### 2026-11-11 — constructed finite geometric waterfall

- Constructed finite subdivisions by repeated insertion, proving exact coverage,
  retained separators, side-specific exterior-wall provenance, and pairwise
  disjoint strict cell interiors. Every separator avoids every cell interior.
- Proved the height-ordered finite waterfall construction for coalescing tails,
  allowing equal starting heights. All inserted graphs begin at the source
  and preserve their actual tails up to a common cutoff.
- Chose actual component sectors controlling positions and directions together,
  including rim-only components and isolated degenerate tips. Constructed their
  exact enclosing ray strips and enumerated actual leaves by height.
- Applied insertion to precisely the leaves active below the cutoff. Proved that
  every assigned cut-edge point there belongs to an actual leaf tail, hence to
  a separator, and stays out of every strict waterfall strip interior.
- Verification: cache retrieval followed by full `lake build` pass; **8,093
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,072 indexed local links resolve.
- Open: cutoff geometry, separation from other sectors, coherent developed maps
  on the nondegenerate strip regions, global developed strip separation, and
  nonoverlap transfer. Coincident projected tails do not identify bank copies.
  The full cap theorem is not yet complete.

### 2026-11-11 — actual tail coalescence and leaf avoidance

- Proved unique forward continuation in the complete geometric cut network.
  Finite closed-segment activity and increasing heights imply that covered
  monotone graphs merge permanently after meeting; this is a derived fact.
- Constructed exact whole-edge tail graphs in one common sector network,
  including distinct components. Their order is consistent on shared height
  slabs, and a distinct leaf avoids each already active tail.
- Proved that the strict strip insertion preserves a tail between coalescing
  neighbors up to a common cutoff. Completion below the leaf does not change
  this conclusion.
- Verification: cache retrieval followed by full `lake build` pass; **7,961
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,062 indexed local links resolve.
- Open: finite waterfall insertion, compatible surface lifts, global developed
  strip separation, and nonoverlap transfer. The full cap theorem remains open.

### 2026-11-11 — complete geometric forest and leaf sweep

- Constructed the finite parent forest of the complete original-and-skirt
  geometric cut network, before any auxiliary triangulation. Original rim
  roots continue to skirt tips; independent nonconstant components add leaves.
- Proved exact equality with the prescribed geometric cuts, including isolated
  degenerate tips. All geometric node positions are distinct; any node on an
  edge is an endpoint, and distinct edges meet only at shared endpoints.
- Preserved component labels along all parent orbits. Each component has one
  fixed five-sector direction bound, and each whole root path has an exact
  monotone height-graph representation preserving every segment.
- Proved a localized descendant-leaf lemma and applied it to the actual
  component sweep: every cut-edge point lies above a childless descendant
  whose path contains that edge. No auxiliary mesh or safe-path input is used.
- Verification: cache retrieval followed by full `lake build` pass; **7,868
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,046 indexed local links resolve.
- Still open: complete the waterfall insertion over this forest and compatible
  lifts, prove whole-bank and global strip separation, and transfer nonoverlap
  to original faces. The full cap theorem is not yet complete.

### 2026-11-11 — strict strip insertion and bounded domains

- Represented every whole edge of a genuine monotone polygonal path by a
  single monotone height graph, using exact affine pieces and splicing.
- Constructed strict internal connectors by averaging the two extremal feasible
  monotone connectors. They pass through the target without touching the old
  boundaries below it wherever the old strip has positive width.
- Spliced a connector to an existing geometric tail and split the old strip.
  Proved exact carrier coverage and that the substrip intersection is precisely
  the new graph, retaining boundary contacts and zero-width tails.
- Added bounded-height strip APIs and proved that connecting paths stay in the
  height slab. Derived actual roof-face injectivity on these bounded strips,
  without assuming any continuation of their maps outside the physical clip.
- Proved a descendant-leaf lemma for arbitrary ascending sweep coordinates.
  A radial skirt component meeting the original rim begins at that point;
  attached components correspond bijectively to original rim vertices.
- Verification: cache retrieval followed by full `lake build` pass; **7,806
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,036 indexed local links resolve.
- Still open: apply insertion to the complete geometric forest, construct
  compatible lifts, compare whole branching banks and all strips globally,
  and transfer nonoverlap to original faces. No full cap theorem is claimed.

### 2026-11-11 — injectivity inside coherent monotone strips

- Built coordinate-monotone height graphs, their envelopes, and clamped
  connectors. Closed strips admit increasing paths between comparable points;
  rectangles between mixed-coordinate endpoints lie entirely in the strip.
- Proved that local quantitative cone bounds imply global strip injectivity.
  Continuous selections among finitely many monotone coordinate functions
  preserve endpoint order, even with infinitely many branch switches.
- Reduced finite affine strip-map injectivity to four positive axis tests.
  Derived those tests from a positive numerical angular tolerance, independent
  of cap scale, face count, and orthogonal strip coordinates.
- Applied this to actual calibrated developed face maps. Proved
  `exists_uniform_extended_strip_injectivity` with tilt chosen before both
  meshes. Each candidate strip still needs a continuous map selecting those
  actual face placements; no covering partition is assumed to exist.
- Verification: cache retrieval followed by full `lake build` pass; **7,745
  project** and **7,243 pinned topology declarations** use only standard Lean
  axioms. No project warnings; all 1,025 indexed local links resolve.
- Still open: construct the waterfall partition and its compatible cut-surface
  lifts, compare whole branching banks, prove global strip separation, and
  transfer nonoverlap to original faces. The full cap theorem is not complete.

### 2026-11-11 — completed roof banks and redundant flat slits

- Derived five-sector bounds for every curvature-carrying descendant of the
  actual extended forest. Component labels propagate through complete fine
  parent edges; no direction condition is imposed on added flat branches.
- Summed all descendant vector differences to obtain actual parent-copy gaps,
  matched bank-point order, and immediate child-branch gap conservation.
- Proved that zero subtree curvature makes both bank positions and vectors
  coincide at every parameter. A flat contact still has a unique parameter.
- Proved `exists_uniform_extended_parent_bank_separation`, choosing tilt before
  both meshes. For every actual completed-parent pair, contact before the child
  endpoint has equal parameters and zero whole-subtree curvature.
- Verification: cache retrieval and full `lake build` pass; **7,628 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 1,012 indexed local documentation links resolve.
- Open: compare different edges along complete branching banks, construct the
  waterfall strip partition, prove global separation, and transfer nonoverlap
  to original faces. The full cap theorem is not yet proved.

### 2026-11-11 — preserved source slit and five-sector coordinates

- Proved that the actual roof refinement preserves the original source vertex,
  its leaf property, and its unique cut-surface copy. The two source-side bank
  endpoints therefore coincide in every actual development.
- Covered all projected directions by five acute sectors, including the forward
  gap where auxiliary roof vertices may occur. Constructed one calibrated frame
  with robust quadrant bounds for all five sectors, uniformly before both meshes.
- Preserved the signed whole-subtree bank rotation in these frames and derived
  coordinate order for each actual paired parent vector.
- Verification: cache retrieval and full `lake build` pass; **7,575 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 999 indexed local documentation links resolve.
- The waterfall partition and global separation remain open; the cap theorem
  is not yet complete.

### 2026-11-11 — uniform developed directions on the actual roof extension

- Constructed oriented completed-parent bank openings in one actual projection
  frame. Geometric transverse crossings determine the signed descendant-curvature
  phase; removing it leaves only the genuine spatial section bend.
- Proved that actual seam transitions are exact parent-counter changes.
  Constructed real unreduced section headings and telescoped all signed phases
  to the completed forest's bounded curvature potential. The heading error is
  at most twice tilt plus twice total curvature, without a mesh-size factor.
- Transferred one common rim-face alignment to every direction of every actual
  developed face and calibrated all directions to horizontal projection.
- Proved `exists_uniform_extended_direction_control`: for any positive error
  tolerance, one positive tilt threshold precedes the original cap mesh, source
  forest, clip height, and auxiliary refinement. The actual extended cut paths
  supply all required wedges; no auxiliary acute mesh or path certificate is
  assumed. The normal-height lower bound is derived from the same threshold.
- Verification: cache retrieval and full `lake build` pass; **7,507 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 988 local documentation links resolve.
- Still open: construct the waterfall strip partition, prove its developed
  regions and all gaps separate globally, and transfer nonoverlap to original
  faces. Direction control alone is not the cap nonoverlap theorem.

### 2026-11-11 — actual extended fine-seam paths have acute wedges

- Proved that original selected cut segments preserve their tree root at every
  geometric contact. A parent segment meets the old rim only at its parent.
  Each radial skirt component meets the convex old rim in at most one point,
  so distinct old tree roots cannot merge through a continuation.
- Labeled the complete original-cut and skirt network by its radial components.
  Contacts preserve these labels. Attached trees retain their original acute
  sector; independent radial components have wedge width zero.
- Proved finite-cover transfer: labels stay constant along whole meshed edges
  and paths, while whole-edge radial orientation preserves their component's
  direction wedge. Constant edges and flat subdivision vertices are allowed.
- Applied this to the constructed completed fine-seam forest. All paths
  starting at positive curvature have derived acute wedges; added zero-curvature
  branches impose no auxiliary acuteness requirement. The actual crossing
  potential is bounded by total curvature, uniformly in the extension mesh.
- Verification: cache retrieval and full `lake build` pass; **7,419 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 973 indexed local documentation links resolve.
- Developed heading transport for the completed extension, waterfall strips,
  global nonoverlap, and original-face transfer remain open. No full cap
  nonoverlap theorem is claimed.

### 2026-11-11 — whole-edge directions and flat-branch completion

- Strengthened the constructed fine-seam forest to whole-edge radial progress.
  Root paths meet each source-centered circle in at most one geometric point.
- Proved that original root paths retain their strict acute wedge after an
  entire outward radial continuation is appended, with no extra angle budget.
- Constructed a spanning completion at unused vertices, preserving all selected
  edges and nonroot parents. Halfplane progress needs no acute auxiliary mesh.
  Old geometric cuts are forward invariant; added outside branches carry zero
  descendant curvature.
- Applied exact subtree bank rotations to the completed disk, including zero
  apertures for added branches, in one projection-preserving frame. Additional
  cuts preserve rigid placements and nonoverlap; the prior development gives
  a completed development whose added seam cuts still match pointwise.
- Generalized signed crossing budgets to require acute root paths only at
  positive-curvature vertices. The actual fine-seam path wedges and their
  developed heading bounds still need to be derived; they are not assumptions
  of a claimed cap theorem.
- Proved that a whole outward segment meshed into a finite segment network
  inherits a positive multiple of a covering direction, preserving a common wedge.
- Verification: cache retrieval and full `lake build` pass; **7,375 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 963 local documentation links resolve.
- Still open: direction control for complete fine-seam paths, waterfall strips,
  global nonoverlap, and transfer to the original-edge unfolding. The full cap
  theorem remains incomplete.

### 2026-11-11 — constructed extended forest, cut disk, and development

- Proved strict source-distance growth along every original selected parent
  edge and local outward progress throughout the original cuts and radial skirt
  components, including parent endpoints and original rim junctions.
- Turned this local progress into actual fine-seam neighbors using a finite
  incident-star argument. Strict source-distance ascent selects a primal forest.
- Allowed unused vertices outside the geometric cuts as isolated parent roots;
  proved that every actual cut component still has exactly one boundary root.
- Constructed the extended roof's actual cut-disk homeomorphism. Every positive
  curvature vertex selects an outgoing seam, so the disk has a locally isometric
  facewise development, with overlap permitted. No cut-disk certificate is assumed.
- Extended direction control, waterfall strips, global nonoverlap, and transfer
  to an original-edge unfolding remain open; the full cap theorem is incomplete.
- Verification: `lake exe cache get` and full `lake build` pass; **7,243 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings; all 947 indexed local documentation links resolve.

### 2026-11-11 — actual extended cut seams leave flat interior copies

- Constructed the actual retained-seam set by removing fine whole edges contained
  in the original forest and selected skirt components. Every interior point of
  that geometric set belongs to an actual removed seam.
- Proved that every positive-curvature vertex is an intrinsic endpoint of a
  removed seam. The proof uses exact original-edge and component meshing and the
  actual intrinsic bank/rim correspondence.
- Proved that an interior vertex copy retains its entire original angle, and
  that every copy of a removed seam endpoint is a boundary copy. Applied this
  to the constructed cut pattern: all surviving interior copies have angle two pi.
- Generalized the disk-development route to cutting only positive-curvature
  vertices, allowing all other flat subdivision vertices to remain uncut.
- The constructed cut graph's boundary-rooted forest property and cut-disk
  homeomorphism, extended direction control, and global strip separation remain
  open. No disk certificate is claimed for this constructed cut pattern yet.
- Verification: full `lake build` passes; **7,177 project** and **7,243 pinned
  topology declarations** use only standard Lean axioms. No project warnings.
  All 936 local documentation links resolve.


### 2026-11-11 — selected extended geometric cuts cover all actual positive curvature

- Proved that each regular original cap point lies in a genuine chord and that
  every original support plane active there agrees along that chord. All active
  normal slopes are therefore collinear.
- Applied the checked normal-area identity: actual clip curvature within the
  original footprint occurs only at original cap vertices, for any conforming
  physical extension triangulation.
- Selected a finite skirt seed set before meshing from preceding roof corners
  and original rim corners outside the original footprint's interior. Combined
  original-vertex support with stability of curvature under line meshing.
- Proved that the selected original forest edges and constructed radial skirt
  components cover every positive-curvature vertex of the actual meshed clip.
  No post-meshing curvature or safe-cut certificate is assumed.
- The actual cut-seam selection, its boundary-rooted primal forest property,
  the extended flat cut disk/development, and global strip separation remain open.
  This is still not the full cap theorem.
- Verification: scoped cache check and full `lake build` pass; **7,158 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 929 local documentation links resolve.


### 2026-11-11 — derived input conformity and positive interior source height

- Proved that the supplied cap's projected input triangles are face-to-face
  conforming. Vertex contact follows from the actual vertex quotient; regular
  contact is an actual unique seam crossing and supplies its whole shared edge.
  No new conformity premise is added to geometric cap input.
- Proved that one positive roof height makes every interior roof height positive.
  Thus the nonflat case permits the actual internal forest source for compact
  radial continuations, rather than requiring a different positive-height source.
- The full extended cutting scheme and global strip-separation proof remain open.
- Verification: full `lake build` passes; **7,137 project** and **7,243 pinned
  topology declarations** use only standard Lean axioms. No project warnings.
  All 923 local documentation links resolve.


### 2026-11-11 — genuine geometric clips and finite curvature support under line meshing

- Identified the actual unpaired banks of a conforming physical clip with its
  horizontal outer rim, using intrinsic boundary preservation for disk maps.
- Translated the rim to zero and constructed the full geometric `ConvexCap`
  interface: actual spatial isometries, supporting original normals, injective
  convex projection, horizontal banks, and nonnegative corner heights.
- Applied the existing normal-area argument to all actual clip vertices. One
  numerical threshold controls their total intrinsic curvature before the
  original mesh, clip height, and any extra triangulation are supplied.
- Proved collinear incident slopes have zero intrinsic curvature, including
  one-plane and two-plane crease subdivisions. A regular point of a conforming
  triangle partition belongs to at most two faces.
- Exposed actual parents and support labels of line-constrained clip triangles.
  Applied the flatness criterion: arbitrary actual line meshing creates no
  positive curvature away from the preceding roof triangulation's corners.
- Sufficient skirt seed selection and its correspondence with the original cut
  forest, the extended cut disk and development, global strip separation, and
  the full cap theorem remain open. No acute auxiliary triangulation is asserted.
- Verification: scoped cache check and full `lake build` pass; **7,133 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 921 local documentation links resolve.


### 2026-11-10 — disjoint radial skirt components and exact segment meshing

- Constructed finite conforming physical roof triangulations respecting arbitrary
  prescribed genuine segments, including both endpoints, while preserving every
  original cap edge. Each spatially lifted segment is exactly a whole-edge union.
- Constructed outward continuations from arbitrary supplied skirt seeds to the
  outer convex rim. Their carriers avoid the original footprint's interior;
  any two are disjoint or nested.
- Merged nested tails by their outer rim labels into disjoint whole segment
  components. These components preserve the entire cut set and cover all seeds.
  Their actual spatial lifts are disjoint and mesh exactly into physical edges.
- This is not yet the complete cutting scheme: selection of sufficient curvature
  seeds, flatness at remaining new vertices, the retained-seam/forest correspondence,
  direction control of the extended development, and global strip separation remain open.
- Verification: scoped cache check and full `lake build` pass; **7,095 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 911 local documentation links resolve.


### 2026-11-10 — line-constrained roof triangulation preserves original cut geometry

- Triangulated compact chambers of arbitrary finite proper affine arrangements.
  Including all old triangle supporting lines gives exact disjoint-interior
  refinements subordinate to whole old parents, even with extra cut lines.
- Proved supporting-line contacts occur on actual whole fine edges or vertices.
  Respecting all three old supporting coordinates makes each old edge exactly a
  finite union of whole fine edges; finite exceptional vertex sets leave no gaps.
- Constructed conforming physical roof triangulations aligned to all original
  input face supporting lines. Exact old-edge coverage holds in projection and
  after actual spatial lifting, so original cut geometry is preserved.
- Extended cut-forest and retained-seam correspondence, cuts through extra roof
  vertices, global strip separation, and the full cap theorem remain open.
- Verification: scoped cache check and full `lake build` pass; **6,988 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 906 local documentation links resolve.


### 2026-11-10 — actual metric disk realization of the roof clip

- Proved that edge-compatible labels agree around every point of a conforming
  convex triangle partition. A punctured convex neighborhood is path connected;
  its finite closed triangle cover propagates the labels. Boundary and flat
  subdivision vertices are included.
- Applied this to actual physical intrinsic face copies. The constructed seam
  system has exactly the spatial roof's fibers, hence its metric realization
  is homeomorphic to the actual roof clip and the closed disk.
- Derived finite intrinsic route distances and an ordinary metric with the same
  topology and edistance. Projection is 1-Lipschitz; inverse projection has a
  bound depending only on original normal height, uniformly in the clip and mesh.
- Original-cut preservation, extension cuts through additional roof vertices,
  global strip separation, and the full cap theorem remain open.
- Verification: scoped cache check and full `lake build` pass; **6,913 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 899 local documentation links resolve.


### 2026-11-10 — conforming roof triangles and actual isometric seams

- Subdivided all boundaries of a finite triangle family in one straight
  embedded graph. Center fans use common global base labels, preserve exact
  coverage, and retain disjoint interiors.
- Proved exact face-to-face intersections: empty, a common vertex, or a whole
  common edge. This removes partial-edge contacts across support polygons.
- Constructed the complete canonical whole-edge seam system. Geometric
  separation proves unique partners, correct opposite-side opening, and
  nonoverlap of the identity planar development.
- Constructed physical clip seams separately: both spatial placements equal
  the actual roof point, so each full-edge identification is an isometry for
  the physical face metrics. The resulting spatial folding covers exactly
  the clipped roof; refinement retains the original support normals and tilt.
- The metric disk realization, preservation of original cuts, extension cuts
  through new vertices, global strip separation, and full cap theorem remain open.
- Verification: scoped cache check and full `lake build` pass; **6,876 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings. All 892 local documentation links resolve.


### 2026-11-10 — actual finite triangle partitions of the roof clips

- Constructed genuine center triangles from convex polygon rims. Proved exact
  coverage even when the supplied rim includes singleton cells, using dense
  regular rays and finite closedness. Refined overlapping rim segments into a
  straight embedded graph, giving pairwise disjoint triangle interiors.
- Constructed exact finite segment rims of compact finite affine halfplane
  intersections. Applied this to all actual clipped support polygons, which
  contain their original projected triangle and therefore have interior.
- Removed duplicate original support planes and proved the remaining active
  polygon interiors disjoint. Assembled a finite triangle partition covering
  the whole clipped footprint exactly.
- Pulled every projected triangle into its actual support-face coordinates.
  The resulting spatial triangles use the original rigid isometries, cover the
  clipped roof exactly, and retain the original unit normals and tilt bound.
- Strengthened straight-network subdivision to retain exact whole-edge coverage
  of every original segment. Existing theorem statements remain unchanged.
- Conforming edge pairings, preservation of original cuts, cuts through new
  roof vertices, global strip separation, and the full cap theorem remain open.
- Verification: scoped cache check and full `lake build` pass; **6,734 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  No project warnings in the full build.


### 2026-11-10 — compact polygonal roof clips from geometric cap input

- Derived the flat-or-positive-height dichotomy. The flat case has an injective
  uncut development; no positive-height assumption is added to cap input.
- For positive-height caps, proved that roof height is zero on the supplied rim,
  nonnegative on the original footprint, and strictly negative outside it.
- Constructed every finite lower clip with an explicit compact homothety bound.
  Its convex footprint contains the original footprint in its interior and has
  exactly the prescribed horizontal level on its frontier.
- Derived an exact finite support-plane segment cover of each clip rim, including
  degenerate cells. Constructed actual spatial clip disk homeomorphisms and
  packaged the geometric flat-or-compact-polygonal-clips alternative.
- Added interior triangle radial coordinates and actual convex-body frontier
  intersections from arbitrary interior centers for the triangulation step.
- Compatible extension triangulation and cuts through additional roof vertices,
  global bank and strip separation, and the full cap theorem remain open.
- Verification: scoped cache check and full `lake build` pass; **6,634 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  The committed modules are indexed; no project warnings.


### 2026-11-10 — origin leaf, exact branch balance, and the actual unbounded roof

- Proved that no nonroot parent step ends at the sector origin. An internal
  origin is a leaf, its descendant set is a singleton, and the actual two
  child-bank endpoints coincide. The threshold constructor now has a stronger
  companion retaining its origin's internality; existing statements are unchanged.
- Proved that immediate-child subtrees partition the proper descendants for
  arbitrary additive weights. Applied this to actual positions: a parent seam's
  child-end gap equals the sum of its immediate children's parent-end gaps.
- Constructed the unbounded roof as a closed graph homeomorphic to the plane,
  covered by closed convex active-support cells. It agrees pointwise with the
  supplied cap and is precisely the frontier of the convex intersection of the
  original supporting halfspaces.
- Constructed disjoint radial continuations of actual rim roots. They leave the
  original footprint and surface, lift continuously to the roof, and preserve
  their tree's sector direction.
- Generalized finite segment traces to arbitrary finite closed convex covers
  and reused this lemma for the original cap without changing its trace theorem.
  Constructed actual support-cell traces on the entire roof, with genuine face
  tangent secants. Every roof ray eventually stays in one original support cell
  and becomes exactly straight.
- Compatible extension triangulation and cuts through additional roof vertices,
  complete branching-bank separation, waterfall strips, and global nonoverlap
  remain open. The full cap theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **6,582 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **861 local documentation links**; no project warnings.


### 2026-11-10 — strict actual sector quadrants and branching paired-seam separation

- Constructed orthogonal acute-wedge frames with a common positive angular
  margin. One tilt threshold, before the entire mesh, puts every actual
  developed sector direction inside its strict fixed quadrant.
- Preserved the signed whole-subtree rotation in those frames and derived
  actual paired-bank vector order, strict for positive descendant curvature.
- Proved additive cancellation for actual contour positions and an exact gap
  identity: the parent-copy displacement sums every descendant paired-vector
  difference. All attached branches are counted by their actual seam labels.
- Ordered every matched actual bank point, including endpoints and straight
  extensions beyond the parent rim. Two banks of the same seam can intersect
  only at matched parameters. Before the child endpoint, contact forces zero
  whole-subtree curvature; positive curvature separates their interiors.
- Packaged this individual paired-seam separation under a threshold depending
  only on the acute margin. No safe-bank certificate is assumed.
- Different-seam and complete branching-path separation, strip assembly, and
  global nonoverlap remain open. The full cap theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **6,478 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **850 local documentation links**; no project warnings.


### 2026-11-10 — common-frame control of every actual original-face direction

- Proved a general oriented planar comparison: one reference-ray alignment
  controls any other direction by the difference of their reference angles.
  Actual linear maps extend this to collinear directions and two error budgets.
- Derived a uniform local face-direction angle-error threshold before the entire
  mesh. Every rigid development has the same actual local angle error.
- Transferred the checked section alignment from one direction to every direction
  on each actual original face, compared against the same original rim face.
- Constructed one global rotation calibrating the actual common developed frame
  against original projection. Every actual direction has error at most
  `2 * tilt + 2 * totalCurvature + 3 * localError` in that same global frame.
- Proved a positive numerical threshold depending only on the acute margin and
  requested error, before the complete cap mesh. It constructs the actual forest
  and controls every direction of every actual developed original face.
- Strict actual bank wedges, branching-bank separation, waterfall strip assembly,
  and global nonoverlap remain open. The full cap theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **6,350 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **830 local documentation links**; no project warnings.


### 2026-11-10 — uniform actual section headings via the crossing potential

- Constructed positively oriented horizontal section frames, with every original
  vertex strictly off-axis and actual interior samples strictly ordered.
- Proved that a nonvertex projected seam point has one original seam name.
  Between adjacent interior samples, only the actual transition seam can meet
  the section; repeated original face labels contain no original seam.
- Identified geometric segment-ray counter changes with actual original-segment
  intersections and their exact oriented signs. Physical parent counters are
  the previously bounded actual forest-ray counters.
- Proved that every actual local phase is precisely the weighted potential
  change. All other parent counters stay constant. The actual whole-trace
  signed phase sum telescopes and has absolute value at most twice total curvature.
- Proved real unreduced heading change at most `2 * tilt + 2 * totalCurvature`
  on every regular trace. Every original face has such an aligned section
  direction from the same rim face. A positive forest-and-heading threshold
  is quantified before the complete input mesh.
- Calibration of all original face directions against projection, bank and
  branching-strip separation, and global nonoverlap remain open. The full cap
  theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **6,329 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **825 local documentation links**; no project warnings.


### 2026-11-10 — constructed signed-phase transport along actual section traces

- Propagated positive original projection orientation around the actual full
  bank contour. Each outgoing bank has its actual original face on the left.
- Identified actual geometric transverse crossing signs at parent-bank
  entrances and exits. Each removed original seam has its unique selected
  parent, so its actual signed curvature phase is determined geometrically.
- Constructed actual local phases at every regular original-face trace
  transition. Retained seams contribute zero; cut seams contribute the signed
  whole-subtree curvature, with residual turn bounded by the spatial bend.
- Constructed real unreduced headings along entire actual traces. Heading
  change minus the signed phase sum has absolute value at most twice the tilt.
- Constructed genuine face-interior sample points and proved every whole open
  regular section piece interior. Every original seam avoids every such piece.
- Defined the actual weighted forest-ray potential and proved telescoped
  query changes bounded by twice total curvature, independently of mesh size.
- The remaining heading obligation is identifying actual trace phases with
  those potential changes. Full uniform headings, branching-bank separation,
  and global nonoverlap remain open; the cap theorem is still incomplete.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **6,268 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. Checked **811 local documentation links**; no project warnings.


### 2026-11-10 — actual retained and signed parent-bank section transitions

- Derived strict opposite-side opening in actual cap projection. The actual
  projected-to-developed affine charts have the same nonzero determinant sign
  across the connected retained mesh.
- Identified actual spatial and developed seam chords. Every nonconstant
  vertex-avoiding section transition has an actual transverse original seam.
  Actual retained hinge opening contracts section turns.
- Chose a complete actual boundary contour positive in cap projection. Its
  common developed frame preserves projected orientation on all original faces.
- Exposed the prescribed entrance and exit data in subtree rotation proofs,
  preserving existing theorem statements. Actual parent-bank entrances run
  parent to child; exits run child to parent.
- Identified the actual outward parent-vector rotation, positively by all
  descendant curvature in that common frame. Removing this actual phase gives
  a section turn at most the genuine spatial bend, for all transverse directions.
- Matching these phases to trace crossing counters, composing uniform headings,
  branching-bank separation, and global nonoverlap remain open. The full cap
  theorem is still incomplete.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **6,180 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. Checked **797 local documentation links**; no project warnings.


### 2026-11-10 — constructed regular sections from a common rim face

- Proved that an acute positive-span wedge supplies a monotone ambient
  coordinate in every orthogonal frame. The actual signed forest-crossing
  curvature budget therefore works for arbitrary ray origins and directions.
- Constructed strictly increasing finite original-face partitions from the
  actual convex projected-triangle cover. Each whole closed piece has its
  original face label; the roof agrees with that face's supporting plane.
- Defined actual spatial and rigidly developed face vectors over horizontal
  directions. Identified exact section secants and transferred the twice-tilt
  spatial turn bound to the constructed sequence of actual face tangents.
- Constructed a midpoint of an actual original rim bank. Its original face is
  unique and it is distinct from every original projected corner. All sections
  from it start in that same original face.
- Used the checked finite affine-arrangement density theorem to choose an
  interior target in every original face whose complete anchor line avoids
  all original vertices. The resulting actual trace has the required first
  and last face labels; every nontrivial transition crosses an actual original
  seam, by exact metric classes and injective projection.
- Proved the local angular reverse triangle inequality and a hinge-turn bound
  from matching seam angles and the planar same-halfplane condition. Instantiating
  this condition across the actual face trace remains to be done.
- Retained-seam and cut-seam developed direction transitions, uniform global
  headings, bank noncrossing, and global nonoverlap remain open. The full cap
  theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **6,102 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **782 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — actual roof-section turning and signed forest-crossing budgets

- Bounded the entire supporting-plane roof's height variation by the actual
  normal slopes. Every vertical section is concave; ordered secant slopes
  and their real arctangent inclinations are antitone.
- Identified those inclinations with genuine spatial secant angles. Total
  actual spatial turning along every finite section partition is at most twice
  the normal tilt. Positive thresholds are quantified before the whole mesh.
- Proved exact affine level-intersection parameters and signed horizontal-ray
  crossing bounds for chains monotone in either ambient coordinate. A half-open
  endpoint convention handles degeneracies without identifying counts with
  proper crossings or asserting geometric noncrossing.
- Derived the required coordinate monotonicity for all three actual sector
  root-path labels. Each path's signed crossing count has magnitude at most one.
- Enumerated each original nonroot ancestor exactly once along its first-root
  path. Regrouped nested subtree weights over those paths before taking absolute
  values. The actual curvature-weighted parent-edge crossing sum is at most
  total cap curvature, independent of mesh size and tree depth.
- Actual developed section transitions and rim calibration remain open, as do
  uniform prefix turns, bank noncrossing, and global nonoverlap. These estimates
  do not complete the cap theorem.
- Verification: scoped cache check and full `lake build` pass; **5,989 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **770 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — actual rigid openings around branching descendant subtrees

- Enumerated the actual banks and vertex copies along a complete boundary
  contour. Weighted cut-copy angles regroup exactly to original vertex angles.
- Proved that a nonroot descendant subtree has one selected original-edge exit
  and exactly two actual bank exits. Membership conservation orients them as
  one entrance and one exit of the actual contour.
- Counted actual cut-copy incidence and derived aggregate boundary turn
  pi minus descendant curvature, including arbitrary branches and flat vertices.
  No Euler identity or planar separation certificate is assumed.
- Propagated developed orientation through the actual hinge and endpoint
  pairings. Generalized link headings to a prescribed common orthogonal frame;
  existing link-heading theorems reuse these proofs with unchanged statements.
- Proved actual boundary-step rotations. Multiplying rotations over the subtree
  cancels every internal direction, leaving the actual two original parent
  banks. Their equal lengths upgrade the normalized identity to a rigid rotation
  by all descendant curvatures. In a convex cap this is between zero and total
  curvature, and at most pi gives the exact genuine bank aperture.
- Prefix-turn bounds, branching-bank noncrossing, and global strip separation
  remain open. The full cap theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **5,919 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **760 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — actual developed headings and rigid bank openings at forest leaves

- Defined actual planar developed germ rays and their genuine corner angles.
  The opposite-side hinge condition separates adjacent corner cones, giving a
  common orientation and exact unreduced real link headings even when distant
  faces of the development overlap.
- Derived terminal bank rotations from complete retained corner angles.
  Nonnegative defects at most pi give exact genuine bank aperture; zero defect
  gives coincident unit directions and allows boundary contact.
- Proved that opening one original cyclic-link pair preserves the complete
  corner star in one actual cut vertex copy. Its terminal germs are exactly
  the original opened pair. Developed edge lengths match original spatial
  lengths, including banks belonging to different cut copies.
- At a childless internal vertex of the constructed source-centered forest,
  derived unique cut-seam incidence from the actual selected graph. Its two
  actual equal-length bank vectors therefore differ by a rigid rotation of
  precisely its actual vertex curvature. No opening angle certificate is input.
- Minimum potential supplies a childless nonroot whenever nonroots exist.
  Branching-bank openings, uniform prefix turns, and global nonoverlap remain
  unproved; this milestone does not complete the cap theorem.
- Verification: scoped cache check and full `lake build` pass; **5,789 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **737 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — constructed source-centered forest and regional angle balance

- Proved relative angle balance for every actual union of original faces.
  Complete stars contribute interior curvature or nonnegative rim excess;
  the aggregate excess on partial stars is bounded in absolute value by total
  curvature. Relating these stars to arbitrary path-prefix closures remains open.
- Constructed three algebraic near-quadrants covering the backward halfplane,
  with disjoint interiors, stable closed cones, and acute actual boundary rays.
  A direct inner-product perturbation bound gives one positive parameter for
  all triangles with the requested acute margin, before any mesh is supplied.
- Chose the source at an internal horizontal extremum. Constructed actual
  original-seam parent choices preserving the source-centered sector label,
  and hence an actual boundary-rooted forest. Closed-sector banks and flat
  vertices are allowed. The forward gap contains no internal vertices.
- Proved that root paths stay in their sectors and are globally radially
  monotone, including whole edges. Constructed their actual cut disk and a
  locally isometric development, with overlap still allowed.
- Combined the forest construction and any requested total-curvature budget
  under a single positive tilt threshold quantified before the complete mesh.
- Added horizontal orthogonal reframing of actual cap data, preserving intrinsic
  triangles, seams, height, supporting geometry, and normal-tilt bounds.
- Uniform prefix-turn estimates, actual developed-bank opening identities,
  branching-bank separation, and global strip assembly remain unproved.
  The full cap theorem is still incomplete.
- Verification: scoped cache check and full `lake build` pass; **5,730 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **723 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — nonnegative rim excess and uniform bounds for rim portions

- Constructed genuine spatial and projected interval-link ray sequences.
  Disjoint actual corner cones force consistent orientation. A ray chain in
  the supporting closed halfplane has exact endpoint angle, including straight
  outer boundary rays; spherical angular length bounds the spatial endpoint angle.
- Identified terminal unpaired germs with actual horizontal rim banks. Derived
  that every original rim vertex's intrinsic angle is at least its projected
  angle, without strict corners or an assumed planar polygon certificate.
- The nonnegative rim angle excesses sum exactly to total interior curvature.
  Every finite rim portion, and every selected finite set of interior curvature
  contributions, is therefore bounded by the complete curvature budget.
- A single positive tilt threshold controls every rim portion across all meshes.
  Truncated subregions, uniform prefix turns, source-centered forests, developed
  branching banks, and global nonoverlap remain open.
- Verification: scoped cache check and full `lake build` pass; **5,578 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **707 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — actual spherical Gauss identity and uniform total curvature

- Extended the exact lune calculation to every nonzero spatial vector pair,
  including parallel and opposite directions. Antipodal symmetry halves each
  sign-change measure within any hemisphere.
- Proved the discrete spherical Crofton integral and connected it to actual
  cyclic spatial germ directions and original triangle corner angles.
- Derived the geometric zero-or-two crossing count from actual supporting
  planes, closed local face coverage, and disjoint projected face cones.
  A supported planar convex cone has at most two boundary ray directions;
  this handles repeated normals and flat vertices without strict convexity.
- Proved that intrinsic angular defect at every interior cap vertex equals
  the solid angle of its complete actual outward normal cone. Derived
  nonnegative defects and the conservative bound
  `81 * (sqrt (1 - c²) / c)² * pi` for normal heights at least `c ≥ 3/4`.
- Chose a positive total-curvature threshold before even the face type and
  triangle complex. The same numerical threshold works across all input meshes.
- Uniform prefix turns, source-centered forest placement, actual developed
  branching banks, and global nonoverlap remain open. This is not the full
  cap theorem. No existing theorem statements changed; no external code copied.
- Verification: scoped cache check and full `lake build` pass; **5,534 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **654 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — volume-induced solid angle and exact spherical lunes

- Defined solid angle from Mathlib's `volume.toSphere`, transported to ambient
  space. Proved the conical-volume formula, full-sphere measure `4π`, orthogonal
  invariance, and nullity of great circles and linear hyperplanes.
- Proved the exact uniform azimuth law by almost-equivariance under vertical
  rotations and Haar uniqueness. Added canonical angular length on `Real.Angle`.
  A spherical lune of aperture `θ ∈ [0, π]` has solid angle exactly `2θ`.
- Constructed a 3-Lipschitz conical parametrization over bounded slope polygons.
  It bounds solid normal angle by 81 times planar area; the constant is a
  conservative bound, not an asserted equality of surface-area formulas.
- Derived an arbitrarily small summed solid-angle budget from a positive tilt
  threshold chosen before the cap, independent of its vertex count.
- This provides a direct volume-based route to the missing intrinsic-curvature
  identity. That identity, uniform prefix-turn control, and global nonoverlap
  remain unproved. No external proof code was copied.
- Verification: scoped cache check and full `lake build` pass; **5,454 project**
  and **7,243 pinned topology declarations** use only standard Lean axioms.
  Checked **679 local documentation links**; no project warnings or temporary worktrees.

### 2026-11-10 — actual projected links and cap angle-defect balance

- Proved that a cyclic fan of genuine disjoint direction cones makes exactly
  one full turn. Derived consistent orientation from actual cone separation;
  reflection handles either orientation. No convex polygon or winding-number
  certificate is supplied as input.
- Proved that disjoint triangle interiors give disjoint open corner direction
  cones. Identified these cones and their genuine angles in the cap's actual
  cyclic germ order, including seam endpoint reversals.
- Derived projected interior total angle `2π` from this geometry. The cap's
  total interior intrinsic defect therefore equals its actual boundary angle
  excess, removing the previously explicit projected-flatness hypothesis.
- The spherical Gauss-image curvature identity, uniform prefix-turn bound,
  source-centered forest, and global developed-face nonoverlap remain open.
- Verification: full `lake build` and standard-axiom audit pass for
  **5,368 project** and **7,243 pinned topology declarations**; no project
  warnings. Checked **667 local documentation links**. No temporary worktrees.

### 2026-11-10 — spherical normal-cone geometry and area comparison

- Proved exact radial/angular distance decomposition and nonexpansiveness of
  normalization outside the unit ball. The inverse gnomonic map is therefore
  nonexpansive for chord distance.
- Used Mathlib's normalized Euclidean Hausdorff measure to prove that each
  actual spherical normal polygon has area at most its planar slope polygon.
  The full spherical normal-image area has a positive uniform tilt threshold
  for every requested positive budget, independent of vertex count.
- Proved that every spherical image normal supports the entire actual cap.
  Conversely, at an interior vertex, separation and local face incidence show
  that every upward supporting unit normal lies in this image. Repeated normals
  and degenerate normal polygons are allowed.
- Specified the next missing local equality: intrinsic angular defect equals
  spherical normal-image area. This curvature identity, uniform prefix-turn
  control, and global cap nonoverlap remain unproved.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **5,334 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. Checked **662 local documentation links**; no project warnings
  or temporary worktrees.

### 2026-11-10 — original-edge cap forests and normal-image packing

- Constructed an actual boundary-rooted forest of original seams with canonical
  acute-wedge paths to the rim. Each whole path is radially monotone from every
  earlier point. The construction uses a fixed wedge; the source-centered sector
  construction needed for nonoverlap remains open.
- Proved that these selected cuts give an intrinsic disk and put every vertex
  copy on its boundary. Constructed its locally isometric development, unique
  after fixing one original face, with overlap permitted.
- Handled caps with no interior vertices by proving they are flat and have an
  injective, nonoverlapping uncut development.
- Constructed supporting-slope normal polygons from the actual incident faces.
  Proved disjoint interiors and a common tilt-controlled disk, hence a total
  planar area bound independent of vertex count. Any positive area budget has
  a positive uniform tilt threshold. Gnomonic coordinates recover face normals.
- The intrinsic-curvature identity, uniform prefix-turn bounds, and global
  nonoverlap proof remain unproved; this is not the full cap theorem.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **5,311 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. No project warnings or temporary worktrees.

### 2026-11-10 — acute-wedge progress and intrinsic cap bounds

- Constructed the actual projected triangle cover, preserving corner incidence
  and proving seam agreement and disjoint interiors. A uniform positive tilt
  threshold preserves half the input acute margin.
- Proved uniform intrinsic projection bounds by passing local face estimates
  across the convex projected cover. The inverse bound is `1/c` for minimum
  normal height `c`; this concerns the route metric, not only ambient chords.
- Derived a concave lower-envelope roof from the actual supporting planes,
  with exact agreement on every cap face. Its global extension is not asserted
  to be vertex-free. Proved relative original/projected angle-defect balance;
  projected-link flatness remains an explicit hypothesis of its curvature corollary.
- Proved outgoing original-edge progress in acute triangles and finite planar
  meshes, then for actual projected cap vertex classes. A small shear chosen
  uniformly from the acute margin supplies a wedge strictly narrower than pi/2.
  Chains in this wedge are angle-monotone and radially monotone.
- Constructed rooted forests from increasing parents and from local progress
  preserving a sector label. Selected edges retain their original names;
  proved that distinct nonroots cannot select the same edge. The cap's global
  near-quadrant assignment and cut-seam construction remain open.
- Constructed opened banks from matched lengths and nonnegative cumulative
  opening angles. Proved both equal-abscissa and equal-radius order in a common
  quadrant, with contacts and finite endpoints included. The general Theorem 9
  and the geometric branching-curvature identification are not claimed.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **5,171 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. No project warnings or temporary worktrees.

### 2026-11-10 — first convex-cap proof foundations

- Specified O’Rourke’s cap theorem and its remaining obligations in
  `docs/CAP_THEOREM.md`; the full near-flat edge theorem remains unproved.
- Defined geometric convex caps without assumed cuts, forest, disk topology,
  development, or nonoverlap. Derived disk topology from convex injective
  projection. Constructed the uncut injective development of every flat cap.
- Proved exact horizontal projection and tangent-plane contraction estimates,
  small vertical motion, and a projection-angle tolerance uniform over all
  unit tangent directions. Compact-annulus continuity gives a rigorous positive
  tilt threshold without relying on an approximate numerical constant.
- Added finite chains with actual positions inside closed edges. Proved the
  outward scalar-product criterion, acute-wedge radial monotonicity, extension
  to arbitrary interior anchors, and uniqueness of actual circle intersections.
  Examples include a staircase and a counterexample to endpoint-only tests.
- Proved whole-chain paired-bank order from matched edge lengths and ordered
  headings in a common open quadrant. This is a stronger conditional hypothesis
  suitable for acute slack, not a claimed proof of the paper’s general Theorem 9.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **4,942 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. No project warnings or temporary worktrees.

### 2026-11-10 — polygonal cut forests and flat-disk development

- Constructed unique rigid transition germs for arbitrary open Euclidean metric
  charts. Proved local constancy and the exact cocycle laws. Their discrete
  frame bundle is a covering; Mathlib's simply connected lifting theorem
  continues a chosen frame to a global planar local isometry.
- Applied continuation to the open interior of a metric disk. Convex patch
  rigidity gives one whole-face motion; retained edge agreement extends across
  all endpoints. Local injectivity forces strict opposite-side opening.
- Proved that a spatially folded triangular disk with total angle `2π` at each
  interior vertex admits a development, allowing overlap and arbitrary boundary
  angles. Prescribing any one face motion gives exactly one development. The
  public theorem retains actual local isometry at every interior point, including
  flat vertices, so no interior branching is hidden by the facewise interface.
- Added refined polygonal cut presentations, their nonexpanding original-surface
  projection, and an actual finite embedded graph of new cut arcs with rigid
  parent-face coordinates. Derived its acyclicity from the rooted-forest test.
  The disk criterion and unique normalized flat development apply directly.
- A presentation supplies a conforming refinement certificate. Automatically
  constructing such a refinement from arbitrary polygonal input arcs remains a
  separate construction problem; no such existence conclusion is assumed here.
- Verification: Mathlib covering-space cache check and full `lake build` pass;
  **4,748 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. All **595 local documentation links** resolve, there are no new
  project warnings, and no temporary worktrees remain.

### 2026-11-10 — normalized uniqueness and refined cut presentations

- Proved that two endpoint distances and a strict side determine a planar
  point. A joined edge and outward opening therefore determine the next face
  motion uniquely. Equality propagates across either seam direction and every
  retained dual path: fixing one face determines the entire development.
  No disk or nonoverlap hypothesis is required.
- Defined the actual nonexpanding projection of a refined cut surface to the
  original uncut realization. Compatible further refinements preserve the cut
  metric and commute with this projection. Projected boundary banks are a
  finite union of actual straight spatial segments.
- Transported the convex-sphere cut-tree iff disk theorem to refined cuts,
  including cuts through original face interiors. Automatic insertion of an
  arbitrary polygonal cut and general flat-disk existence remain unchecked.
- Verification: full `lake build` and standard-axiom audit pass; no new project
  warnings. The README remains a short entry point; detailed APIs are indexed
  in `docs/REFERENCE.md`.

### 2026-11-10 — conforming metric refinements

- Defined finite geometric subdivisions by actual child placements and covers,
  with conformity expressed entirely as declared seam chains. Derived the
  intrinsic isometry, including infinite distances across disconnected cuts.
- Constructed identity and composite refinements, and the two-triangle split
  at any strict interior point of an edge. Its glued realization is isometric
  to the original Euclidean triangle and has an outward nonoverlapping development.
- Transported spatial foldings, surface images, convex hulls, embedding, and
  convex-boundary certificates. Whole-ball Euclidean regularity is invariant.
- Restricted arbitrary developments to refinements. Derived strict edge opening
  from seam conformity and geometric disjointness. Proved nonoverlap is preserved
  in both directions, with overlap allowed throughout the development API.
- Verification: scoped Mathlib cache check and full `lake build` pass;
  **4,534 project** and **7,243 pinned topology declarations** use only standard
  Lean axioms. No new project warnings; local documentation links resolve.
- Numerical curvature transport, automatic polygonal-cut insertion, and general
  flat-disk development existence remain separate unchecked goals.

### 2026-11-10 — concrete tetrahedron benchmark

- Constructed all four planar triangles, rigid spatial face placements, and
  six full-edge pairings for the coordinate tetrahedron. Added a reusable
  endpoint-and-length edge-identification constructor.
- Proved the paired-edge realization embeds in space and is exactly the
  boundary of its full-dimensional convex hull. Supporting affine coordinates
  identify the four facets and the actual four metric vertex classes.
- Instantiated the full source-unfolding API at a concrete crease midpoint,
  with proved nonextremality and nonoverlap of the resulting polygonal layout.
- Proved that cutting the three edges incident to vertex zero produces an
  actual disk. The uncut sphere and the four completely separated faces are
  proved not to be disks. No cut-tree or convex-boundary certificate is assumed.
- Verification: cache check and full `lake build` pass; **4,352 project** and
  **7,243 pinned topology declarations** use only standard Lean axioms.
  All **558 local documentation links** resolve, with no new project warnings.

### 2026-11-09 — full relative disk forest criterion and canonical sphere iff

- Extended the outside-root tree equivalence to named multigraphs. Loops and
  parallel edges are retained. A tree quotient identifying exactly the roots
  forces acyclicity, one root per component, and no rootless components.
- Defined the actual relative cut graph with one edge per newly removed seam.
  Old boundary edges are excluded; unused original boundary vertices form
  harmless rooted singleton components, including when no seams are removed.
- Proved opposite-bank reachability for relative forest cuts. Boundary-component
  labels descend through restored vertex classes; old banks keep every root
  label equal. Constructed the further cut's actual disk homeomorphism and
  proved exact bank-to-circle correspondence.
- Constructed the actual embedded cut graph after collapsing the old disk
  boundary. Proved separation of all open seam arcs, exact carrier equality,
  and exact vertex fibers. Contractibility of that carrier gives the necessity
  direction. `cutDisk_iff_rootedForest` is the full relative disk criterion.
  Added explicit cycle, multiple-root, missing-root, and empty-cut consequences.
- Applied the same graph construction without a boundary collapse to convex
  spheres. `cutDisk_iff_cutSeamGraph_tree` now uses the same canonical primal
  multigraph in both directions. Arbitrary graph-subdivision comparisons and
  general regular neighborhoods remain independent later tasks.
- Verification: `lake exe cache get` finds no missing files; full `lake build`
  passes and audits **4,208 unfolding** and **7,243 pinned planar-topology
  declarations**, with only standard Lean axioms. All **547 local documentation
  links** resolve; no new project warnings occur.

### 2026-11-09 — disk cuts and collapse of the original boundary

- Constructed the continuous quotient sending a closed boundary to infinity
  in its complement's one-point compactification. Its fibers are exactly equal
  points or pairs of boundary points. For the standard disk, Mathlib's open-ball
  and one-point-sphere homeomorphisms identify the target with a sphere.
- Proved that old banks persist under further cuts. Restoring cuts and collapsing
  the original disk boundary therefore gives an actual boundary quotient onto
  a sphere; a further disk cut has contractible collapsed bank image.
- Constructed planar embeddings and open planar boundary-complement models for
  arbitrary further cuts of a disk. Proved `cutDisk_iff_boundaryGraph_connected`:
  connectedness of the actual bank graph is necessary and sufficient, and the
  sufficient direction constructs the disk homeomorphism. Empty cuts are covered.
- Verification: full `lake build` passes and audits **4,110 unfolding** and
  **7,243 pinned planar-topology declarations**, using only standard axioms.
- The remaining forest step is to identify this actual bank criterion with
  one original-boundary root in each component of the new cut graph.

### 2026-11-09 — constructed cut disks from primal cut trees

- Defined the canonical primal cut multigraph with one edge per actual cut
  seam and exactly its incident original vertex classes. On closed complexes
  its banks are in bijection with cut seams and side labels.
- Proved that forest cuts put opposite banks in the same actual boundary
  component. Descended boundary-component labels through the original germ
  chains and vertex quotient. A connected primal forest has connected bank
  boundary, and one closed bank order visits every end.
- Identified that order's exact carrier with the whole bank boundary. In the
  constructed planar embedding of a convex-sphere cut, it is one Jordan curve.
- Proved the generic compact planar classification: nonempty interior and
  Jordan frontier imply a closed-disk homeomorphism. Half-plane charts and an
  open planar model of the boundary complement identify the exact frontier.
- Constructed that complement model from the original sphere by stereographic
  projection. `exists_cutDisk_of_tree` and `cutDiskHomeomorphOfTree` now build
  the actual cut disk from connectedness and acyclicity of the primal graph.
  Exact correspondence of banks with the disk circle is proved. No disk
  presentation, development, nonoverlap, Euler formula, or surface classification
  is assumed in this converse.
- The relative disk forest equivalence and comparison with arbitrary spatial
  graph subdivisions remain open. The canonical converse itself is complete.
- Verification: full `lake build` passes and audits **4,068 unfolding** and
  **7,243 pinned planar-topology declarations**, with only standard axioms.
  All **521 local documentation links** resolve, with no new project warnings.

### 2026-11-09 — actual bank cycles and planar cut embeddings

- Constructed bank-end and boundary-vertex types from actual unpaired germs.
  Exactly two ends occur at each boundary vertex. The other-end pairing and
  exchange of a bank's ends are fixed-point-free involutions.
- Derived closed bank orders and proved that no bank or boundary vertex
  repeats within a cycle. Constructed the actual finite embedded boundary
  multigraph, with original affine edge maps and exact bank-set carrier.
- Constructed a multigraph cycle through every bank; no bank is a bridge.
  Loops and parallel edges remain supported for abstract triangle complexes.
- Added generic vertex/edge-map and embedded-graph transport bridges. Actual
  nonloop embedded cycles satisfy the pinned plane-drawing API and are Jordan
  curves. A cycle mapped to a forest must repeat the image of its distinguished
  edge on its alternate path; this supplies the coming cut-tree bridge step.
- Constructed a closed planar embedding of every nontrivial cut of a convex
  sphere: push its banks inward, omit a cut-graph point, and stereographically
  project. Every bank lies on an actual Jordan cycle in that embedding.
- The connected/single-boundary-cycle step for tree cuts, sphere tree-to-disk
  converse, and full disk forest criterion remain open. Multiple boundary
  cycles are allowed in the current results.
- Verification: full `lake build` passes and audits **3,994 unfolding** and
  **7,243 pinned planar-topology declarations**, with only standard axioms.
  All **501 local documentation links** resolve.

### 2026-11-09 — actual boundary atlases and global inward embeddings

- Identified both outer fan banks exactly with the boundary line, preserving
  the original ray radii even when the planar development overlaps.
- Proved that no continuous injective open planar patch can hit a nonvertex
  bank. Transferred planar openness to product coordinates and identified
  the actual bank set under every local half-plane homeomorphism. Perfect
  edges and open line subsets remove all finite vertex exceptions.
- Constructed centered affine edge coordinates and combined nonvertex edge
  charts with the actual vertex fan charts into a genuine bank-boundary atlas.
- Constructed compactly supported injective inward pushes, their arbitrary
  rescalings, and extension through an open chart by the identity. Finite
  composition moves an entire compact boundary inward, without collisions.
- Applied this to every spatially folded finite triangle complex, for every
  retained seam set. The whole cut surface embeds into its bank complement
  and into the original surface off the cut graph. These are constructed
  embeddings; neither disk topology nor nonoverlap is a premise.
- Extended arbitrary sphere homeomorphisms radially to closed balls, with
  exact boundary agreement and radius preservation, for disk-boundary matching.
- The single-boundary-cycle argument for tree cuts, the sphere tree-to-disk
  converse, and the full disk forest equivalence remain open. The inward
  embedding alone does not prove a cut disk.
- Verification: full `lake build` passes and audits **3,912 unfolding** and
  **7,243 pinned planar-topology declarations**, with only standard axioms.
  All **484 local documentation links** resolve. Removed temporary research
  clones after preserving their refs, commits, and proof patches as ignored
  bundles and review evidence; no temporary worktrees remain.

### 2026-11-09 — half-plane neighborhoods at boundary vertices

- Constructed bounded linear changes between convex sectors that preserve the
  parameters on both boundary rays. A finite uniform Lipschitz bound descends
  these maps to actual glued angular fans, with explicit continuous inverses.
- Compressed arbitrary interval fans to a convex quarter-sector and opened
  the quadrant by a piecewise linear homeomorphism. Every such fan is a
  half-plane, regardless of total angle or overlapping developed interiors.
- Transferred the model to actual interval-link tangent fans and, for spatial
  foldings, whole intrinsic boundary-vertex balls. Proved the charts send the
  actual vertex to the boundary-line origin.
- Added a five-right-angle example checking both actual planar overlap and
  applicability of the half-plane topology theorem. Boundary collars, the
  sphere tree-to-disk converse, and the full relative forest theorem remain
  open; these local charts do not assert their global constructions.
- Verification: `lake exe cache get` and full `lake build` pass. The audit
  checks **3,689 unfolding declarations** and **7,243 pinned planar-topology
  declarations**, with only standard axioms. All **465 local documentation
  links** resolve.

### 2026-11-09 — exact graph criterion for boundary-rooted forests

- Defined the outside-vertex extension of a simple graph with marked roots.
  Proved connectedness iff every component meets the root set, and acyclicity
  iff the original graph is acyclic and distinct roots are never connected.
  Every added root edge is handled explicitly, preserving cycle obstructions.
- Proved the extension is a tree iff the original graph is a forest with
  exactly one root per connected component. Constructed a bijection between
  marked roots and connected components. No nonempty-vertex hypothesis is used.
- Added examples for the empty forest and one rooted edge, plus both failure
  modes: no root and two boundary roots in one component. The topological
  sphere-capping/slit-disk bridge remains in progress; the combinatorial
  equivalence is complete.
- Verification: full `lake build` passes. The audit checks **3,579 unfolding
  declarations** and **7,243 pinned planar-topology declarations**, with only
  standard Lean axioms. All **459 local documentation links** resolve.

### 2026-11-09 — intrinsic cut boundaries and planar openness

- Proved the circle is not contractible by real covering-lift uniqueness, and
  ruled out a disk-to-circle retraction. A continuous disk map fixing its
  sphere boundary covers its open ball; if injective, its interior image is
  exactly that open ball.
- Integrated Álvaro Begué's Apache-2.0 Jordan–Schönflies formalization at
  revision `05a43d29cde026618777db3d4e4316204ccca237`. Preserved all source
  notices and license; excluded challenge files and build caches. Documented
  the Lean 4.35 public-module and graph proof compatibility changes, with no
  theorem statement changes. Audited every imported vendor declaration.
- Derived planar invariance of domain from the verified Schönflies theorem
  and circle obstruction. The generic topology layer stays independent of
  project geometry and metrics.
- Proved every nonvertex point off the actual cut banks has a Euclidean metric
  ball chart on any spatially folded complex. Planar openness separates these
  charts from the actual one-sided bank charts under any disk homeomorphism.
  Perfect edges and the perfect boundary circle extend both inclusions across
  the finite vertex set. Thus every disk homeomorphism preserves exactly the
  actual unpaired-bank boundary, without a boundary-preservation hypothesis.
- Added `exists_cut_tree_of_homeomorph`: a disk homeomorphism of a cut convex
  boundary suffices to construct the actual straight cut tree. The earlier
  theorem statement remains unchanged. Tree-to-disk and the full disk forest
  criterion remain in progress.
- Verification: selected Mathlib cache fetch and full `lake build` pass. The
  audit checks **3,538 unfolding declarations** and **7,243 pinned planar-topology
  declarations**, allowing only standard Lean axioms. All **456 local
  documentation links** resolve and every project module is indexed.

### 2026-11-09 — boundary quotients and the disk-to-tree direction for edge cuts

- Added a topology-only boundary quotient API: distinct points in one fiber
  lie on a distinguished boundary. Proved exact boundary preimages, closedness
  of the boundary image, complement homeomorphisms, transport through domain
  homeomorphisms, and descent of punctured boundary retractions.
- Constructed the radial retraction for a standard closed ball. Its boundary
  quotient has an actual open-ball complement. When the target is a sphere,
  the boundary image is contractible and every exact embedded boundary graph
  is simple and a tree.
- Proved the actual union of unpaired triangle bank images is compact. Exact
  seam chains imply every nontrivial fiber of canonical seam restoration lies
  on those banks. The canonical map is a homeomorphism on bank complements.
  All boundary endpoints, original unpaired edges, and self-pairings are kept.
- A boundary-preserving disk presentation of an actual cut realization gives
  an open-disk complement and the disk-to-tree direction on a spherical target.
  On convex boundaries, constructed the exact finite straight spatial bank
  graph from original edge segments and proved it a tree. This graph is an
  output, not an additional hypothesis.
- Constructed standard source-disk boundary quotient data with exact cut-locus
  image. The existing source cut-locus contractibility proof now uses the
  generic theorem, with its statement unchanged. Added computation lemmas for
  complement homeomorphisms in terms of actual seam restoration.
- Updated README, topology guide, checklist, and complete module index. The
  tree-to-disk converse, intrinsic manifold boundary identification, disk
  forest equivalence, and cone-vertex sources remain open.
- Verification: selected Mathlib cache fetch and full `lake build` pass;
  **3,489 declarations** are audited with only standard Lean axioms. All
  **446 local documentation links** resolve and every module is indexed.

### 2026-11-09 — source cut-locus tree theorem

- Proved the source projection has singleton fibers away from the cut locus
  and all nontrivial fibers lie on the developed boundary. Radial boundary
  retraction descends through the punctured quotient to an actual continuous
  retraction of the punctured convex boundary onto its source cut locus.
- Stereographic projection proves the punctured original surface contractible.
  Its cut-locus retract and the exact spatial embedded graph carrier are
  therefore contractible as well.
- Added topology-only continuous graph extension and covering-lift theorems.
  Sending one selected edge around the circle and lifting to the real line
  constructs a vertex potential changing by one along that edge and constant
  along every other edge. This excludes loops and parallel edges and proves
  every adjacency edge a bridge, hence a contractible embedded graph is a tree.
- Applied the generic theorem to the actual source cut locus, including an
  explicit constructor theorem for every nonextreme source. The tree retains
  straight edge formulas, the exact carrier, and original-face containment.
  No Euler formula or Jordan separation theorem is assumed.
- Updated the short README, feature checklist, topology guide, and module index.
  General sphere/disk cut equivalences and cone-vertex sources remain open.
- Verification: selected Mathlib cache fetch and full `lake build` pass;
  **3,380 declarations** are audited with only standard Lean axioms. All
  **436 local documentation links** resolve and every module is indexed.

### 2026-11-09 — finite embedded cut graphs

- Added a topology-only finite embedded multigraph interface with actual
  continuous edge maps, disjoint open edges, and vertex avoidance. Loops and
  parallel edges are allowed. Connectedness of the carrier implies graph
  connectedness.
- Marked original segment endpoints and both endpoints of every nonempty
  pairwise intersection. Proved consecutive marked subsegments cover the
  network and distinct open cells cannot overlap, including collinear overlap
  and coincident input segments. Degenerate input segments remain as vertices.
- Constructed a finite embedded straight graph with exactly the original
  network as its carrier. Affine edge formulas imply that its multigraph is
  simple. Applied this construction to the actual source cut locus, preserving
  original-face containment and deriving graph connectedness.
- Verification: selected Mathlib cache fetches and full `lake build` pass;
  **3,345 declarations** are audited with only standard Lean axioms.
- Acyclicity, the tree/disk criteria, and Euler's formula remain open.

### 2026-11-09 — finite boundary representations and actual terminal source images

- Finite compact graphs of rigid face maps cover the retained endpoint graph.
  Closedness and interior density extend the cover to the whole completed disk.
  Bounded actual endpoint seam routes transport these vector representations
  to every original endpoint face, including ties and singular points.
- Vector injectivity and the finite rigid family prove that every endpoint has
  finitely many normalized shortest paths and boundary copies.
- Constructed the actual rigid radial formula on every whole face piece of
  every shortest path. Proper prefixes give the retained formula; continuity
  extends it through the terminal endpoint without assuming uniqueness there.
- Exact seam classes make face-interior endpoint tags unique. Every shortest
  path to such an endpoint has a finite actual terminal-face motion. Equal
  virtual source images give one final straight interval, so actual geodesic
  continuation proves equality of the whole original paths.
- The actual closed cut locus is a connected continuous image of the source
  boundary circle. Distinct-image bisector and polygonal/cut-graph results
  remain next.
- Verification: selected Mathlib cache fetch and full `lake build` pass;
  the audit checks **3,115 declarations**, using only the standard Lean axioms.

### 2026-11-09 — finite actual source motions and virtual source images

- Propagated whole actual motions through bounded oriented seam words,
  including both seam orientations and retained vertex crossings.
- Lifted every face-contained route piece continuously into its original
  closed face. Local constancy proves that its actual source motion is fixed.
- Proved an abstract finite-choice reachability lemma. Propagation through
  a complete retained face route takes its piece count plus one rounds,
  including initial and final face-copy choices.
- Actual shortest paths have at most `2 * card Face + 1` pieces. Thus a fixed
  source copy and `2 * card Face + 2` finite-choice rounds construct a finite
  global family containing every actual retained face motion.
- Inverting these motions at the developed source constructs finitely many
  virtual source images. Every retained endpoint distance equals distance to
  one of them. No minimum over infeasible candidate images is asserted.
- Extension to boundary path data and polygonal/Voronoi/cut-graph descriptions
  remain next.
- Verification: full `lake build` passes; the audit checks **3,095 declarations**,
  using only the standard Lean axioms. The selected Mathlib cache was verified.

### 2026-11-09 — actual source motions match outward seam transitions, including vertices

- Constructed a rigid expression of any actual local isometry in an open
  Euclidean chart, using a whole smaller metric ball; no image openness is assumed.
- Applied this to the actual source-coordinate map in the explicit outward
  hinge chart. One rigid motion expresses both incident face maps, so their
  actual motions differ by the constructed outward hinge placement.
- Proved every neighborhood in a genuine closed triangle edge contains a
  nonvertex point. Both source-face motions are locally constant along the
  retained edge, extending the exact transition identity to retained endpoints,
  including flat subdivision vertices.
- Bounded seam words can now propagate these actual motions. Finite global
  source-image and polygonal boundary/cut-graph descriptions remain next.
- Verification: full `lake build` passes; the audit checks **3,059 declarations**,
  using only the standard Lean axioms. The selected Mathlib cache was verified.

### 2026-11-09 — actual rigid motions on connected retained face regions

- Proved that two rigid motions agreeing on a neighborhood within a convex
  set with interior agree everywhere, even when the neighborhood center is
  on that set's boundary.
- Proved that rigid patches representing one coordinate map have locally
  constant whole-plane motions. This uses genuine overlapping interior
  patches, without assuming global convexity of the retained region.
- Constructed the actual source-coordinate atlas on each face's cut complement
  from the previous local existence theorem. Its chosen motions are locally
  constant, so one actual rigid map develops every connected retained part
  of the face. Seam-transition identification remains next.
- Verification: full `lake build` passes; the audit checks **3,048 declarations**,
  using only the standard Lean axioms. The selected Mathlib cache was verified.

### 2026-11-09 — constructed rigid source-face patches, including boundary centers

- Extended actual isometries of convex sets with interior to affine isometries.
  A whole interior ball constructs the map; segment preservation proves its
  agreement on the whole set, including the boundary. Finite dimension makes
  self-embeddings rigid equivalences.
- For a source in an original face interior, constructed an initial rigid
  placement agreeing with every shortest-path vector to that face's source-ball
  patch. Its isometry is derived from the original source chart and face metric.
- At every retained point of any face, constructed a positive-radius rigid
  patch agreeing with all actual source vectors and proved that this patch
  stays off the closed cut locus. Dense face interiors let the patch extend
  rigidly even when centered on an edge or flat subdivision vertex.
- Matching these actual local maps across the bounded seam words, and finite
  polygonality/Voronoi/cut-graph descriptions, remain next.
- Verification: full `lake build` passes; the audit checks **3,016 declarations**,
  using only the standard Lean axioms. The selected Mathlib cache was verified.

### 2026-11-09 — bounded actual seam routes and finite candidate placements

- Isolated graph reachability inside an exact fiber of a relation-preserving
  map. In a finite fiber, loop erasure gives a simple path shorter than the
  fiber cardinality. This combinatorial lemma has no unfolding dependencies.
- A spatial folding proves at most one tagged copy per original face. Exact
  seam gluing identifies all copies of a surface point, so any two are joined
  by fewer seams than the original face count, including at vertices.
- Constructed actual oriented seam routes with pointwise crossing witnesses,
  and tagged entry/exit points of every geodesic face-route piece. Every
  consecutive junction receives a bounded seam resolution without perturbing
  the path or assuming generic edge crossings.
- Bounded seam words form a finite type. Oriented outward hinge motions
  construct their rigid placements; their composition agrees at the actual
  crossing point. Matching these motions to the full source-coordinate map,
  and deriving finite polygonality/Voronoi data, remain next.
- Verification: selected Mathlib cache fetch and full `lake build` pass;
  the audit checks **3,011 declarations**, using only the standard Lean axioms.

### 2026-11-09 — cone leaves belong to the closure of actual shortest-path ties

- Proved a general topological lemma: a continuous projection of a perfect
  space cannot have singleton fibers outside a closed set while taking only
  finitely many values there. Such values would give a finite open neighborhood.
- The actual source boundary is a circle, hence perfect. Its images outside
  the closed cut locus can only be original singular vertices, a finite set;
  uniqueness off the cut locus gives singleton fibers. Therefore every boundary
  image lies in the closure of actual nonunique shortest-path endpoints.
- All true extreme vertices, including unique incoming cone leaves, are in
  that closed cut locus. The explicitly defined singular slit set equals it,
  and the regular retained region is exactly its complement.
- Recorded the actual cut-complement homeomorphism, local source isometries
  everywhere off the cut, and exact closed-cut boundary projection. Collected
  compactness, completeness, disk topology, injective development and the
  nonexpanding surjective surface projection in `source_disk_properties`.
- Finite polygonality, finite cut-graph and tree descriptions remain open.
- Verification: selected Mathlib cache fetch and full `lake build` pass;
  the audit checks **2,949 declarations**, using only the standard Lean axioms.

### 2026-11-09 — source disk topology and all completed radial geodesics

- Proved general compact radial bodies have exactly one boundary point on
  each ray. Normalization is a continuous bijection from the compact boundary
  to the unit sphere and hence a homeomorphism. Convexity is not assumed.
- Constructed a closed-ball homeomorphism through two compact quotient maps
  from boundary times the unit interval. They have exactly the same fibers;
  this handles the collapsed center continuously. Proved exact agreement of
  the body boundary with the target sphere.
- Applied these proved hypotheses to the actual source domain, obtaining a
  closed-disk homeomorphism of the intrinsic completed cut surface, with an
  exact characterization of its boundary circle.
- Constructed radial geodesics to every completed point using the actual
  allowed straight segments. Their endpoint projection agrees at every time
  with each original shortest path, including tied routes ending on different
  boundary copies. All source-to-point distances are preserved.
- Cone-leaf inclusion in the closure-of-ties cut locus and finite polygonal
  boundary/cut-tree descriptions remain open.
- Verification: full `lake build` passes; the audit checks **2,933 declarations**,
  using only the standard Lean axioms. The Mathlib cache was verified in this session.

### 2026-11-09 — actual intrinsic source cut metric and its completed development

- Constructed a separate polygonal point type and extended metric generated
  by straight steps whose whole segment stays in the region. Proved separation,
  nonexpanding ambient projection and inclusions, exact convex-patch distances,
  local Euclidean charts, and actual straight geodesics. The route metric equals
  continuous-path distance.
- On open regions this metric has the ambient topology. For bounded regions
  whose proper radial contractions land in the interior, uniformly shrinking
  gives the same conclusion at boundary points. Shrinking all route vertices
  proves the interior inclusion is isometric, and radial convergence gives
  density. A compact closed region is a complete model of its interior.
- Applied these constructions to the actual source domain. The retained
  surface's proved local source isometries identify its continuous-path distance
  exactly with the polygonal metric. This verifies intrinsic compatibility
  instead of relying only on a metric transported through a homeomorphism.
- The completed domain keeps distinct tied-path vectors, has an injective
  planar development, and projects continuously and surjectively to the original
  surface. Local inverse charts and density prove nonexpansion of this whole
  projection. Its boundary image is exactly the explicit singular slit set.
- Cone-leaf inclusion in the closure-of-ties cut locus, disk topology, finite
  polygonal boundary and cut-tree structure remain open.
- Verification: `lake exe cache get` and full `lake build` pass; the audit
  checks **2,844 declarations**, using only the standard Lean axioms.

### 2026-11-09 — exact source-domain interior and actual regular-region development

- Proved finite-dimensional rigid self-embeddings are open and surjective.
  The terminal affine patch and compact singleton-fiber stability therefore
  put every regular unique endpoint vector in the planar domain interior.
- Conversely, extend an interior vector slightly outward. Injectivity identifies
  it with a proper prefix of the longer actual shortest path. Thus an actual
  source vector is interior iff its endpoint is regular and off the closed cut.
- Every proper radial prefix is interior. Proved that the whole compact source
  domain is the closure of its interior and that its interior is star-shaped.
- Constructed a homeomorphism from the actual flat retained region onto that
  planar interior. Its coordinates are continuous, injective, locally isometric
  everywhere and carry actual retained geodesics to exact radial segments.
- Identified boundary projection exactly as the closed cut locus union singular
  points. Added the explicit closed `sourceSlitSet` for this union, and proved
  its complement is the regular retained region. All true extreme vertices
  are in the boundary image by the proved regularity classification.
- Equality of the slit set with the closure-of-ties locus alone remains the
  cone-leaf theorem. Intrinsic metric completion, finite polygon/Voronoi data,
  disk and cut-tree characterizations also remain open.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,700 declarations**, using only the standard Lean axioms.

### 2026-11-09 — retained radial paths and complete metric regularity classification

- Restricted every selected actual shortest path to the closed-cut complement,
  using the proved avoidance at proper prefix times. The restricted path is
  still geodesic; its constructed coordinates are exactly scalar multiples of
  the endpoint vector. The retained coordinate image is star-shaped.
- Proved a whole Euclidean ball chart contains a nonconstant actual geodesic
  through its center at an interior time. Extreme-vertex geodesic avoidance
  therefore rules out regularity at every true extreme vertex.
- Combined this with constructed nonextreme and nonvertex charts: actual
  regularity is equivalent to avoiding all true extreme vertex points.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,649 declarations**, using only the standard Lean axioms.
- Cone-vertex inclusion in the closure-of-ties cut locus and the completed
  boundary/cut-graph descriptions remain open; they are not assumed by the
  regularity or retained-radial results.

### 2026-11-09 — terminal source charts, regular local isometries and closed-cut avoidance

- Proved metric regularity is open and whole compact parameter intervals stay
  in an open chart under sufficiently small uniform path perturbations.
- Proved isometric coordinates of a geodesic interval are affine in its original
  real time. Any two distinct samples identify this affine map on the whole
  interval, including after a rigid chart placement.
- Constructed the initial source trace for a whole path-space neighborhood.
  Constructed each transition using a common ambient ball and two retained
  samples; finite chart stability proves the formula for all nearby paths.
- Chose an actual finite strictly ordered chart partition of every regular
  reference path. Finite induction constructs a terminal affine endpoint chart
  formula; the reference path's regularity is the sole local geometry premise.
- Proved compact endpoint-fiber stability at a unique path without assuming
  that nearby endpoints are unique. Combined it with the terminal formula and
  source-vector injectivity to exclude ties on a whole endpoint neighborhood.
- A unique path to a regular convex-boundary endpoint therefore lies off the
  closed source cut locus. Every proper prefix avoids that closed cut locus,
  strengthening the earlier exclusion of only the nonunique-endpoint set.
- Constructed local isometries of the actual source coordinates at every
  regular retained point.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,641 declarations**, using only the standard Lean axioms. Cone-vertex cut inclusion and the completed boundary
  interpretation remain open, as do finite Voronoi and cut-tree results.

### 2026-11-09 — rigid extension of ball maps and actual metric-chart transitions

- Proved isometric maps on convex subsets preserve every affine segment
  parameter when the target norm is strictly convex.
- Extended an actual isometric open-ball map to an affine isometry of the
  whole ambient normed space. Positive radial sample slopes agree; shrinking
  any pair of points to a common scale proves the global distance equality.
  Neither surjectivity nor a global extension is assumed in the input.
- Recentered open isometric charts on whole ambient metric balls. Two charts
  at a common point now have a constructed rigid affine coordinate transition
  on one whole ambient neighborhood, by applying the ball extension theorem.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,566 declarations**, using only the standard Lean axioms.
- These general metric/convex lemmas provide the transition step for propagating
  source coordinates along regular shortest paths. That propagation remains open.

### 2026-11-09 — continuous source coordinates off the cut locus, isometric near the source

- Proved endpoint evaluation from the compact shortest-path space is a closed
  map. Over the closed cut-locus complement its fibers are singletons, so its
  restriction is a homeomorphism. The unique path is therefore continuous in
  the uniform topology; continuity is not assumed for a choice function.
- Constructed continuous source coordinates on that complement. On actual
  convex boundaries they are injective, and their norms recover source
  distance. The existence theorem assumes only the original convex-boundary
  input and actual regularity of the selected source.
- Proved every shortest path to a point in the source chart stays there, and
  its source vector equals the endpoint's actual chart displacement. Thus the
  constructed coordinates are an isometry on the whole source chart ball.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,519 declarations**, using only the standard Lean axioms.
- Propagation of local metric compatibility, proper-prefix stability against
  the closed cut locus, and the completed slit interpretation remain open.

### 2026-11-09 — bounded finite face partitions of actual geodesics

- Proved a finite closed interval cover has a strictly ordered subdivision
  with at most twice the cover size plus one pieces, each contained in one
  covering interval. The proof sorts actual endpoints and uses no open-cover
  or general-position hypothesis.
- Applied the derived closed interval face-visit theorem to every actual
  embedded-surface geodesic. Constructed explicit times and face labels with
  at most `2 * card Face + 1` pieces, allowing flat-vertex crossings.
- Proved each piece's exact spatial affine parametrization and exact additive
  chord length. A generic monotone geodesic partition theorem telescopes its
  distances even in extended metric spaces.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,498 declarations**, using only the standard Lean axioms.
- Seam-adjacent unfolding words and finite Voronoi descriptions remain open;
  the finite face partition does not assume any of those conclusions.

### 2026-11-09 — spliced geodesics and proper-prefix uniqueness

- Constructed an actual constant-speed geodesic by replacing a prefix with any
  other shortest path to the joining point. Constant extension, normalization,
  and a finite closed cover prove the common speed bound across the join.
- Derived unique continuation from a final interval by reversing the actual
  path parameters. Applied it to the spliced geodesic and unchanged tail.
- Every proper positive-time prefix of a nonconstant convex-boundary geodesic
  is the unique shortest path to its endpoint. Consequently nonunique source
  endpoints cannot occur at interior times of another shortest path.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,469 declarations**, using only the standard Lean axioms.
- Exclusion from the closure of nonunique endpoints still needs local stability;
  no cut-locus tree or completed source-unfolding claim is made here.

### 2026-11-09 — actual shortest-path source vectors and compact planar ray domains

- Constructed a source frame from any actual regular ball chart. A positive
  sample time depends only on endpoint distance and stays in the source chart.
  Extending the initial straight displacement gives a full-length planar vector
  with norm exactly equal to intrinsic source distance.
- Equal vectors force initial agreement. The proved convex-boundary continuation
  theorem then distinguishes all normalized shortest paths, including distinct
  tied paths to the same cut-locus endpoint and the constant source path.
- Equipped the whole shortest-path space with uniform distance. The source
  condition and geodesic equations are closed; the compact surface diameter
  bounds all speeds. Arzela--Ascoli gives actual compactness of this path space.
- Proved continuity of the constructed vectors and identified the path space
  homeomorphically with its compact planar image. Endpoint evaluation gives
  a continuous surjection back to the actual surface, preserving endpoint ties.
- Proved exact initial chart coordinates and prefix-vector scaling. Every
  actual shortest-path prefix is represented, so the whole planar image is
  star-shaped, including zero and full time.
- Defined the closed source cut locus as the closure of nonunique endpoints.
  Proved a whole source ball misses it and convex-boundary shortest paths
  exist uniquely outside it. This does not yet prove the cone-leaf or tree
  characterization, nor local metric compatibility of the planar image.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,463 declarations**, using only the standard Lean axioms.
- Next: uniqueness and stability of proper prefixes, local unfolding isometries,
  finite route descriptions and cut-locus structure. Source unfolding remains open.

### 2026-11-09 — genuine hinge charts and regular geodesic interiors

- Proved finite piecewise rigid planar parametrizations of the actual spatial
  tangent image are intrinsic isometries. Both metric bounds come from the
  route metric and finite closed covers, including seams within either piece.
- Extended actual outward edge placements to the entire supporting half-planes.
  Supporting functionals give the precise side tests and injectivity, including
  agreement along the whole seam line.
- Selected a genuine crease from distinct cyclic incident planes and constructed
  support hinges with those prescribed incident faces. Distinct supports put
  opposite corners strictly on their own sides, as required by the parametrization.
- Constructed whole intrinsic Euclidean ball charts at every nonextreme vertex,
  including subdivision vertices on genuine polyhedron edges. No angle equality
  or intrinsic isometry is assumed by the geometric construction.
- Combined these charts with extreme-vertex avoidance: every interior point of
  a nonconstant geodesic is regular. Two geodesics agreeing on an initial interval
  agree everywhere, with no remaining regularity premise.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,337 declarations**, using only the standard Lean axioms.
- Numerical angle equality at nonextreme vertices and source unfolding remain
  open. Next: source geodesic coordinates and normalized finite routes.

### 2026-11-09 — whole tangent hinges and convex spatial inverse isometries

- Proved local equality extends globally for sets invariant under positive
  homotheties about the same apex. Proved exact radial homogeneity of the
  actual tangent image and of support levels/half-spaces.
- Identified the spatial tangent image with the original surface on one
  small ball, using radial distance and the derived spatial vertex star.
  Consequently the whole tangent image equals the constructed support hinge.
- Constructed the actual inverse tangent folding on spatial subsets. Its
  finite closed isometric wedge cover makes this inverse isometric on every
  convex spatial subset, including across coplanar subdivisions.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks **2,237 declarations**, using only the standard Lean axioms.
- Next: use a genuine incident crease and its constructed outward placement
  to parametrize the two half-planes and obtain the intrinsic hinge chart.
  Source unfolding remains open.

### 2026-11-09 — actual local vertex hinges and planar metric charts

- Proved a nonconstant finite cyclic list has no more labels than changes,
  using an entry for each proper nonempty label class. Applied the two-crease
  bound to obtain at most two actual incident face planes.
- Proved every face containing a spatial vertex has an actual corner there,
  and excluded all nonincident faces from one small spatial ball. The nearby
  surface at a nonextreme vertex lies in the derived two incident planes.
- Used radial projection to prove the converse: a convex frontier locally
  contained in two supporting planes is exactly their supporting half-planes
  near the point. Constructed actual vertex support hinges, with coincident
  planes allowed and no metric conclusion stored as an assumption.
- Constructed whole intrinsic metric-ball charts from actual planar patches
  via convex spatial inverse isometries and ambient ball coverage. This proves
  regularity in the coincident-plane case, including subdivision vertices.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2219 declarations with only standard Lean axioms; `git diff --check`
  passes.
- Next: the metric chart for a genuine two-plane hinge and nonextreme angle
  equality, followed by source routes and source unfolding.

### 2026-11-09 — exact radial directions and at most two nonextreme creases

- Constructed original-edge coordinates at each sufficiently small positive
  radius, proved them nonvertex, and computed their exact spatial images.
- Equal normalized spatial germ directions give equal spatial lifts.
  Embeddedness and exact seam classes classify these precisely as equal
  germs or seam mates. Cyclic chain initial directions are therefore distinct.
- A nonzero real line has only two opposite unit directions. Combined this
  with the derived common crease axis to prove at most two genuine creases
  in every nonextreme cyclic vertex link, retaining all coplanar subdivisions.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2162 declarations with only standard Lean axioms; `git diff --check`
  passes.
- Next: reduce incident planes to at most two and construct the actual local
  plane/hinge metric chart. Nonextreme angle equality and source unfolding
  remain open.

### 2026-11-09 — common axes at nonextreme subdivision vertices

- Proved a rigid two-dimensional spatial plane equals any nonzero functional
  level containing it. A supporting functional attaining its bound inside
  a body chord has that same value at both chord endpoints.
- Applied a nontrivial body chord through each nonextreme vertex to derive
  a common nonzero direction in every actual incident face plane.
- Proved distinct two-dimensional spatial planes intersect in the line of
  any shared nonzero vector. Actual germ directions are nonzero, lie in
  their face planes, and are preserved by seam mates.
- Consequently every genuine crease at a nonextreme vertex lies along the
  one derived axis. Flatness still requires limiting repeated axis rays and
  measuring the coplanar link arcs; source unfolding remains open.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2143 declarations with only standard Lean axioms; `git diff --check`
  passes.

### 2026-11-09 — derived closedness and nonvertex regularity

- Constructed continuous gauge projection onto a bounded convex frontier,
  from any body interior point. It fixes boundary points; a point and its
  projection on the same strict supporting level must coincide.
- Moved across each triangle edge in its supporting plane and projected
  back to the boundary. This gives boundary points outside that triangle
  arbitrarily near every edge point. Finite closed face coverage forces
  another incident original face there.
- Embeddedness and exact nonvertex seam classes then force an actual seam
  at every original edge. Thus no unpaired bank or boundary vertex remains
  in the uncut complex, and all its actual vertex links are cyclic.
- Removed the interior premise from extreme-vertex curvature equivalence
  and geodesic avoidance. Constructed regular charts at every nonvertex
  surface point using original face or either-bank hinge charts.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2131 declarations with only standard Lean axioms; `git diff --check`
  passes.
- Nonextreme subdivision flatness and source unfolding remain open.

### 2026-11-09 — one-turn figure fans and strict extreme-vertex curvature

- Used Mathlib's gauge to normalize nonzero rays to the actual convex
  frontier. Proved radial cones over the actual figure edges cover the
  punctured plane and their open sectors are separated.
- Derived supporting half-planes and consistent radial orientation for
  adjacent boundary edges, including straight subdivisions. Proved affine
  signed-area scaling and transported these signs to one normalized frame.
- Constructed exact cumulative real headings from genuine central angles.
  Transferred open-cone separation to angular nonoverlap. Its total angle
  is positive and at most one turn; the closing ray forces exactly one turn.
- Proved an interior center splits every simple convex boundary corner angle
  exactly. Summing central triangle angles yields the actual figure polygon
  angle sum, including flat subdivisions.
- Combined this with the strict lateral pyramid budget to prove total angle
  below two pi at interior spatial extreme vertices. Together with the prior
  converse this gives extremality iff positive curvature. Intrinsic geodesics
  avoid these extreme vertices at all interior times.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2106 declarations with only standard Lean axioms; `git diff --check`
  passes.
- Remaining: derive closedness of the uncut triangulation and flatness of
  nonextreme subdivision vertices, then source routes and source unfolding.

### 2026-11-09 — actual simple figure polygons and strict angle budgets

- Proved chords joining nonvertex points of different triangle edges enter
  the face interior. Embedded original face interiors meet no other face;
  hence every open figure section misses every other closed section.
- Converted the derived cyclic chain into a Mathlib polygon. Proved its
  edges nondegenerate, open edges separated, at least three vertices, and
  boundary exactly the planar figure frontier, allowing flat subdivisions.
- Identified its spatial apex-angle sum with the genuine surface total
  angle and applied the lateral pyramid angle budget.
- Proved any nonempty finite point list has a nonstraight chosen corner
  by taking a farthest point and using strict convexity. This makes the
  transverse pyramid budget strict without any extra corner hypothesis.
- Proved supporting functionals for convex boundary segments, noncollinear
  central triangles, and unique boundary points on positive rays. Constructed
  the figure's actual positive-angle central fan.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 2042 declarations with only standard Lean axioms; `git diff --check`
  passes.
- Next: prove this central fan makes exactly one turn and obtain the planar
  polygon angle sum. The convex angle bound and source unfolding remain open.

### 2026-11-09 — actual link germs and ordered figure sections

- Constructed each planar figure endpoint by projecting the actual far
  endpoint of its link germ. Proved seam crossings and mates preserve this
  point, including seams that reverse endpoint labels.
- Identified each corner section with the planar segment between its two
  germ points. These segments lie on the actual figure boundary; their
  spatial apex angles equal the original positive triangle corner angles,
  so every segment is nondegenerate.
- Derived consecutive and closing endpoint agreement from the actual link
  chain. Proved any covering link chain covers exactly the figure boundary.
- Proved the section misses every original corner. Its endpoints lift to
  nonvertex original-edge points; embeddedness classifies equal endpoints
  precisely as equal germs or seam mates. The cyclic chain consequently
  has no repeated initial endpoints.
- Verification: cache refresh and full `lake build` pass; the audit checks
  2013 declarations with only standard Lean axioms; `git diff --check` passes.
- The simple cyclic polygon and its planar angle sum remain next, followed
  by the convex upper angle bound. Source unfolding remains open.

### 2026-11-09 — actual supporting face planes and figure boundary segments

- Proved an affine real functional with a local maximum is constant, and a
  nonzero support functional is strictly below its level in the ambient
  interior. Used separation at an input face interior to prove its entire
  affine plane supports the convex body, including subdivided maximal facets.
- Identified the planar figure boundary exactly with the original spatial
  surface intersected with the transverse level plane.
- Proved nonincident faces cannot meet the section: their corner heights,
  hence all triangle heights, are strictly above the level. Every boundary
  point therefore lies in a face with an actual corner at the chosen vertex.
- Applied the full slice-hull formula to each incident triangle, obtaining
  exactly the segment between its two radial corner projections. Proved
  these actual segments lie on and cover the complete figure boundary.
- Verification: full `lake build` passes; the audit checks 1971 declarations,
  only standard Lean axioms occur, and `git diff --check` passes.
- Next: the actual cyclic order of these boundary segments and its planar
  angle sum, then the convex upper angle bound. Source unfolding is open.

### 2026-11-09 — nondegenerate planar vertex figures

- Proved a positive transverse section below a body point meets the ambient
  interior of a convex body. Constructed an interior center for each actual
  extreme-vertex section while retaining its finite-hull description.
- Constructed Euclidean affine coordinates on every nonzero functional level
  plane in spatial dimension three, using its two-dimensional kernel and an
  orthonormal basis.
- Constructed actual planar vertex figures from convex-boundary data. Proved
  their carriers compact and convex, exactly the hull of finitely many radial
  corner generators, with zero in their interior. The generators span the
  plane and are noncollinear; their boundary is homeomorphic to a circle.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1958 declarations, and `git diff --check` passes.
- The actual link's polygon boundary order and planar angle sum remain to
  connect these figures to the convex angle bound. Source unfolding is open.

### 2026-11-09 — complete slice hulls and spatial tangent embeddings

- Proved the full transverse body section equals the convex hull of all
  other generator projections. The proof rescales finite barycentric weights
  by functional height and discards zero-height copies of the original vertex.
  Applied this equality to actual spatial extreme vertices.
- Proved one positive dilation places any two tangent points in a prescribed
  apex ball. Used exact local tangent neighborhoods and the original spatial
  embedding to prove injectivity of the whole uncut tangent folding.
- Proved tangent folding preserves every apex distance and is proper for all
  retained-seam sets. For embedded original surfaces the uncut tangent map is
  a closed spatial embedding.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1902 declarations, and `git diff --check` passes.
- The vertex figure's nondegeneracy, cyclic polygon boundary and planar angle
  sum remain next. The convex upper angle bound and source unfolding are open.

### 2026-11-09 — constructed transverse sections and pyramid angle budgets

- Strictly separated each finite-hull extreme point from the compact hull
  of the other generators. The functional has a uniform positive margin.
- Constructed actual compact convex level sections and projected generator
  points along their original vertex segments. At actual spatial extreme
  vertices, proved the section nonempty and the functional nonzero.
- Characterized two-ray wedge sections exactly as segments between the
  normalized endpoints; proved positive normalization preserves apex angles.
- Proved a direction transverse to a level plane makes angular triangle
  inequality strict unless its two boundary directions are opposite.
- Summed lateral triangle angle budgets over any finite successor permutation,
  with strictness at a nonstraight base corner for a transverse apex.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1895 declarations, and `git diff --check` passes.
- The section's polygon description, actual link order and planar angle sum
  remain to connect to the convex upper angle bound. Source unfolding is open.

### 2026-11-09 — regular continuation and spatial boundary chords

- Added inverse affine subpath parameters and proved two-point determination
  of a chart-straight geodesic subpath. Continuous induction propagates an
  initial common interval along regular points, without endpoint charts.
- Defined regularity by genuine Euclidean metric-ball charts and connected
  the constructed face, hinge and flat-vertex charts to this interface.
- Proved the embedded inverse is isometric on every convex spatial subset
  of a convex boundary, using the finite original-triangle closed cover.
  Boundary chords have exact intrinsic distance and a unique geodesic even
  when crossing many subdivision edges.
- Proved a segment through an interior convex-frontier point stays entirely
  on the frontier. Combined its exact geodesic with vertex avoidance to show
  positive-curvature interior vertices are spatial extreme points.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1875 declarations, and `git diff --check` passes.
- The convex upper angle bound and full regular/singular classification
  remain open, followed by source routes, cut locus and source unfolding.

### 2026-11-09 — cyclic shortcuts and original-surface vertex avoidance

- Appended a repeated first angular sector, proved its exact continued
  headings and constructed nonexpanding cyclic maps through the closing
  bank. Radial distances remain exact in this extension.
- Proved cell shortcuts on the selected sheet for all heading gaps below
  pi, including coincident headings. The repeated sector handles short
  arcs crossing the cyclic slit even if the extended development overlaps.
- Started actual cyclic links at arbitrary prescribed germs. Combined the
  cyclic shortcut with actual closing seam equality to prove strict apex
  shortcuts for every pair of nonapex actual tangent points at an interior
  vertex whose total angle is less than a full turn.
- Proved the whole-ball chart sends apex to the original vertex. Transferred
  the strict shortcuts to the original intrinsic metric and proved every
  nonconstant geodesic avoids such vertices at all interior times.
- Added generic geodesic injectivity and local strict-shortcut avoidance.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1849 declarations, and `git diff --check` passes.
- Convex geometric angle bounds, continuation, finite source routes, cut
  locus and source unfolding remain open.

### 2026-11-09 — sheet-aware isometric heading lifts

- Constructed a lift of every pointed real heading interval contained in an
  arbitrary angular fan. The full development may overlap and its total
  angle is unrestricted.
- Proved uniqueness of positive-radius headings on bounded intervals and
  on intersecting pointed intervals. Restricted the finite closed-cover
  bound to pieces meeting the selected interval, retaining the intended
  sheet through the construction.
- Proved the selected lift is isometric, preserves radial distance and has
  strict apex shortcuts. Such shortcuts survive radial-distance-preserving
  nonexpanding maps to arbitrary extended metric spaces.
- Verification: full `lake build` passes; the audit checks 1803 declarations,
  and `git diff --check` passes.
- Continuing with a repeated first sector to lift cyclic arcs across the
  chosen slit. Source unfolding remains open.

### 2026-11-09 — exact angular chords and strict apex shortcuts

- Proved development injectivity below one full turn, including all banks.
  Constructed the Euclidean sector isometry when the total angle is less
  than pi, with inverse bounds obtained from its finite closed sector cover.
- Proved strict chord shortcuts between nonzero points of pointed sectors
  and apex avoidance for geodesics in convex angular fans.
- Extended the inverse bound to every covered convex set in a reentrant
  slit fan. In particular, every covered chord realizes intrinsic distance.
- Added rotated sectors retaining real heading bounds. Shortcuts across
  multiple pieces transfer to the actual tangent metric by the constructed
  nonexpanding comparison and exact radial distances, without a folding.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1787 declarations, and `git diff --check` passes.
- Cyclic shortcuts crossing the chosen slit remain open, as do general
  positive-curvature vertex avoidance, convex angle bounds and source unfolding.

### 2026-11-09 — shortest paths in actual flat charts

- Added codomain restriction preserving length and geodesics, and affine
  constant-speed subpaths for arbitrary endpoint order.
- Proved exact affine coordinates and uniqueness of contained geodesics in
  isometric charts. Convex coordinate domains construct ambient geodesics.
- Proved an endpoint-distance bound confining every competing geodesic to
  an open ball; Euclidean ball charts therefore give ambient uniqueness.
- Applied construction, straightness and uniqueness to the actual flat
  vertex charts. No local straightness or uniqueness is assumed as data.
- Verification: selected cache fetch and full `lake build` pass; the audit
  checks 1752 declarations, and `git diff --check` passes.
- Angular shortcuts and positive-curvature vertex avoidance remain next;
  source unfolding is still open.

### 2026-11-09 — Euclidean cyclic fans and actual flat vertex charts

- Constructed the closing identification from every actual cyclic link,
  including one-corner cycles. Refactored the consecutive-seam proof for
  reuse without changing its public theorem statements.
- Added closed polar sector coordinates and full-turn coverage of the whole
  plane. Classified all full-turn development fibers, including the apex,
  consecutive banks and the two outer banks.
- Descended full-turn planar coordinates through every actual tangent seam.
  The actual closing seam removes exactly the extra outer-bank fibers,
  proving bijectivity. Proved the inverse nonexpanding on each closed sector
  and then on the whole convex plane by the finite closed-cover theorem.
- Constructed the Euclidean isometry for every actual full-turn cyclic
  tangent fan, without a spatial folding. Normalized it at the origin.
- Composed the isometry with the proved whole-ball tangent comparison to
  construct actual Euclidean ball charts at flat interior vertices of
  spatially folded complexes, agreeing with every incident face coordinate.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1718 declarations, and `git diff --check` passes.
- Local geodesic straightness, convex angle bounds and vertex avoidance remain
  next. Source routes, cut locus and source unfolding are still open.

### 2026-11-09 — inverse interval metric comparison

- Constructed nonexpanding angular maps on every actual tangent cell using
  the unique ordinal selected by its covering link order.
- Classified all actual retained seams of an interval link as consecutive
  in one direction or the other. Extended the bank-coordinate formulas to
  every radial extension, not only the prescribed-radius witnesses.
- Proved compatibility of the inverse cell maps with every actual seam,
  descended the inverse and checked both round trips on original cells.
- Obtained an explicit isometry from the ordered angular fan to the actual
  tangent fan at every boundary vertex, with its genuine total angle. No
  spatial folding is assumed.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1628 declarations, and `git diff --check` passes.
- Cyclic closure and full-turn Euclidean cone charts are next; source
  unfolding remains open.

### 2026-11-09 — exact nonoverlap criterion for angular fans

- Characterized genuine sector interiors by positive radii and strictly
  intermediate real headings. Characterized rigid fan piece interiors by
  the corresponding open cumulative-heading intervals.
- Defined angular fan nonoverlap using pairwise disjoint actual planar
  interiors. Proved it iff total angle is at most a full turn.
- At equality, proved that the two outer banks have coincident developed
  coordinates. Above a full turn, constructed two distinct piece interiors
  overlapping at every prescribed positive radius, away from all banks.
- Added geometry-independent chain pairing classification: every nonfixed
  pairing is consecutive or closes the two outer ends. Interval chains have
  only the consecutive cases, supporting the inverse metric comparison next.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1599 declarations, and `git diff --check` passes.
- This completes the slit angular-fan benchmark. Flat cyclic charts, convex
  vertex avoidance and source unfolding remain open.

### 2026-11-09 — directed actual/angular fan comparison

- Constructed angular-bisector reflections exchanging the two sector banks.
  Directed rigid corner frames follow each actual initial link germ and send
  the two banks to the expected rays at their exact metric radii.
- Proved barycentric bank equations for actual radial seam points, including
  endpoint reversals. Constructed actual glue witnesses at every prescribed
  nonnegative radius by scaling the opposite original edge endpoint.
- Used the actual seam and endpoint data at each ordered corner transition
  to descend a nonexpanding angular-to-tangent comparison through the route
  metrics. It is surjective for a covering link order, maps apex to apex and
  preserves all distances from the apex. No spatial folding is assumed.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1584 declarations, and `git diff --check` passes.
- The inverse comparison for interval links, cyclic closure, flat charts and
  source unfolding remain open.

### 2026-11-09 — constructed slit angular fans

- Constructed nonempty finite fans of actual closed Euclidean sectors, with
  angles strictly between zero and pi. Partial sums retain real cumulative
  headings, which are strictly increasing and end at the total angle.
- Glued each terminal ray to the next initial ray at equal nonnegative radius.
  The existing route construction supplies the metric and separation quotient.
- Rigid sector placements agree across these seams and descend to an actual
  nonexpanding planar development for every total angle, including overlap.
  Derived exact within-cell metric distances from that constructed map.
- Identified all apices, proved exact radial distances and finite distances
  between every pair, and registered the canonical ordinary metric.
- Actual retained-link orders supply genuine angle lists with exactly the
  previously defined metric vertex total angle.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1520 declarations, and `git diff --check` passes.
- The oriented comparison with actual tangent fans, flat cyclic closure,
  complete fan nonoverlap criterion and source unfolding remain open.

### 2026-11-09 — actual wedges and angular sectors

- Proved unique boundary-ray coordinates on every original triangle wedge,
  including its genuine topological interior. Constructed normalized rigid
  complex frames from two-point isometries and the upper-side convention.
- Proved that the second ray's argument equals the actual Euclidean corner
  angle. Restricted the frame to an isometry from the whole original wedge
  onto the closed positive-span sector at that angle.
- Constructed sector coordinates, closedness, convexity, actual interiors,
  supporting half-plane descriptions and real angular representations.
- Proved that the real-heading polar map on an open positive-radius strip is
  injective iff its width is at most a full turn. Wider strips have explicit
  collisions at every positive radius, so overlap remains representable.
- Extracted actual retained radial seams along every consecutive pair in the
  previously constructed corner orders, including endpoint transport.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1456 declarations, and `git diff --check` passes.
- Fan assembly with cumulative headings, its metric comparison and the flat
  vertex chart remain next. This is not yet the complete fan nonoverlap or
  source-unfolding theorem.

### 2026-11-09 — finite closed-piece distance bounds

- Adapted the generic interval center-bound argument from EdgeUnfoldings,
  with attribution and no source- or face-count hypotheses.
- Proved that finitely many closed covering pieces give local center bounds
  from their common Lipschitz constant. Derived continuity from those bounds.
- Extended the bound along segments by continuous induction, obtaining the
  common Lipschitz constant on a convex domain. Included subtype domains.
  Pieces need neither convexity nor maps extending to the whole domain.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1373 declarations, and `git diff --check` passes.
- These generic lemmas support flat-fan inverse maps, metric refinement and
  facet chord arguments; they do not themselves construct an angular fan.

### 2026-11-09 — exact radial dilations

- Added generic descent of compatible cell maps with any positive finite
  Lipschitz bound, including the route-distance estimate. Positivity is
  necessary for arbitrary disconnected realizations because zero times
  infinite distance is zero.
- Constructed tangent-fan dilations at every nonnegative scale from actual
  wedge coordinates. Proved seam compatibility, zero/identity/composition
  laws, exact scaling of all intrinsic distances and reciprocal
  homeomorphisms at positive scales. No spatial folding is required.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1367 declarations, and `git diff --check` passes.
- Angular developments and flat fan charts remain the next geometric work.

### 2026-11-09 — whole-ball tangent charts

- Selected a uniform positive radius where every tangent wedge lies inside its
  original triangle, and proved exact original/tangent vertex distances there.
- Proved that tangent seam identifications within the triangles are original
  retained seam identifications. Local route budgets give the first distance
  comparison without assuming a global map outside the neighborhood.
- Constructed the reverse tagged maps using uniqueness of incident corners per
  spatially folded face. They agree across every incident original seam;
  closed-seam localization gives the reverse metric bound.
- Proved that all sufficiently near original representatives have incident
  face labels. Combined both bounds into whole-ball isometries agreeing with
  every original incident face coordinate, for arbitrary retained seam sets.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1338 declarations, and `git diff --check` passes.
- Angular developments, flat-vertex charts, geometric convex angle bounds and
  the source-unfolding construction remain open.

### 2026-11-09 — constructed tangent metric fans

- Constructed tangent cells from the actual corner wedges and glued all
  nonnegative radial extensions of the retained original edge isometries.
  Endpoint reversals, boundary vertices and self-pairings remain represented.
- Proved that all wedge apices coincide using the actual connected vertex link.
  The origin is chosen only after this identification theorem.
- Descended the compatible cell-radius functions and proved exact distance
  from the origin. Derived finite distances and a canonical ordinary metric.
- Proved that closed origin balls are finite unions of compact wedge balls;
  the tangent fan is proper and complete.
- Proved equality of route distance and continuous-path distance, and
  constructed explicit constant-speed radial geodesics with exact length.
- Extended spatial face foldings to the tangent fan. These give nonexpanding
  spatial maps and isometric tangent-cell maps when a spatial folding exists.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1263 declarations, and `git diff --check` passes.
- Comparison with the original vertex-star balls, angular fan developments,
  flat-vertex charts and convex-vertex avoidance remain open.

### 2026-11-09 — metric excision and vertex-star neighborhoods

- Strengthened generic finite closed-seam localization: compatibility only at
  incident seams makes a map constant on the chosen class and nonexpanding on
  a whole sufficiently small intrinsic neighborhood.
- Constructed whole-ball isometries for seam excision, using the canonical map
  that restores cuts. Applied this to triangle complexes without a development
  or manifold assumption.
- Isolated each vertex's incident seams. Proved that its complete corner class,
  unique central vertex copy, total angle, and a whole small metric ball remain
  unchanged after cutting all distant seams.
- Constructed actual convex closed supporting wedges at triangle corners and
  wedge-ball/cell-ball isometries. Proved positive clearance to the opposite
  edge and invariance of the wedge under nonnegative radial scaling.
- Proved that spatially foldable complexes have at most one representative of
  a point class in any original cell; incident corner classes therefore use
  distinct original faces.
- Verification: selected cache fetch and `lake build` pass; the audit checks
  1151 declarations, and `git diff --check` passes.
- The metric tangent fan/cone and its comparison with these star neighborhoods
  remain to be constructed; no source-unfolding conclusion is assumed here.

### 2026-11-09 — constructed vertex-link orders

- Constructed the endpoint permutation of every full-edge isometry, including
  reversal. Defined the two actual edge germs at every tagged triangle corner.
- Proved uniqueness and symmetry of retained seam germ pairings. Seam transport
  is an involution with fixed points precisely at unpaired boundary banks;
  turning within a corner is a fixed-point-free involution.
- Proved that germ connectivity is exactly retained metric-vertex equivalence.
  Thus a vertex link has no hidden disconnected components. Boundary incidence
  is equivalent to existence of an unpaired link germ.
- Proved a geometry-independent finite two-involution classification by maximal
  nonrepeating interval chains. Closed systems give cycles, and boundary systems
  give intervals with exactly two unpaired endpoints. One-interval cycles are
  allowed, so loops/self-pairings are preserved.
- Applied that classification to every cut vertex link, constructing its cyclic
  or interval corner order. Each incident corner occurs exactly once and its
  ordered Euclidean angles sum to the actual vertex total angle.
- Verification: selected Fin-tuple/endpoint-geometry cache fetch and `lake build`
  pass; the audit checks 1083 declarations, and `git diff --check` passes.
- Metric fan/cone neighborhoods and geometric convex-vertex angle bounds remain
  unproved; no such conclusion was made a link-order input.

### 2026-11-09 — vertex copies and actual angle sums

- Defined vertices as quotients of tagged original corners by retained-seam
  chains. Proved their images inject into the actual metric realization and
  characterize exactly its original corner points.
- Constructed surjective maps between vertex copies when restoring cuts,
  commuting with the metric maps. Defined boundary incidence using endpoints
  of the actual unpaired banks.
- Defined corner angles from Euclidean geometry, proved each is strictly
  between zero and pi, and proved each triangle's sum is pi.
- Defined total angles of retained vertex classes. Proved positivity, the
  global sum `number of triangles * pi`, and conservation of angle when a
  vertex splits into cut copies. No cone-chart or curvature-bound conclusion
  has been assumed.
- Verification: selected triangle-geometry cache fetch and `lake build` pass;
  the audit checks 929 declarations, and `git diff --check` passes.
- Vertex-link classification and metric cone/sector charts are next.

### 2026-11-09 — spatial convex boundaries and face visits

- Added compatible rigid spatial face placements. They descend through every
  cut metric and make every original cell isometric. Spatial injectivity stays
  separate; for embedded uncut surfaces, proved equality of intrinsic and
  spatial subspace topology. Rigid foldings rule out same-face edge pairings.
- Added a geometric convex-boundary adapter: the actual finite corner hull has
  nonempty spatial interior, and the embedded triangle union is exactly its
  frontier. Flat/subdivision corners are allowed. Maximal facets are not yet
  represented by a separate API.
- Used Mathlib's gauge-rescaling homeomorphism to derive sphere topology,
  connectedness, finite intrinsic distances and shortest paths. The generic
  bounded-convex-boundary theorem lives separately in `Topology/`.
- Proved strict-convexity straightness of saturated nonexpanding geodesic images,
  including their affine parameterization. Proved face no-re-entry on embedded
  surfaces and that each visited closed face occupies one closed time interval.
- Proved that finite metric distances are equivalent to retained face-incidence
  connectivity; geometric convex boundaries therefore have connected dual incidence.
- Verification: selected Mathlib cache fetch and `lake build` pass; the audit
  checks 892 declarations, and `git diff --check` passes.
- Cone geometry, vertex avoidance, cut-locus construction and source unfolding
  remain open; this adapter assumes no geodesic or unfolding conclusion.

### 2026-11-09 — retained-edge Euclidean ball charts

- Proved a generic local development estimate for finite closed seam systems:
  cell maps need agree only across seams incident to the chosen finite class.
- Constructed local hinge coordinates and proved exact intrinsic/Euclidean
  distance equality in a small ball around each nonvertex retained-seam point
  with distinct incident faces. This uses the actual route metric and does not
  require a global development.
- Constructed isometries from whole Euclidean balls onto whole intrinsic balls,
  agreeing with both original incident face maps in their outward hinge frames.
- Self-paired edges remain supported by the complex API; their charts need a
  two-patch argument inside one original cell and are not claimed here.
- Verification: selected Mathlib cache fetch and `lake build` pass; the audit
  checks 804 declarations, and `git diff --check` passes.

### 2026-11-09 — hinge neighborhoods and metric localization

- Proved barycentric reconstruction, exact edge membership, and proportionality
  of affine supporting functions vanishing along an edge.
- Proved that outward hinge triangles intersect exactly in their shared edge
  and cover a planar ball around every nonvertex seam point. Chords crossing
  the two sides meet the actual seam, giving intrinsic distance upper bounds
  in a full triangle complex.
- Added a generic short-route localization theorem: a local nonexpanding step
  estimate gives a metric lower bound whenever the radius budget is satisfied.
- Exposed quantitative capped-distance class barriers. Small metric balls at
  a nonvertex seam class use only its two tagged representatives; for distinct
  incident faces the coordinate distances are controlled by intrinsic distance.
- Added retained-face connectivity, ordinary intrinsic metrics for connected
  complexes, and geodesics between all pairs in those complexes.
- Verification: `lake build` audits 741 declarations; `git diff --check` passes.
- The paired-edge chart still needs the local model map and its lower-bound
  application; no full paired-edge chart is claimed at this milestone.

### 2026-11-09 — boundary half-ball charts

- Constructed the affine basis and barycentric coordinate functions for every
  triangle. Characterized carrier/interior membership by coordinate signs.
- Proved that nonvertex edge points have positive endpoint coordinates,
  zero opposite coordinate, and positive clearance from the other two edges.
  This gives an actual local supporting-half-plane description.
- Proved clearance of every nonvertex unpaired-bank point from retained seams.
  Constructed isometries from Euclidean half-balls onto entire intrinsic open
  balls in the cut realization, agreeing with the original bank's face map.
- Verification: `lake build`, the transitive axiom audit, and `git diff --check`.
- Paired-edge and vertex charts remain open.

### 2026-11-09 — geodesics for constructed cut metrics

- Constructed straight paths in triangle cells with exactly their Euclidean
  length. Constructed continuous realization paths from every finite-cost route.
- Defined continuous-path intrinsic distance and proved that it equals the
  constructed route metric when cell distances are realized by cell paths.
- Applied compact shortest-path existence and the endpoint-saturation geodesic
  criterion. Every finite-distance pair in every cut triangle realization is
  joined by an actual constant-speed metric geodesic. No manifold, embedding,
  convexity or global development premise was used.
- Added a chosen-geodesic API after proving existence. It makes no uniqueness
  or cut-locus assertion.
- Verification: `lake build`, the transitive axiom audit, and `git diff --check`.

### 2026-11-09 — compact shortest-path existence

- Generalized the speed-bound length estimate to arbitrary extended
  pseudometric targets. Added metric geodesics and proved their length and
  minimizing properties; an endpoint-distance speed bound forces a geodesic.
- Adapted the reference's natural-parameterization argument to arbitrary metric
  spaces. The newer Mathlib continuity theorem shortens the accumulated-length
  proof. Pauses and zero-length paths are handled.
- Proved compactness of bounded-speed families and lower semicontinuity of
  length. Constructed shortest paths between any rectifiably joined points of
  a compact metric space, with a speed bound by the minimizing length.
- Constructed clopen finite-distance components of extended metric spaces and
  their ordinary metrics. Rectifiable paths lift without changing length.
  This extends shortest-path existence to compact extended metric spaces.
- Verification: targeted constant-speed and Arzela-Ascoli cache fetches;
  `lake build` and `git diff --check` pass. The audit checks 612 declarations.
- The continuous-path/route-distance bridge is the next cut-metric step.

### 2026-11-09 — constructed hinges and continuous path length

- Extended arbitrary closed-segment isometric embeddings to planar rigid
  motions. Constructed edge-line reflection and proved its signed-area reversal.
- Constructed strict outward hinge placements and nonoverlapping developments
  for arbitrary nondegenerate triangles with full-edge isometric pairings.
- Added `Path.eLength` for arbitrary extended pseudometric targets. Proved the
  chord lower bound, reversal and concatenation formulas, Lipschitz bounds and
  invariance under isometries.
- Rechecked the EdgeUnfoldings reference at the same pinned commit. Its generic
  variation arguments are useful for path length and bounded-speed compactness;
  its shortest-branch continuation results inspected here impose additional
  small-polyhedron hypotheses and cannot be used as general convex-surface facts.
- Verification: selected cache fetches for reflection and bounded variation;
  `lake build` and `git diff --check` pass. The audit checks 566 declarations.
- Constant-speed replacement and shortest-path existence are next.

### 2026-11-09 — face-interior metric charts

- Proved quantitative seam-clearance estimates for general metric-cell gluing.
  Compatible single-cell functions extend by constants to other cells; capped
  distances bound intrinsic distance from below.
- Proved that a sufficiently small intrinsic ball consists exactly of the
  corresponding original cell ball and constructed an isometry between them.
- Separated supporting-height lemmas from the development-dependent hinge
  module without changing their statements. Proved all triangle edges lie
  outside the carrier interior and constructed positive clearance radii.
- Constructed Euclidean ball charts at every face-interior point of every cut
  triangle complex, agreeing with its original face map. No global placement or
  manifold conclusion was assumed.
- Verification: `lake build` passes without warnings; 512 declarations pass the
  transitive axiom audit; `git diff --check` passes.
- Paired-edge and vertex charts remain under construction.

### 2026-11-08 — triangle-complex exactness

- Proved that closed-edge isometries preserve endpoints, and distinct edges of
  a nondegenerate triangle intersect only at its corners.
- Proved finiteness of every retained-seam class: corner classes lie in a finite
  set, and a nonvertex point has at most one undirected seam neighbor. The
  relation-theoretic lemma is independent of all metric and triangle geometry.
- Adapted triangle edge pairings to the general closed-seam theorem. Proved
  exactness for all retained-seam sets and an unconditional homeomorphism
  between the original cell quotient and the constructed metric realization.
- Added separation of unpaired bank interiors, while allowing endpoints to be
  identified through other retained seams.
- Verification: selected cache fetch for strict convexity and linear-combination
  tactics; `lake build` and the transitive axiom audit.

### 2026-11-08 — closed-seam separation theorem

- Continued toward the full source-unfolding construction, starting with metric
  exactness for retained seams.
- Constructed capped distance-to-class barriers, including cells with no class
  points. Proved nonexpansion and zero-set characterization for closed classes.
- Proved that finite classes with positive local transport radii give exactness.
  Finite sets and closed seam images supply uniform positive radii.
- Bundled finite closed isometric seams and proved exactness whenever their
  equivalence classes are finite in each original cell. Cells need not be compact.
- Moved the unchanged corner-case lemma into the triangle foundation and added
  compactness of closed triangle edges and their metric subspaces.
- Verification: targeted cache fetch for Hausdorff distance and Lipschitz
  infrastructure, followed by `lake build` and the transitive axiom audit.
- Triangle-specific finite seam-class geometry is the next construction step.

### 2026-11-08 — unglued metric and boundary banks

- Committed seam-quotient and compactness work as `152855f` (320 declarations
  passed the transitive axiom audit).
- Proved the exact no-seam metric formula for arbitrary families: original
  distance within cells, infinity between cells. Proved isometric cell maps and
  exactness for separated cells, including completely cut triangle complexes.
- Added boundary-edge predicates and monotonicity under cutting. The unique
  pairing condition proves that either side of a seam is a boundary edge iff
  that seam is cut.
- Added the two distinct local bank labels, nonexpanding maps of their closed
  edges, and pointwise bank identification when the seam is restored. Bank
  labels do not imply that all their endpoints have distinct metric images.
- Added hinge examples checking bank creation, infinite distance between cut
  cells, and restoration of the original bank pairing.
- Boundary-vertex classes, local manifold charts, and exactness with retained
  seams remain open.
- Verification: `lake build` including examples and the transitive axiom audit;
  `git diff --check`. No additional Mathlib imports needed a cache download.

### 2026-11-08 — seam quotient and compactness

- Committed the verified foundation as `2e73201`.
- Defined the seam quotient independently of the route topology. Proved that
  its points agree exactly along finite seam chains, and constructed its
  continuous surjection to the metric realization.
- Defined metric exactness, characterized it by injectivity of that surjection,
  and proved a criterion using compatible nonexpanding separating coordinates.
- Proved compactness and completeness for finite compact-cell realizations,
  hence for every finite triangle complex and every retained-seam subset.
- Proved that exactness supplies a homeomorphism between the seam quotient and
  the metric realization. Exactness itself for triangle complexes remains open.
- Added a checked example where gluing all nonzero real points also collapses
  zero in the metric quotient, although zero is a separate seam class.
- Verification: selected `lake exe cache get` for `Mathlib.Logic.Relation`,
  `Mathlib.Topology.Separation.Hausdorff`, and
  `Mathlib.Topology.UniformSpace.Cauchy`, then `lake build` including the axiom
  audit; `git diff --check`.

### 2026-11-08

- Set source unfolding of convex polyhedra as the first major target. Added the
  full feature checklist in `PLAN.md`, including the fan nonoverlap equivalence,
  sphere/disk cut criteria, and a separate embedded-graph/Euler development for
  possible Mathlib upstreaming.
- Upgraded to stable Lean/Mathlib 4.35.0; Mathlib is pinned by the manifest to
  `56a005855ea17e0b0958f73ec801ae140b0a1679`. Checked the newer metric gluing,
  extended metric, path-length, and polygon infrastructure before choosing it.
- Replaced the placeholder classification and supplied-metric scaffold with
  proved finite-route distance, constructed family gluing, descent of compatible
  maps, and nonexpansion when restoring cut seams.
- Added nondegenerate triangular cells, full-edge isometric pairings, explicit
  retained seams, and facewise developments with strict opposite-side opening.
  Nonoverlap remains a separate predicate, equivalent to multiplicity at most
  one; it permits boundary contacts.
- Proved that placements descend to the cut metric, that a consistent rigid
  development makes its cell maps isometric, and that opposite-side opening
  gives disjoint interiors at every retained hinge.
- Proved the source-facing radial injectivity criterion. It assumes actual
  radial paths and local injectivity; shortest-path and cut-locus construction
  remain explicit future tasks.
- Added checked examples for single-cell metric recovery, infinite distance
  between disconnected cells, endpoint identifications, a nonoverlapping hinge
  with boundary contact, and coincident developed triangles with multiplicity
  two.
- Added the default `Audit` target. It uses Lean 4.35's public `collectAxioms`
  interface and inspects declarations in every imported unfolding module,
  including dependencies behind opaque exported theorem signatures.
- Verification: the following selected cache fetch succeeded, followed by
  `lake build`. The full build checks the library and its examples; the audit
  checks 287 declarations and permits only `propext`, `Classical.choice`, and
  `Quot.sound`. No `sorry` or `admit` remains in the source.

  ```sh
  lake exe cache get Mathlib.Topology.EMetricSpace.Basic \
    Mathlib.Analysis.InnerProductSpace.PiL2 \
    Mathlib.Analysis.Normed.Operator.Banach \
    Mathlib.Topology.IsLocalHomeomorph \
    Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum \
    Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
  lake build
  ```

- Remaining metric boundary: exactness of the zero-distance quotient for finite
  triangle complexes, quotient topology, compactness, vertex links, and local
  charts. `FacewiseDevelopment` does not yet assert unbranchedness at interior
  vertices. The old scaffold remains available in Git history.

### 2026-06-19

- Verified that the current uncommitted workspace changes are the consolidated
  scaffold developed in this chat.
- Verification: `/Users/sl/.elan/bin/lake exe cache get` succeeded with no
  downloads needed, and `/Users/sl/.elan/bin/lake build` succeeded.  The only
  remaining warning is the intentional `sorry` on
  `Unfoldings.convex_metric_bounded_unfolding_thickness_iff`.
- Prepared the current state for commit.

### 2026-06-06

- Read `/Users/sl/Downloads/CODEX_BRIEF_GraphBasedUnfolding.md`.
- Implemented the simplified graph/cell-structure scaffold directly in
  `Unfoldings/Abstract.lean`.
- Consolidated the project layout so there is only one abstract layer: no root
  `Abstract.lean` and no separate `PolyhedralUnfolding` library.
- Verification after consolidation: `lake exe cache get` succeeded with no
  downloads needed, and `lake build` succeeded.  The only remaining warning is
  the intentional `sorry` on
  `Unfoldings.convex_metric_bounded_unfolding_thickness_iff`.

## Definition Choices

The entries below describe the historical scaffold. Current interfaces and
choices are documented in `README.md` and `PLAN.md`.

- `TriangulatedSurface` is the primary surface model.  It records finite
  vertex, edge, and triangular-face types explicitly rather than using
  `SimpleGraph` alone.
- Edges currently store ordered endpoint pairs with `edgeVerts : E → V × V`.
  This is the simplified first scaffold; it can later be replaced by `Sym2 V`
  or a more structured incidence model.
- Convexity is modeled as nonnegative Gaussian curvature at every vertex:
  `∀ v, 0 ≤ S.curvature v`.
- Cone points are vertices with nonzero curvature.
- Refinements are refinements of the triangulated cell structure, preserving
  old vertex curvature and making all new vertices flat.
- Cut trees live in a refinement, have finite vertex and edge support, are
  intended to be trees, and span all cone points.
- General unfoldings are represented by explicit planar placements of
  triangular pieces.  The hard metric compatibility conditions are placeholders
  for now.
- Thickness is face-counting: `multiplicityAt` counts the unfolded triangular
  face interiors containing a plane point.

## Bridge Notes

- No bridge lemmas yet.

## Stuck Points

- None.

## Cost / Usage

- Not recorded by the local toolchain.

## Times

- Initial scaffold work recorded on 2026-06-06.
