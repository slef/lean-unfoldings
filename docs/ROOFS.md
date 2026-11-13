# Arbitrary-rim acute-roof theorem

The [main theorem](../Unfoldings/Roof/SimpleEdgeUnfolding.lean),
`ConvexRoof.arbitrary_rim_acute_roof_theorem`, is proved. For each positive
acute margin, it chooses a positive tilt threshold before the entire input
mesh. Every convex roof satisfying those bounds has a simple original-edge
unfolding. Boundary heights are unrestricted.

Import `Unfoldings.Roof.SimpleEdgeUnfolding`. Supply a `ConvexRoof C`, a positive
acute margin, and the resulting tilt bound. The roof model records an actual
spatial folding, upward supporting unit normals, injective vertical projection,
and a convex footprint with nonempty interior. It asks for no cut or development
certificate.

The resulting `U : K.SimpleEdgeUnfolding` provides:

- `retain` and `cutForest`: cuts along original seams, with one boundary root
  per tree.
- `disk`: an actual intrinsic closed-disk homeomorphism.
- `development`, `nonoverlapping`, and `local_isometry`: a facewise rigid
  development, locally isometric on the open disk.
- `injective` and `footprintHomeomorph`: global injectivity, including all
  boundary copies.
- `frontier_isJordanCurve` and `frontier_eq_segments`: a simple polygon frontier
  consisting exactly of finitely many developed bank segments.

The construction includes flat subdivision vertices and roofs with no interior
mesh vertices. It is noncomputable; a numerical threshold and an algorithmic
running-time bound are outside the result.

## Completed foundations

- [x] [Independent cap abstract](../Unfoldings/Cap/Abstract.lean) and
  [checked bridge](../Unfoldings/Cap/AbstractBridge.lean). The default audit checks
  that public definitions and statements depend only on the abstract and Mathlib.
- [x] [Roof inputs](../Unfoldings/Roof/Basic.lean) with supporting upward normals,
  injective projection, and convex footprint; no boundary-height condition.
- [x] [Disk topology](../Unfoldings/Roof/Topology.lean),
  [boundary identification](../Unfoldings/Roof/Boundary.lean), and exact
  [supporting envelope](../Unfoldings/Roof/SupportingEnvelope.lean).
- [x] [Gradient selection escape](../Unfoldings/Roof/GradientSelection.lean):
  monotonicity of directional gradients gives a straight ray from every omitted
  face that avoids every selected face at positive distance.
- [x] [Whole-edge connected selections](../Unfoldings/Roof/RestrictedDisk.lean)
  have an actual closed-disk homeomorphism and Jordan frontier. The proof constructs
  a boundary Jordan subcurve and excludes all additional branches and pinches.
- [x] [Cap inclusion](../Unfoldings/Roof/CapBridge.lean) preserves the entire
  original complex, folding, footprint, and tilt bound.

## Completed construction

- [x] Give a [concrete nonflat cap](../Unfoldings/Examples/Pyramid.lean) with
  actual supporting normals, projection embedding, horizontal rim, and a derived
  positive acute margin. This checks the input model, not a numerical tilt threshold.
- [x] Prove a [geometric disk and Jordan frontier](../Unfoldings/Roof/SelectionComponentDisk.lean)
  for every nonempty whole-edge selection component, including disconnected
  selections whose distinct components touch at vertices.
- [x] Prove [intrinsic disks and projection injectivity](../Unfoldings/Roof/SelectionIntrinsicDisk.lean)
  for every component, excluding distinct intrinsic vertex copies with one planar image.
- [x] Construct a [proper affine extension](../Unfoldings/Roof/TentClips.lean)
  with four new support planes inactive on the original footprint. Its actual
  [normals preserve the chosen tilt budget](../Unfoldings/Roof/TentNormals.lean),
  and sufficiently low horizontal clips contain any prescribed compact region.
- [x] Assemble an [actual auxiliary cap mesh](../Unfoldings/Roof/CompletionMesh.lean)
  with rigid Euclidean triangles, whole-edge spatial seam isometries, injective
  projection, and the original tilt budget. Prescribed finite line constraints
  survive the common geometric refinement.
- [x] Recover [every whole original face isometrically](../Unfoldings/Roof/CompletionOriginalSubdivision.lean)
  from its auxiliary pieces.
- [x] Prove the [correspondence of arbitrary retained original seam classes](../Unfoldings/Roof/CompletionOriginalConforming.lean)
  with the retained auxiliary subdivision, including original boundary vertex copies,
  and transfer nonoverlap in both directions.
- [x] Construct an [original-edge acute forest](../Unfoldings/Roof/SectorForestExistence.lean),
  its actual intrinsic cut disk, and locally isometric development. Sources are
  interior planar points, so roofs without interior mesh vertices are included.
- [x] Construct the [actual outward auxiliary forest](../Unfoldings/Roof/CompletionOutwardForest.lean),
  cover every positive-curvature seed, and derive acute whole-path wedges and
  [uniform developed direction control](../Unfoldings/Roof/CompletionSectorQuadrants.lean).
- [x] Control the [actual developed banks](../Unfoldings/Roof/CompletionRadialWaterfallData.lean)
  and prove [uniform original-face separation](../Unfoldings/Roof/UniformOriginalNonoverlap.lean).
- [x] Restrict to an intrinsic original-edge cut disk with one boundary root per tree.
  The exact metric correspondence preserves the original triangles and seam classes.
- [x] Identify [all closed-face contacts physically](../Unfoldings/Roof/UniformOriginalAllRadiusContact.lean),
  including every radius; derive a uniform intrinsic curvature budget and original-face frames.
- [x] Restore flat descendant cuts and prove [global injectivity](../Unfoldings/Roof/InjectiveEdgeUnfolding.lean)
  and the exact simple polygon frontier under a mesh-independent tilt threshold.

Finished public results enter the default build and axiom audit. Conditional
lemmas may expose intermediate geometric data; the final theorem constructs
all cuts and developments from roof geometry, acute margin, and tilt alone.
