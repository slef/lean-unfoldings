# Arbitrary-rim roofs

The target is a simple original-edge unfolding for every sufficiently shallow
acute convex roof over a compact convex polygon. The positive tilt threshold
must depend only on the acute margin. Boundary heights are unrestricted.
No numerical threshold or algorithmic running-time bound is part of this target.

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
  Extending this to each component of a disconnected selection remains below.
- [x] [Cap inclusion](../Unfoldings/Roof/CapBridge.lean) preserves the entire
  original complex, folding, footprint, and tilt bound.

## Remaining proof milestones

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
- [ ] Control the actual developed banks and prove their global separation.
- [ ] Restrict to an intrinsic original-edge cut disk with one boundary root per tree.
- [ ] Prove global injectivity and the exact simple polygon frontier under a
  mesh-independent tilt threshold.

Finished public results enter the default build and axiom audit. Conditional
lemmas may expose intermediate geometric data; the final theorem must construct
all cuts and developments from roof geometry, acute margin, and tilt alone.
