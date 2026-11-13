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
- [ ] Prove projection injectivity for the corresponding intrinsic whole-face
  restriction, excluding distinct intrinsic vertex copies with one planar image.
- [ ] Construct the convex extension used by the arbitrary-rim acute forest.
- [ ] Preserve whole original faces and their original seam names in the extension.
- [ ] Construct and control the actual acute forest and its developed banks.
- [ ] Restrict to an intrinsic original-edge cut disk with one boundary root per tree.
- [ ] Prove global injectivity and the exact simple polygon frontier under a
  mesh-independent tilt threshold.

Finished public results enter the default build and axiom audit. Conditional
lemmas may expose intermediate geometric data; the final theorem must construct
all cuts and developments from roof geometry, acute margin, and tilt alone.
