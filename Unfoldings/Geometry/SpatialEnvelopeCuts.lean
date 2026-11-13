module

public import Unfoldings.Geometry.SpatialEnvelopePairings

/-! Actual auxiliary whole-edge cuts on spatial affine-roof meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialCutsIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Cut exactly those auxiliary seams whose whole geometric edge lies in the given cut set. -/
def retainOutside (cuts : Set Plane) : Set T.pairedComplex.Seam :=
  {s | ¬ (T.projectedTriangle (T.pairedComplex.left s).face).edge
    (T.pairedComplex.left s).edge ⊆ cuts}

/-- Every actual common whole projected edge has its corresponding physical auxiliary seam. -/
theorem pairedComplex_complete {a b : EdgeRef T.Index} (different : a.face ≠ b.face)
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b) :
    ∃ s : T.pairedComplex.Seam,
      (T.pairedComplex.left s = a ∧ T.pairedComplex.right s = b) ∨
      (T.pairedComplex.left s = b ∧ T.pairedComplex.right s = a) :=
  TriangleFamily.pairedComplex_complete T.projectedTriangle T.separated different same

end Unfoldings.SpatialEnvelope.Triangulation
