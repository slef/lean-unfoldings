module

public import Unfoldings.Geometry.TriangleWithEdge
public import Unfoldings.Geometry.WholeEdgeSubdivision
public import Unfoldings.Geometry.SpatialEnvelopeTriangles

/-! Whole-edge coverage of arbitrary finite prescribed segments on a physical roof mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u

variable {A : Type u} (first last : A → Plane) (different : ∀ a, first a ≠ last a)

def segmentEquations (i : A × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord i.2

theorem segmentEquations_ne_zero (i : A × Fin 3) :
    segmentEquations first last different i ≠ 0 :=
  (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord_ne_zero i.2

namespace SpatialEnvelope.ConstrainedTriangulation

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : ConstrainedTriangulation family (segmentEquations first last different) Z)

/-- Including the other two supporting lines prevents edges extending past either endpoint. -/
theorem prescribed_segment_eq_union_subedges (a : A)
    (first_member : first a ∈ clip family Z) (last_member : last a ∈ clip family Z) :
    segment ℝ (first a) (last a) =
      ⋃ e : {e : T.Index × Fin 3 //
          (T.projectedTriangle e.1).edge e.2 ⊆ segment ℝ (first a) (last a)},
        (T.projectedTriangle e.val.1).edge e.val.2 := by
  let := T.finite
  let U := triangleWithEdge (first a) (last a) (different a)
  have cover : U.edge 0 ⊆ ⋃ i, (T.projectedTriangle i).carrier :=
    ((AffineEnvelope.convex_clip _ Z).segment_subset first_member last_member).trans T.cover.subset
  exact TriangleFamily.edge_eq_union_subedges T.projectedTriangle U 0 cover
    (fun i k => T.signs i (a, k)) (fun i k p member => T.constrained i p member (a, k))

end SpatialEnvelope.ConstrainedTriangulation
end Unfoldings
