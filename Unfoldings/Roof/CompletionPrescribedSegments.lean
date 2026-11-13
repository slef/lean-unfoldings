module

public import Unfoldings.Roof.CompletionRefinement
public import Unfoldings.Roof.CompletionOriginalPieces
public import Unfoldings.Geometry.TriangleWithEdge
public import Unfoldings.Geometry.WholeEdgeSubdivision

/-! Mesh prescribed closed segments while retaining all original roof edge constraints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {A : Type} (first last : A → Plane) (different : ∀ a, first a ≠ last a)

def originalAndSegmentEquations : (Face × Fin 3) ⊕ (A × Fin 3) → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim K.originalEdgeEquations
    (fun i => (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord i.2)

theorem originalAndSegmentEquations_ne_zero (i : (Face × Fin 3) ⊕ (A × Fin 3)) :
    K.originalAndSegmentEquations first last different i ≠ 0 := by
  cases i with
  | inl i => exact K.originalEdgeEquations_ne_zero i
  | inr i => exact (triangleWithEdge (first i.1) (last i.1) (different i.1)).coord_ne_zero i.2

namespace CompletionMesh

variable {K first last different} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region (K.originalAndSegmentEquations first last different))

/-- Forget only the extra constraint labels; keep the identical physical mesh and support data. -/
def originalPart : K.CompletionMesh φ region K.originalEdgeEquations where
  tentHeight := L.tentHeight
  level := L.level
  mesh := {
    toTriangulation := L.mesh.toTriangulation
    signs i j := L.mesh.signs i (Sum.inl j)
    constrained i p member j := L.mesh.constrained i p member (Sum.inl j) }
  conforming := L.conforming
  covers := L.covers
  unchanged := L.unchanged

/-- Endpoint constraints ensure coverage by whole fine edges, including both endpoints. -/
theorem segment_eq_union_subedges (a : A)
    (first_member : first a ∈ SpatialEnvelope.clip
      (K.completionPlanes L.tentHeight (Real.sin φ / 2)) L.level)
    (last_member : last a ∈ SpatialEnvelope.clip
      (K.completionPlanes L.tentHeight (Real.sin φ / 2)) L.level) :
    segment ℝ (first a) (last a) =
      ⋃ e : {e : L.mesh.Index × Fin 3 //
          (L.mesh.projectedTriangle e.1).edge e.2 ⊆ segment ℝ (first a) (last a)},
        (L.mesh.projectedTriangle e.val.1).edge e.val.2 := by
  let := L.mesh.finite
  let U := triangleWithEdge (first a) (last a) (different a)
  have cover : U.edge 0 ⊆ ⋃ i, (L.mesh.projectedTriangle i).carrier :=
    ((AffineEnvelope.convex_clip _ L.level).segment_subset first_member last_member).trans
      L.mesh.cover.subset
  exact TriangleFamily.edge_eq_union_subedges L.mesh.projectedTriangle U 0 cover
    (fun i k => L.mesh.signs i (Sum.inr (a, k)))
    (fun i k p member => L.mesh.constrained i p member (Sum.inr (a, k)))

end CompletionMesh
end Unfoldings.ConvexRoof
