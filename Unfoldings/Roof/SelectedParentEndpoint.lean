module

public import Unfoldings.Roof.PotentialCutForest
public import Unfoldings.Geometry.PolygonalChain

/-! A literal selected roof edge meets original vertices only at its own endpoints. -/

@[expose] public section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

include S

/-- Conformity excludes any third original vertex from a closed selected parent segment. -/
theorem selectedParentSegment_vertex (e : {v : C.Vertex Set.univ // v ∉ P.roots})
    (w : C.Vertex Set.univ)
    (member : K.projectedVertex w ∈
      segment ℝ (K.projectedVertex e.val) (K.projectedVertex (P.parent e.val))) :
    w = e.val ∨ w = P.parent e.val := by
  have link := S.link e
  have edge_eq : segment ℝ (K.projectedVertex e.val) (K.projectedVertex (P.parent e.val)) =
      (K.projectedTriangle (C.left (S.edge e)).face).edge (C.left (S.edge e)).edge := by
    rcases link with ⟨first, last⟩ | ⟨first, last⟩
    · rw [last, first]
      rfl
    · rw [last, first]
      exact segment_symm ℝ _ _
  obtain ⟨side, hw⟩ := K.vertex_eq_seamEndpoint_of_projected_edge w (S.edge e) (edge_eq ▸ member)
  rcases link with ⟨first, last⟩ | ⟨first, last⟩
  · cases side
    · exact Or.inl (hw.trans first.symm)
    · exact Or.inr (hw.trans last.symm)
  · cases side
    · exact Or.inr (hw.trans last.symm)
    · exact Or.inl (hw.trans first.symm)

/-- Recover the exact parameter as well as the original vertex at a selected parent endpoint. -/
theorem selectedParentLineMap_eq_vertex (e : {v : C.Vertex Set.univ // v ∉ P.roots})
    (w : C.Vertex Set.univ) (t : unitInterval)
    (equal : AffineMap.lineMap (K.projectedVertex e.val) (K.projectedVertex (P.parent e.val))
      t.val = K.projectedVertex w) :
    (e.val = w ∧ t = 0) ∨ (P.parent e.val = w ∧ t = 1) := by
  have member : K.projectedVertex w ∈
      segment ℝ (K.projectedVertex e.val) (K.projectedVertex (P.parent e.val)) := by
    rw [segment_eq_image_lineMap]
    exact ⟨t.val, t.property, equal⟩
  have other : K.projectedVertex e.val ≠ K.projectedVertex (P.parent e.val) := by
    intro same
    have fixed := congrArg P.height (K.projectedVertex_injective same)
    exact (ne_of_lt (P.ascending _ e.property)) fixed
  rcases K.selectedParentSegment_vertex S e w member with first | last
  · refine Or.inl ⟨first.symm, Subtype.ext (AffineMap.lineMap_injective ℝ other ?_)⟩
    rw [equal, first, Set.Icc.coe_zero, AffineMap.lineMap_apply_zero]
  · refine Or.inr ⟨last.symm, Subtype.ext (AffineMap.lineMap_injective ℝ other ?_)⟩
    rw [equal, last, Set.Icc.coe_one, AffineMap.lineMap_apply_one]

end Unfoldings.ConvexRoof
