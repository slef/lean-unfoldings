module

public import Unfoldings.Complex.BoundaryFanAgreement
public import Unfoldings.Complex.SeamGraph

/-! A boundary fan depends only on the retained seams incident to its original vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- The germ's corner is one actual endpoint of any seam on its supporting edge. -/
theorem seamGraph_exists_link_of_germEdge (s : C.Seam) (side : Bool) (g : C.Germ)
    (edge : C.germEdge g = C.seamSide s side) :
    ∃ w, C.seamGraph.IsLink s (C.vertexOfCorner Set.univ g.1) w := by
  have tag : C.germOfEndpoint (C.seamSide s side) g.2 = g := by
    rw [← edge, C.germOfEndpoint_germEdge]
  let v (b : Bool) := C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s side) b).1
  have ends := C.seamGraph_side_link s side
  have initial : v g.2 = C.vertexOfCorner Set.univ g.1 :=
    congrArg (fun q : C.Germ => C.vertexOfCorner Set.univ q.1) tag
  refine ⟨v (!g.2), initial ▸ ?_⟩
  cases h : g.2
  · exact ends
  · exact ends.symm

variable {small large : Set C.Seam} (include_cuts : small ⊆ large)
  (vertex : C.Vertex Set.univ)
  (same : ∀ s, (∃ w, C.seamGraph.IsLink s vertex w) → (s ∈ small ↔ s ∈ large))

include same in
/-- All unpaired literal banks at this original vertex remain unpaired in either set. -/
theorem isBoundaryEdge_of_incidentSeams (g : C.Germ)
    (original : C.vertexOfCorner Set.univ g.1 = vertex)
    (bank : C.IsBoundaryEdge small (C.germEdge g)) :
    C.IsBoundaryEdge large (C.germEdge g) := by
  rintro ⟨s, keeps, edge | edge⟩
  · have inc := C.seamGraph_exists_link_of_germEdge s false g edge
    exact bank ⟨s, (same s (original ▸ inc)).mpr keeps, Or.inl edge⟩
  · have inc := C.seamGraph_exists_link_of_germEdge s true g edge
    exact bank ⟨s, (same s (original ▸ inc)).mpr keeps, Or.inr edge⟩

include include_cuts same in
/-- Restoring seams away from the specified original vertex leaves its whole boundary fan angle. -/
theorem totalAngle_eq_of_incidentSeams (p : C.BoundaryEnd small) (q : C.BoundaryEnd large)
    (anchor : p.val = q.val) (original : C.vertexOfCorner Set.univ p.val.1 = vertex) :
    C.totalAngle small (C.boundaryEndVertex small p) =
      C.totalAngle large (C.boundaryEndVertex large q) := by
  have mate_at : C.vertexOfCorner Set.univ (C.boundaryMate small p).val.1 = vertex :=
    (congrArg (C.vertexForgetCuts (Set.subset_univ small))
      (C.boundaryMate_spec small p).2).trans original
  have kept_first := C.isBoundaryEdge_of_incidentSeams vertex same p.val original p.property
  have kept_last := C.isBoundaryEdge_of_incidentSeams vertex same (C.boundaryMate small p).val
    mate_at (C.boundaryMate small p).property
  have forget : C.vertexForgetCuts include_cuts (C.boundaryEndVertex small p) =
      C.boundaryEndVertex large q :=
    congrArg (fun g : C.Germ => C.vertexOfCorner large g.1) anchor
  classical
  simp only [totalAngle, ← forget,
    C.boundary_fan_corners_iff include_cuts p kept_first kept_last]

end Unfoldings.TriangleComplex
