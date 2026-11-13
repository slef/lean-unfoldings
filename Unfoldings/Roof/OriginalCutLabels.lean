module

public import Unfoldings.Roof.ParentSegments
public import Unfoldings.Roof.Boundary
public import Unfoldings.Roof.ProjectedSeamEndpoints
public import Unfoldings.Roof.ProjectedSeamUnique

/-! Actual original cut segments have consistent tree labels at every geometric contact. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedVertex_mem_footprint (w : C.Vertex Set.univ) :
    K.projectedVertex w ∈ K.footprint := (K.toFootprint (C.vertexPoint Set.univ w)).property

namespace SectorForest

variable {K} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)

/-- Both actual seam endpoints have the same selected-tree root as their child selector. -/
theorem seamEndpoint_root_eq (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) (b : Bool) :
    M.parents.root (C.seamVertex (M.selection.edge e) b) = M.parents.root e.val := by
  have same := M.parents.root_eq_of_ancestor (M.parents.ancestor_parent e.val)
  rcases M.selection.link e with ⟨first, last⟩ | ⟨first, last⟩
  · cases b
    · exact congrArg M.parents.root first.symm
    · exact (congrArg M.parents.root last.symm).trans same.symm
  · cases b
    · exact (congrArg M.parents.root last.symm).trans same.symm
    · exact congrArg M.parents.root first.symm

/-- The geometric network cannot identify points from distinct selected original trees. -/
theorem parent_segments_root_eq_of_intersection
    (a b : {w : C.Vertex Set.univ // w ∉ M.parents.roots})
    {p : Plane}
    (first : p ∈ segment ℝ (K.projectedVertex a.val)
      (K.projectedVertex (M.parents.parent a.val)))
    (last : p ∈ segment ℝ (K.projectedVertex b.val)
      (K.projectedVertex (M.parents.parent b.val))) :
    M.parents.root a.val = M.parents.root b.val := by
  have first_edge := (M.parent_segment_eq_original_seam a).subset first
  have last_edge := (M.parent_segment_eq_original_seam b).subset last
  by_cases vertex : ∃ w : C.Vertex Set.univ, K.projectedVertex w = p
  · obtain ⟨w, at_p⟩ := vertex
    obtain ⟨i, first_endpoint⟩ := K.vertex_eq_seamEndpoint_of_projected_edge w
      (M.selection.edge a) (at_p.symm ▸ first_edge)
    obtain ⟨j, last_endpoint⟩ := K.vertex_eq_seamEndpoint_of_projected_edge w
      (M.selection.edge b) (at_p.symm ▸ last_edge)
    have first_root := (congrArg M.parents.root first_endpoint).trans (M.seamEndpoint_root_eq a i)
    have last_root := (congrArg M.parents.root last_endpoint).trans (M.seamEndpoint_root_eq b j)
    exact first_root.symm.trans last_root
  · have regular (f : Face) (i : Fin 3) : p ≠ (K.projectedTriangle f).vertex i := by
      intro equal
      exact vertex ⟨C.vertexOfCorner Set.univ (f, i), equal.symm⟩
    have same := K.projected_seam_unique_at_regular_point (M.selection.edge a) (M.selection.edge b)
      first_edge last_edge regular
    exact congrArg (fun e => M.parents.root e.val) (M.selection.edge_injective same)

/-- An original parent segment meets the old rim only at its parent endpoint. -/
theorem parent_segment_frontier_endpoint
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) {p : Plane}
    (member : p ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val)))
    (rim : p ∈ frontier K.footprint) : p = K.projectedVertex (M.parents.parent e.val) := by
  have child_internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
  have inside := (K.projectedVertex_mem_interior_iff e.val).mpr child_internal
  obtain ⟨s, bounds, at_p⟩ := (segment_eq_image_lineMap ℝ _ _).subset member
  have last : s = 1 := by
    by_contra different
    have before : s < 1 := lt_of_le_of_ne bounds.2 different
    have interior_point := K.convex_projection.combo_interior_closure_mem_interior inside
      (subset_closure (K.projectedVertex_mem_footprint (M.parents.parent e.val)))
      (sub_pos.mpr before) bounds.1 (show (1 - s) + s = 1 by ring)
    have same : (1 - s) • K.projectedVertex e.val +
        s • K.projectedVertex (M.parents.parent e.val) = p := by
      rw [← at_p, AffineMap.lineMap_apply_module']
      module
    exact rim.2 (same ▸ interior_point)
  exact at_p.symm.trans (last ▸ AffineMap.lineMap_apply_one _ _)

end SectorForest
end Unfoldings.ConvexRoof
