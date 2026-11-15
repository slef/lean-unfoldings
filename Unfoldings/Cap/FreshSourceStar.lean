module

public import Unfoldings.Complex.ProcessedParentCuts
public import Unfoldings.Cap.SingleCutStar

/-! An intermediate fresh source has one actual cut copy carrying its entire original star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ) (fresh : vertex ∉ frontier.processed)

include K roots fresh in
/-- Cutting the next fresh branch opens just the original parent seam at its source.
Its full actual corner star becomes one boundary copy, even if the final forest has children
there. Its intrinsic angle is exactly the original angle, independently of curvature. -/
theorem exists_fresh_source_cut_star :
    let retain := C.processedParentRetain S (frontier.process vertex)
    ∃ w : C.Vertex retain, C.IsBoundaryVertex retain w ∧
      C.vertexForgetCuts (Set.subset_univ retain) w = vertex ∧
      C.totalAngle retain w = C.totalAngle Set.univ vertex ∧
      ∀ z : C.Vertex retain, C.vertexForgetCuts (Set.subset_univ retain) z = vertex → z = w := by
  dsimp only
  have nonroot : vertex ∉ P.roots := fun root => fresh (frontier.roots root)
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [roots, TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using nonroot
  let retain := C.processedParentRetain S (frontier.process vertex)
  let edge := S.edge ⟨vertex, nonroot⟩
  obtain ⟨p, pedge⟩ := exists_linkGerm_at_seam (S.link ⟨vertex, nonroot⟩)
  have preserves := K.preserves_other_link_pairs_of_single_cut retain edge p pedge
    (C.unique_processed_cut_at_new_source S frontier vertex fresh nonroot)
  have cut : edge ∉ retain := C.parent_cut_at_new_source S frontier vertex nonroot
  have boundary : C.IsBoundaryEdge retain (C.germEdge p.val) := by
    rw [pedge, C.isBoundaryEdge_left_iff]
    exact cut
  refine ⟨C.vertexOfCorner retain p.val.1,
    C.isBoundaryVertex_of_boundary_germ retain p.val boundary, p.property,
    C.totalAngle_of_single_link_cut retain internal p preserves, ?_⟩
  intro z original
  exact C.unique_vertex_copy_of_single_link_cut retain internal p preserves z original

end Unfoldings.ConvexCap
