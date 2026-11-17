module

public import Unfoldings.Roof.ProjectedRemovedSeams
public import Unfoldings.Roof.SeamSegments
public import Unfoldings.Roof.PotentialCutForest
public import Unfoldings.Complex.ProcessedParentCuts

/-! Processed original parent segments lie in the actual projected removed-seam carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- An original removed seam retains its complete closed projected segment. -/
theorem projected_link_segment_subset_removed {retain : Set C.Seam} {s : C.Seam}
    (removed : s ∉ retain) {v w : C.Vertex Set.univ} (link : C.seamGraph.IsLink s v w) :
    segment ℝ (K.projectedVertex v) (K.projectedVertex w) ⊆
      K.removedProjectedSeamCarrier retain := by
  rw [K.projected_link_segment link]
  have edge : (K.projectedTriangle (C.left s).face).edge (C.left s).edge =
      K.projectFace (C.left s).face '' (C.triangle (C.left s).face).edge (C.left s).edge :=
    (C.triangle (C.left s).face).affineImage_edge _ _ _
  intro p member
  obtain ⟨x, on_edge, rfl⟩ := edge.subset member
  exact K.removed_edge_mem_projected_removed retain s removed ⟨x, on_edge⟩

namespace PotentialCutForest

variable {K} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)

/-- Processing an original selector cuts the entire original closed parent segment. -/
theorem processed_parent_segment_subset (S : R.parents.ParentFrontier)
    (v : C.Vertex Set.univ) (nonroot : v ∉ R.parents.roots) (processed : v ∈ S.processed) :
    segment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) ⊆
      K.removedProjectedSeamCarrier (C.processedParentRetain R.selection S) := by
  apply K.projected_link_segment_subset_removed
    (s := R.selection.edge ⟨v, nonroot⟩) ?_ (R.selection.link ⟨v, nonroot⟩)
  exact (C.not_mem_processedParentRetain_iff R.selection S _).mpr
    ⟨⟨v, nonroot⟩, processed, rfl⟩

end PotentialCutForest
end Unfoldings.ConvexRoof
