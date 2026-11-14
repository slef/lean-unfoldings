module

public import Unfoldings.Roof.CompatibleCutEmbedding

/-! Disjoint open pieces also include the complete terminal rays, not just finite parent edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

open Classical in
/-- Open original parent edges, exterior first-contact pieces, and full terminal rays. -/
def openPiece (v : C.Vertex Set.univ) : Set Plane :=
  if root : v ∈ R.original.parents.roots then R.exterior.openPiece ⟨v, root⟩
  else openSegment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v))

theorem openPiece_root (v : {v // v ∈ R.original.parents.roots}) :
    R.openPiece v.val = R.exterior.openPiece v := by
  simp [openPiece, v.property]

theorem openPiece_nonroot {v : C.Vertex Set.univ} (nonroot : v ∉ R.original.parents.roots) :
    R.openPiece v =
      openSegment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) := by
  simp [openPiece, nonroot]

theorem parent_segment_subset_openPiece {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots) :
    openSegment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) ⊆
      R.openPiece v := by
  by_cases root : v ∈ R.original.parents.roots
  · rw [R.openPiece_root ⟨v, root⟩]
    exact R.exterior_segment_subset_openPiece root nonroot
  · rw [R.openPiece_nonroot root]

end Unfoldings.ConvexRoof.CompatiblePotentialRouting

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)

include no_boundary in
theorem compatible_openPiece_avoids_vertices (v w : C.Vertex Set.univ) :
    K.projectedVertex w ∉ R.openPiece v := by
  by_cases root : v ∈ R.original.parents.roots
  · rw [R.openPiece_root ⟨v, root⟩]
    by_cases wr : w ∈ R.original.parents.roots
    · simpa only [R.exterior_points] using R.exterior.openPiece_avoids_roots ⟨v, root⟩ ⟨w, wr⟩
    · have inside : K.projectedVertex w ∈ interior (K.selectedCarrier slopes) := by
        by_contra outside
        exact wr ((Set.ext_iff.mp R.original.roots_eq w).mpr outside)
      exact fun member => Set.disjoint_left.mp
        (K.exterior_piece_disjoint_selected compact nonempty R no_boundary _) member
        (interior_subset inside)
  · rw [R.openPiece_nonroot root, R.original_parent root]
    exact K.seamEmbedding_straight.openSegment_avoids_vertices (R.original.selection.link ⟨v, root⟩)

include no_boundary in
theorem compatible_openPieces_pairwise_disjoint :
    Pairwise (fun v w => Disjoint (R.openPiece v) (R.openPiece w)) := by
  intro v w different
  by_cases vr : v ∈ R.original.parents.roots
  · rw [R.openPiece_root ⟨v, vr⟩]
    by_cases wr : w ∈ R.original.parents.roots
    · rw [R.openPiece_root ⟨w, wr⟩]
      exact R.exterior.openPieces_pairwise_disjoint
        (fun same => different
          (congrArg (fun r : {v // v ∈ R.original.parents.roots} => r.val) same))
    · rw [R.openPiece_nonroot wr]
      exact (K.exterior_piece_disjoint_selected compact nonempty R no_boundary ⟨v, vr⟩).mono
        Set.Subset.rfl ((openSegment_subset_segment ℝ _ _).trans
          (K.compatible_original_segment_selected compact nonempty R wr))
  · rw [R.openPiece_nonroot vr]
    by_cases wr : w ∈ R.original.parents.roots
    · rw [R.openPiece_root ⟨w, wr⟩]
      exact ((K.exterior_piece_disjoint_selected compact nonempty R no_boundary ⟨w, wr⟩).mono
        Set.Subset.rfl ((openSegment_subset_segment ℝ _ _).trans
          (K.compatible_original_segment_selected compact nonempty R vr))).symm
    · rw [R.openPiece_nonroot wr, R.original_parent vr, R.original_parent wr]
      apply K.seamEmbedding_straight.openSegments_disjoint _
        (R.original.selection.link ⟨v, vr⟩) (R.original.selection.link ⟨w, wr⟩)
      intro equal
      exact different (congrArg (fun r : {v // v ∉ R.original.parents.roots} => r.val)
        (R.original.selection.edge_injective equal))

end Unfoldings.ConvexRoof
