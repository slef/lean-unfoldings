module

public import Unfoldings.Roof.CompatibleCutCarrier
public import Unfoldings.Roof.SeamEmbedding
public import Unfoldings.Convex.ExteriorEmbedding
public import Unfoldings.Geometry.StraightGraphLinks
public import Unfoldings.Geometry.ParentSegments

/-! The compatible finite cut segments form an actual embedded straight rooted forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting U G boundary a β)

theorem exterior_segment_subset_openPiece {v : C.Vertex Set.univ}
    (root : v ∈ R.original.parents.roots) (nonterminal : v ∉ R.parents.roots) :
    openSegment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) ⊆
      R.exterior.openPiece ⟨v, root⟩ := by
  let r : {v // v ∈ R.original.parents.roots} := ⟨v, root⟩
  have not_terminal : r ∉ R.exterior.terminal := fun terminal => nonterminal ⟨root, terminal⟩
  have parent := R.original.parents.attach_parent_root R.exterior.parents R.shared_height r
  change R.parents.parent v = (R.exterior.parents.parent r).val at parent
  have first : K.projectedVertex v = R.exterior.point r := (R.exterior_points r).symm
  have last : K.projectedVertex (R.parents.parent v) = R.exterior.point (R.exterior.next r) := by
    rw [R.exterior_points, parent]
    rfl
  intro x member
  rw [openSegment_eq_image_lineMap] at member
  obtain ⟨t, ht, rfl⟩ := member
  rw [first, last]
  exact R.exterior.open_edge_mem_openPiece ⟨r, not_terminal⟩ ht.1 ht.2

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
theorem exterior_piece_disjoint_selected (r : {v // v ∈ R.original.parents.roots}) :
    Disjoint (R.exterior.openPiece r) (K.selectedCarrier slopes) := by
  apply Set.disjoint_left.mpr
  intro x on_ray selected
  obtain ⟨t, positive, equal⟩ := R.exterior.openPiece_subset_openRay r on_ray
  obtain ⟨f, hf, member⟩ := K.mem_selectedCarrier.mp selected
  exact K.compatible_exterior_ray_avoids_selected compact nonempty R no_boundary r positive f hf
    (equal ▸ member)

include no_boundary in
theorem compatible_parent_segment_avoids_vertices {v : C.Vertex Set.univ}
    (nonroot : v ∉ R.parents.roots) (w : C.Vertex Set.univ) :
    K.projectedVertex w ∉
      openSegment ℝ (K.projectedVertex v) (K.projectedVertex (R.parents.parent v)) := by
  by_cases root : v ∈ R.original.parents.roots
  · intro member
    have on_ray := R.exterior_segment_subset_openPiece root nonroot member
    by_cases wroot : w ∈ R.original.parents.roots
    · have forbidden := R.exterior.openPiece_avoids_roots ⟨v, root⟩ ⟨w, wroot⟩
      rw [R.exterior_points] at forbidden
      exact forbidden on_ray
    · have inside : K.projectedVertex w ∈ interior (K.selectedCarrier slopes) := by
        by_contra outside
        exact wroot ((Set.ext_iff.mp R.original.roots_eq w).mpr outside)
      exact Set.disjoint_left.mp
        (K.exterior_piece_disjoint_selected compact nonempty R no_boundary _)
        on_ray (interior_subset inside)
  · rw [R.original_parent root]
    exact K.seamEmbedding_straight.openSegment_avoids_vertices (R.original.selection.link ⟨v, root⟩)

include no_boundary in
theorem compatible_parent_segments_disjoint :
    Pairwise (fun v w : {v : C.Vertex Set.univ // v ∉ R.parents.roots} =>
      Disjoint (openSegment ℝ (K.projectedVertex v.val)
        (K.projectedVertex (R.parents.parent v.val)))
        (openSegment ℝ (K.projectedVertex w.val)
          (K.projectedVertex (R.parents.parent w.val)))) := by
  intro v w different
  by_cases vr : v.val ∈ R.original.parents.roots
  · by_cases wr : w.val ∈ R.original.parents.roots
    · exact (R.exterior.openPieces_pairwise_disjoint
        (fun same => different (Subtype.ext
          (congrArg (fun r : {v // v ∈ R.original.parents.roots} => r.val) same)))).mono
        (R.exterior_segment_subset_openPiece vr v.property)
        (R.exterior_segment_subset_openPiece wr w.property)
    · exact (K.exterior_piece_disjoint_selected compact nonempty R no_boundary ⟨v.val, vr⟩).mono
        (R.exterior_segment_subset_openPiece vr v.property)
        ((openSegment_subset_segment ℝ _ _).trans
          (K.compatible_original_segment_selected compact nonempty R wr))
  · by_cases wr : w.val ∈ R.original.parents.roots
    · exact ((K.exterior_piece_disjoint_selected compact nonempty R no_boundary ⟨w.val, wr⟩).mono
        (R.exterior_segment_subset_openPiece wr w.property)
        ((openSegment_subset_segment ℝ _ _).trans
          (K.compatible_original_segment_selected compact nonempty R vr))).symm
    · have edges :
          R.original.selection.edge ⟨v.val, vr⟩ ≠ R.original.selection.edge ⟨w.val, wr⟩ := by
        intro same
        exact different (Subtype.ext
          (congrArg (fun r : {v // v ∉ R.original.parents.roots} => r.val)
            (R.original.selection.edge_injective same)))
      rw [R.original_parent vr, R.original_parent wr]
      exact K.seamEmbedding_straight.openSegments_disjoint edges
        (R.original.selection.link ⟨v.val, vr⟩) (R.original.selection.link ⟨w.val, wr⟩)

/-- This contains actual continuous straight edge maps and proves their vertex avoidance
and pairwise disjoint open images. It is not merely an acyclic abstract parent graph. -/
def compatibleCutEmbedding :
    FiniteEmbeddedGraph (C.Vertex Set.univ) {v // v ∉ R.parents.roots} Plane :=
  R.parents.segmentEmbedding K.projectedVertex K.projectedVertex_injective
    (fun _ nonroot w =>
      K.compatible_parent_segment_avoids_vertices compact nonempty R no_boundary nonroot w)
    (K.compatible_parent_segments_disjoint compact nonempty R no_boundary)

theorem compatibleCutEmbedding_straight :
    (K.compatibleCutEmbedding compact nonempty R no_boundary).IsStraight := fun _ _ => rfl

theorem compatibleCutEmbedding_rootedForest :
    (K.compatibleCutEmbedding compact nonempty R no_boundary).graph.IsRootedForest
      R.parents.roots :=
  R.parents.segmentEmbedding_rootedForest K.projectedVertex K.projectedVertex_injective
    (fun _ nonroot w =>
      K.compatible_parent_segment_avoids_vertices compact nonempty R no_boundary nonroot w)
    (K.compatible_parent_segments_disjoint compact nonempty R no_boundary)

end Unfoldings.ConvexRoof
