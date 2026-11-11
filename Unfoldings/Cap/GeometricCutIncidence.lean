module

public import Unfoldings.Cap.GeometricCutLabels
public import Unfoldings.Cap.ExtendedCutEmbedding

/-! A geometric cut vertex lying on a geometric edge is one of its actual endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))

theorem original_vertex_on_parent_segment
    (e : {w : C.Vertex Set.univ // w ∉ M.parents.roots}) (w : C.Vertex Set.univ)
    (member : K.projectedVertex w ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val))) :
    w = e.val ∨ w = M.parents.parent e.val := by
  obtain ⟨b, endpoint⟩ := K.vertex_eq_seamEndpoint_of_projected_edge w (M.selection.edge e)
    ((M.parent_segment_eq_original_seam e).subset member)
  rcases M.selection.link e with ⟨first, last⟩ | ⟨first, last⟩
  · cases b
    · exact Or.inl (endpoint.trans first.symm)
    · exact Or.inr (endpoint.trans last.symm)
  · cases b
    · exact Or.inr (endpoint.trans last.symm)
    · exact Or.inl (endpoint.trans first.symm)

/-- Neither independent skirt seeds nor outer tips introduce hidden vertices inside an old
edge. On a radial piece every geometric vertex is its seed or its outer tip. -/
theorem geometric_vertex_on_piece_endpoint (lower : Z < 0) (w : F.GeometricVertex)
    (piece : M.ExtendedCutPiece F)
    (member : F.geometricPosition w ∈ segment ℝ (M.cutPieceFirst F piece)
      (M.cutPieceLast F piece)) :
    F.geometricPosition w = M.cutPieceFirst F piece ∨
      F.geometricPosition w = M.cutPieceLast F piece := by
  cases piece with
  | inl e =>
    change F.geometricPosition w ∈ segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (M.parents.parent e.val)) at member
    cases w with
    | inl w =>
      exact (M.original_vertex_on_parent_segment e w member).imp
        (congrArg K.projectedVertex) (congrArg K.projectedVertex)
    | inr w =>
      cases w with
      | inl c =>
        have old := K.convex_projection.segment_subset (K.projectedVertex_mem_footprint e.val)
          (K.projectedVertex_mem_footprint (M.parents.parent e.val)) member
        have rim : F.componentSeed c.val ∈ frontier K.footprint :=
          (mem_frontier_iff_notMem_interior old).mpr
            (F.component_outside c.val (F.componentTail c.val).seed_mem)
        have equal := M.parent_segment_frontier_endpoint e member rim
        exact (F.independent_seed_ne_original c (M.parents.parent e.val) equal).elim
      | inr c =>
        have old := K.convex_projection.segment_subset (K.projectedVertex_mem_footprint e.val)
          (K.projectedVertex_mem_footprint (M.parents.parent e.val)) member
        exact ((F.componentTail c).boundary.2
          (K.original_footprint_in_clip_interior lower old)).elim
  | inr c =>
    change F.geometricPosition w ∈ (F.componentTail c).carrier at member
    cases w with
    | inl w =>
      have boundary : C.IsBoundaryVertex Set.univ w := by
        by_contra internal
        exact F.component_outside c member ((K.projectedVertex_mem_interior_iff w).mpr internal)
      exact Or.inl (F.rim_vertex_eq_seed c w boundary member)
    | inr w =>
      cases w with
      | inl d =>
        have same := F.component_eq_of_common_mem lower d.val c
          (F.componentTail d.val).seed_mem member
        exact Or.inl (congrArg F.componentSeed same)
      | inr d =>
        have same := F.component_eq_of_common_mem lower d c (F.componentTail d).tip_mem member
        exact Or.inr (congrArg (fun c => (F.componentTail c).tip) same)

variable (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
  K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem geometric_vertex_on_parent_endpoint (w z : F.GeometricVertex)
    (nonroot : z ∉ (M.geometricParents F covered positive small lower).roots)
    (member : F.geometricPosition w ∈ segment ℝ (F.geometricPosition z)
      (F.geometricPosition (M.geometricParent F covered z))) :
    w = z ∨ w = M.geometricParent F covered z := by
  obtain ⟨piece, first, last, _⟩ :=
    M.geometric_parent_piece F covered positive small lower z nonroot
  have inside : F.geometricPosition w ∈ segment ℝ (M.cutPieceFirst F piece)
      (M.cutPieceLast F piece) := by rwa [first, last]
  have endpoint := M.geometric_vertex_on_piece_endpoint F lower w piece inside
  rw [first, last] at endpoint
  exact endpoint.imp (fun equal => F.geometricPosition_injective lower equal)
    (fun equal => F.geometricPosition_injective lower equal)

end Unfoldings.ConvexCap.SectorForest
