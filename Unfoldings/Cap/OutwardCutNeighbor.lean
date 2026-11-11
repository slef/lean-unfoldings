module

public import Unfoldings.Cap.RadialCutNeighbor
public import Unfoldings.Geometry.LocalRadialSegment

/-! Select a cut seam whose entire oriented segment points radially outward. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Local progress on one fixed incident edge proves the outward scalar product, which is
stronger than strict endpoint ascent and controls every subdivision of the selected edge. -/
theorem exists_outward_cut_seam (retain : Set C.Seam) (q : Plane)
    (v : C.Vertex Set.univ)
    (growth : LocalRadialGrowth
      (⋃ s : {s : C.Seam // s ∉ retain},
        (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge)
      q (K.projectedVertex v)) :
    ∃ w s, s ∉ retain ∧ C.seamGraph.IsLink s v w ∧
      dist q (K.projectedVertex v) < dist q (K.projectedVertex w) ∧
        0 ≤ inner ℝ (K.projectedVertex v - q) (K.projectedVertex w - K.projectedVertex v) := by
  obtain ⟨s, on_piece⟩ := growth.exists_piece
    (fun s : {s : C.Seam // s ∉ retain} =>
      (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge) Set.Subset.rfl
  have at_edge : K.projectedVertex v ∈
      (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge := by
    have near := closure_mono Set.inter_subset_left
      (localRadialGrowth_iff_mem_closure.mp on_piece)
    exact ((K.projectedTriangle (C.left s.val).face).compact_edge
      (C.left s.val).edge).isClosed.closure_eq ▸ near
  obtain ⟨b, at_endpoint⟩ := K.vertex_eq_seamEndpoint_of_projected_edge v s.val at_edge
  let first := K.projectedVertex (C.seamVertex s.val false)
  let last := K.projectedVertex (C.seamVertex s.val true)
  have segment_eq : (K.projectedTriangle (C.left s.val).face).edge (C.left s.val).edge =
      segment ℝ first last := rfl
  rw [segment_eq] at on_piece
  cases b
  · have starts : K.projectedVertex v = first := congrArg K.projectedVertex at_endpoint
    have fixed_piece : LocalRadialGrowth (segment ℝ first last) q first := starts ▸ on_piece
    obtain ⟨different, outward⟩ := (localRadialGrowth_segment_start_iff q first last).mp fixed_piece
    refine ⟨C.seamVertex s.val true, s.val, s.property, Or.inl ⟨at_endpoint, rfl⟩, ?_, ?_⟩
    · have progress := dist_lineMap_lt_of_inner_nonneg q first last outward different
        (t := 0) (s := 1) le_rfl zero_lt_one
      simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, starts] using progress
    · exact starts.symm ▸ outward
  · have starts : K.projectedVertex v = last := congrArg K.projectedVertex at_endpoint
    have fixed_piece : LocalRadialGrowth (segment ℝ last first) q last := by
      rw [segment_symm]
      exact starts ▸ on_piece
    obtain ⟨different, outward⟩ := (localRadialGrowth_segment_start_iff q last first).mp fixed_piece
    refine ⟨C.seamVertex s.val false, s.val, s.property, Or.inr ⟨at_endpoint, rfl⟩, ?_, ?_⟩
    · have progress := dist_lineMap_lt_of_inner_nonneg q last first outward different
        (t := 0) (s := 1) le_rfl zero_lt_one
      simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, starts] using progress
    · exact starts.symm ▸ outward

end Unfoldings.ConvexCap
