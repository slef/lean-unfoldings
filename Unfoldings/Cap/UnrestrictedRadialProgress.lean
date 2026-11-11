module

public import Unfoldings.Cap.Boundary
public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Geometry.MeshHalfplaneProgress
public import Unfoldings.Geometry.RadialSegment

/-! Radial ascent on arbitrary conforming cap triangulations requires no acuteness. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Any open halfplane contains an actual outgoing seam at an interior intrinsic vertex. -/
theorem exists_halfplane_seam_step (w : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ w)
    (height : Plane →ₗ[ℝ] ℝ) (direction : Plane) (positive : 0 < height direction) :
    ∃ z s, C.seamGraph.IsLink s w z ∧
      0 < height (K.projectedVertex z - K.projectedVertex w) := by
  obtain ⟨f, i, center, step⟩ := exists_mesh_halfplane_edge K.projectedTriangle K.footprint
    K.footprint_eq_union_projectedTriangles.subset (K.projectedVertex w)
    ((K.projectedVertex_mem_interior_iff w).mpr internal)
    (K.projected_corner_of_vertex_mem w) height direction positive
  have at_vertex : C.vertexOfCorner Set.univ (f, i) = w := K.projectedVertex_injective center
  have internal_corner : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f, i)) :=
    at_vertex.symm ▸ internal
  have edges := C.exists_seamGraph_link_at_interior_corner f i internal_corner
  rcases step with first | last
  · obtain ⟨s, link⟩ := edges.1
    refine ⟨C.vertexOfCorner Set.univ (f, Triangle.next i), s, at_vertex ▸ link, first⟩
  · obtain ⟨s, link⟩ := edges.2
    refine ⟨C.vertexOfCorner Set.univ (f, Triangle.next (Triangle.next i)), s,
      at_vertex ▸ link, last⟩

/-- Auxiliary flat vertices can be connected by source-distance ascent without imposing an
acute auxiliary mesh or changing any of the original cut choices. -/
theorem exists_unrestricted_radial_step (q : Plane) (w : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ w) :
    ∃ z s, C.seamGraph.IsLink s w z ∧
      dist q (K.projectedVertex w) < dist q (K.projectedVertex z) ∧
        0 ≤ inner ℝ (K.projectedVertex w - q) (K.projectedVertex z - K.projectedVertex w) := by
  let d : Plane := if K.projectedVertex w = q then WithLp.toLp 2 ![1, 0]
    else K.projectedVertex w - q
  have nonzero : d ≠ 0 := by
    by_cases same : K.projectedVertex w = q
    · simp only [d, ite_eq_left same, ne_eq]
      intro zero
      have first := congrArg (fun x : Plane => x 0) zero
      norm_num at first
    · exact (ite_eq_right same).trans_ne (sub_ne_zero.mpr same)
  have positive : 0 < (innerSL ℝ d).toLinearMap d := real_inner_self_pos.mpr nonzero
  obtain ⟨z, s, link, forward⟩ := K.exists_halfplane_seam_step w internal
    (innerSL ℝ d).toLinearMap d positive
  change 0 < inner ℝ d (K.projectedVertex z - K.projectedVertex w) at forward
  have different : K.projectedVertex w ≠ K.projectedVertex z := by
    intro equal
    have zero : K.projectedVertex z - K.projectedVertex w = 0 := sub_eq_zero.mpr equal.symm
    rw [zero, inner_zero_right] at forward
    exact lt_irrefl _ forward
  have outward : 0 ≤ inner ℝ (K.projectedVertex w - q)
      (K.projectedVertex z - K.projectedVertex w) := by
    by_cases same : K.projectedVertex w = q
    · rw [same, sub_self, inner_zero_left]
    · simpa only [d, ite_eq_right same] using forward.le
  refine ⟨z, s, link, ?_, outward⟩
  simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    dist_lineMap_lt_of_inner_nonneg q _ _ outward different (t := 0) (s := 1)
      le_rfl zero_lt_one

end Unfoldings.ConvexCap
