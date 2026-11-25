module

public import Unfoldings.Roof.CommonPotentialStep

/-! At an interior vertex of a selected roof, a nearby heading is realized by an original edge. -/

@[expose] public section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

open Classical in
/-- The nearest-direction mesh estimate gives an original seam whose whole
segment lies in a selected face. The direction can be chosen independently
of any height potential. -/
theorem exists_selected_seam_near_direction (K : ConvexRoof C) (U : Set Face) {β : ℝ}
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ 2 * β)
    (v : C.Vertex Set.univ) (inside : K.projectedVertex v ∈ interior (K.restrictedCarrier U))
    (direction : Plane) (nonzero : direction ≠ 0) :
    ∃ (w : C.Vertex Set.univ) (s : C.Seam), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
      InnerProductGeometry.angle direction (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
      segment ℝ (K.projectedVertex v) (K.projectedVertex w) ⊆ K.restrictedCarrier U := by
  obtain ⟨f, i, vertex, forward⟩ := exists_mesh_direction_edge
    (fun f : U => K.projectedTriangle f.val) (K.restrictedCarrier U)
    Set.Subset.rfl (K.projectedVertex v) inside
    (fun f present => K.projected_corner_of_vertex_mem v f.val present)
    (fun f j => angles f.val f.property j) direction nonzero
  have original : C.vertexOfCorner Set.univ (f.val, i) = v :=
    K.projectedVertex_injective vertex
  have not_boundary : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f.val, i)) := by
    rw [original]
    exact (K.projectedVertex_mem_interior_iff v).mp
      (interior_mono (K.restrictedCarrier_subset_footprint U) inside)
  have edges := C.exists_seamGraph_link_at_interior_corner f.val i not_boundary
  have finish (j : Fin 3) (s : C.Seam)
      (link : C.seamGraph.IsLink s v (C.vertexOfCorner Set.univ (f.val, j))) (different : j ≠ i)
      (close : InnerProductGeometry.angle direction
        ((K.projectedTriangle f.val).vertex j - K.projectedVertex v) ≤ β) :
      ∃ (w : C.Vertex Set.univ) (s : C.Seam), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
        InnerProductGeometry.angle direction (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
        segment ℝ (K.projectedVertex v) (K.projectedVertex w) ⊆ K.restrictedCarrier U := by
    let w := C.vertexOfCorner Set.univ (f.val, j)
    have endpoint : K.projectedVertex w = (K.projectedTriangle f.val).vertex j :=
      K.projectedVertex_ofCorner f.val j
    refine ⟨w, s, link, ?_, endpoint.symm ▸ close, ?_⟩
    · intro same
      have equal := congrArg K.projectedVertex same
      rw [endpoint, ← vertex] at equal
      exact different ((K.projectedTriangle f.val).affineIndependent_vertices.injective equal)
    · rw [← vertex, endpoint]
      have included := (K.projectedTriangle f.val).convex_carrier.segment_subset
        ((K.projectedTriangle f.val).vertex_mem i) ((K.projectedTriangle f.val).vertex_mem j)
      exact included.trans fun p hp => Set.mem_iUnion.mpr ⟨f, hp⟩
  rcases forward with first | last
  · obtain ⟨s, link⟩ := edges.1
    rw [original] at link
    exact finish (Triangle.next i) s link (by fin_cases i <;> decide) first
  · obtain ⟨s, link⟩ := edges.2
    rw [original] at link
    exact finish (Triangle.next (Triangle.next i)) s link (by fin_cases i <;> decide) last

end Unfoldings.ConvexRoof
