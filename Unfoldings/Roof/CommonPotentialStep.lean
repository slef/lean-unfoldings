module

public import Unfoldings.Convex.AnnularProgress
public import Unfoldings.Geometry.MeshDirectionProgress
public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Roof.Boundary
public import Unfoldings.Complex.SeamGraph

/-! Quantitative common-potential progress along actual original edges of selected patches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
theorem restrictedCarrier_subset_footprint (U : Set Face) :
    K.restrictedCarrier U ⊆ K.footprint := by
  intro p hp
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hp
  rw [K.footprint_eq_union_projectedTriangles]
  exact Set.mem_iUnion.mpr ⟨f.val, hf⟩

open Classical in
/-- No convexity of the selected footprint is needed. Only its original incident triangles
need the stated corner bound; the requested direction comes from the actual common potential. -/
theorem exists_commonPotential_seam_step (U : Set Face) (E : SlopeEnvelope) {a β : ℝ}
    (positive : 0 < a) (beta : 0 ≤ β) (acute : β ≤ Real.pi / 2)
    (lower : ∀ p ∈ E.slopes, a ≤ ‖p‖)
    (angles : ∀ f ∈ U, ∀ i, (K.projectedTriangle f).cornerAngle i ≤ 2 * β)
    (v : C.Vertex Set.univ) (inside : K.projectedVertex v ∈ interior (K.restrictedCarrier U)) :
    ∃ (w : C.Vertex Set.univ) (s : C.Seam) (p : Plane), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
      E.Active (K.projectedVertex v) p ∧
      InnerProductGeometry.angle p (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
      (a * Real.cos β) * ‖K.projectedVertex w - K.projectedVertex v‖ ≤
        E.height (K.projectedVertex w) - E.height (K.projectedVertex v) ∧
      K.projectedVertex w ∈ K.restrictedCarrier U := by
  obtain ⟨p, active⟩ := E.exists_active (K.projectedVertex v)
  have norm_lower := lower p active.1
  have pne : p ≠ 0 := by intro zero; rw [zero, norm_zero] at norm_lower; linarith
  obtain ⟨f, i, vertex, forward⟩ := exists_mesh_direction_edge
    (fun f : {f : Face // f ∈ U} => K.projectedTriangle f.val) (K.restrictedCarrier U)
    Set.Subset.rfl (K.projectedVertex v) inside
    (fun f present => K.projected_corner_of_vertex_mem v f.val present)
    (fun f i => angles f.val f.property i) p pne
  have original : C.vertexOfCorner Set.univ (f.val, i) = v :=
    K.projectedVertex_injective vertex
  have nonboundary : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f.val, i)) := by
    rw [original]
    exact (K.projectedVertex_mem_interior_iff v).mp
      (interior_mono (K.restrictedCarrier_subset_footprint U) inside)
  have edges := C.exists_seamGraph_link_at_interior_corner f.val i nonboundary
  have finish (j : Fin 3) (s : C.Seam)
      (link : C.seamGraph.IsLink s v (C.vertexOfCorner Set.univ (f.val, j)))
      (different : j ≠ i)
      (angle : InnerProductGeometry.angle p
        ((K.projectedTriangle f.val).vertex j - K.projectedVertex v) ≤ β) :
      ∃ (w : C.Vertex Set.univ) (s : C.Seam) (p : Plane), C.seamGraph.IsLink s v w ∧ w ≠ v ∧
        E.Active (K.projectedVertex v) p ∧
        InnerProductGeometry.angle p (K.projectedVertex w - K.projectedVertex v) ≤ β ∧
        (a * Real.cos β) * ‖K.projectedVertex w - K.projectedVertex v‖ ≤
          E.height (K.projectedVertex w) - E.height (K.projectedVertex v) ∧
        K.projectedVertex w ∈ K.restrictedCarrier U := by
    let w := C.vertexOfCorner Set.univ (f.val, j)
    have endpoint : K.projectedVertex w = (K.projectedTriangle f.val).vertex j :=
      K.projectedVertex_ofCorner f.val j
    have ne : K.projectedVertex w - K.projectedVertex v ≠ 0 := by
      rw [endpoint, ← vertex]
      exact sub_ne_zero.mpr ((K.projectedTriangle f.val).affineIndependent_vertices.injective.ne
        different)
    have close : InnerProductGeometry.angle p (K.projectedVertex w - K.projectedVertex v) ≤ β :=
      endpoint.symm ▸ angle
    have step := SlopeEnvelope.direction_progress positive beta acute norm_lower ne close
    have support := E.active_support active (K.projectedVertex w)
    rw [inner_sub_right] at step support
    refine ⟨w, s, p, link, ?_, active, close, by linarith, ?_⟩
    · intro same
      exact ne (sub_eq_zero.mpr (congrArg K.projectedVertex same))
    · exact Set.mem_iUnion.mpr ⟨f, endpoint.symm ▸ (K.projectedTriangle f.val).vertex_mem j⟩
  rcases forward with first | last
  · obtain ⟨s, link⟩ := edges.1
    rw [original] at link
    exact finish (Triangle.next i) s link (by fin_cases i <;> decide) first
  · obtain ⟨s, link⟩ := edges.2
    rw [original] at link
    exact finish (Triangle.next (Triangle.next i)) s link (by fin_cases i <;> decide) last

end Unfoldings.ConvexRoof
