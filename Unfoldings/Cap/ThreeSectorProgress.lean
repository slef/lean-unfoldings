module

public import Unfoldings.Cap.ForestExistence
public import Unfoldings.Geometry.ThreeSectorMesh

/-! Actual original-seam progress in every prescribed source-centered acute sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem exists_threeSector_seam_step {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (i : Fin 3)
    (acute : ∀ f j, ((K.projectedTriangle f).affineImage
      (threeSectorCoordinates t i).toAffineMap
        (threeSectorCoordinates_affine_injective nonnegative small i)).cornerAngle j < Real.pi / 2)
    (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    ∃ w s, C.seamGraph.IsLink s v w ∧
      K.projectedVertex w - K.projectedVertex v ∈ strictThreeSector t i := by
  obtain ⟨f, j, center, forward⟩ := exists_mesh_threeSector_edge K.projectedTriangle
    nonnegative small i K.footprint K.footprint_eq_union_projectedTriangles.subset
    (K.projectedVertex v) ((K.projectedVertex_mem_interior_iff v).mpr internal)
    (K.projected_corner_of_vertex_mem v) acute
  have original : C.vertexOfCorner Set.univ (f, j) = v := K.projectedVertex_injective center
  have nonboundary : ¬ C.IsBoundaryVertex Set.univ (C.vertexOfCorner Set.univ (f, j)) := by
    rwa [original]
  have edges := C.exists_seamGraph_link_at_interior_corner f j nonboundary
  rcases forward with first | last
  · obtain ⟨s, link⟩ := edges.1
    rw [original] at link
    exact ⟨_, s, link, first⟩
  · obtain ⟨s, link⟩ := edges.2
    rw [original] at link
    exact ⟨_, s, link, last⟩

/-- One angle-projection threshold is chosen before the entire input mesh. -/
theorem exists_uniform_acute_projection_tilt {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), AcuteMargin (C := C') α → K.TiltBound φ →
          ∀ f j, (K.projectedTriangle f).cornerAngle j < Real.pi / 2 - α / 2 := by
  obtain ⟨φ, bounds, estimate⟩ := Cap.exists_projection_angle_tilt (half_pos positive)
  refine ⟨φ, bounds, fun {Face'} _ {C'} K acute tilt f j => ?_⟩
  have first : (C'.triangle f).vertex (Triangle.next j) ≠ (C'.triangle f).vertex j :=
    (C'.triangle f).affineIndependent_vertices.injective.ne (by fin_cases j <;> decide)
  have last : (C'.triangle f).vertex (Triangle.next (Triangle.next j)) ≠ (C'.triangle f).vertex j :=
    (C'.triangle f).affineIndependent_vertices.injective.ne (by fin_cases j <;> decide)
  have error := K.face_projection_angle_error estimate tilt f _ _ _ first last
  change |(K.projectedTriangle f).cornerAngle j - (C'.triangle f).cornerAngle j| < α / 2 at error
  linarith [(abs_lt.mp error).2, acute f j]

end Unfoldings.ConvexCap
