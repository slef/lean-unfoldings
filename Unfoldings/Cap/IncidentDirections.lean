module

public import Unfoldings.Cap.GermSupports
public import Unfoldings.Geometry.CornerSpan

/-! The closed projected corner cones cover every direction at an interior vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The coefficients refer to actual incident original edge germs. -/
theorem exists_incident_direction_combination (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint) (q : Plane) :
    ∃ (p : C.LinkGerm Set.univ v) (t a b : ℝ), 0 < t ∧ 0 ≤ a ∧ 0 ≤ b ∧
      t • q = a • K.projectedGermRay p +
        b • K.projectedGermRay (C.linkTurn Set.univ v p) := by
  have star := eventually_piece_contains_center (fun f => (K.projectedTriangle f).carrier)
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed) (K.projectedVertex v)
  have near : {z | z ∈ K.footprint ∧ ∀ f, z ∈ (K.projectedTriangle f).carrier →
      K.projectedVertex v ∈ (K.projectedTriangle f).carrier} ∈ 𝓝 (K.projectedVertex v) := by
    filter_upwards [star, isOpen_interior.mem_nhds inside] with z incidence interior
    exact ⟨interior_subset interior, incidence⟩
  obtain ⟨t, ht, present, incidence⟩ := exists_positive_ray_mem (K.projectedVertex v) q _ near
  obtain ⟨f, face⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset present)
  obtain ⟨i, equal⟩ := K.projected_corner_of_vertex_mem v f (incidence f face)
  have original : C.vertexOfCorner Set.univ (f, i) = v := K.projectedVertex_injective equal
  let p : C.LinkGerm Set.univ v := ⟨((f, i), false), original⟩
  let T := K.projectedTriangle f
  let z := K.projectedVertex v + t • q
  have coordinates := T.carrier_eq_nonneg_coord.le face
  refine ⟨p, t, T.coord (Triangle.next i) z, T.coord (Triangle.next (Triangle.next i)) z,
    ht, coordinates _, coordinates _, ?_⟩
  have reconstructed := T.reconstruct_corner i z
  have subtract := congrArg (fun x : Plane => x - T.vertex i) reconstructed
  simp only [Triangle.cornerCombination, add_sub_cancel_right] at subtract
  rw [equal] at subtract
  change t • q = T.coord (Triangle.next i) z •
    (T.vertex (Triangle.next i) - K.projectedVertex v) +
    T.coord (Triangle.next (Triangle.next i)) z •
      (T.vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v)
  simpa only [z, add_sub_cancel_left] using subtract.symm

/-- No nonzero linear form can be strictly positive on all outgoing projected germs. -/
theorem not_all_projected_germs_positive (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint) (f : Plane →ₗ[ℝ] ℝ) :
    ¬ (∀ p : C.LinkGerm Set.univ v, 0 < f (K.projectedGermRay p)) := by
  intro positive
  obtain ⟨⟨face, i⟩, original⟩ := C.vertexOfCorner_surjective Set.univ v
  let p : C.LinkGerm Set.univ v := ⟨((face, i), false), original⟩
  obtain ⟨r, t, a, b, ht, ha, hb, expression⟩ :=
    K.exists_incident_direction_combination v inside (-K.projectedGermRay p)
  have image := congrArg f expression
  rw [map_smul, map_neg, map_add, map_smul, map_smul] at image
  simp only [smul_eq_mul] at image
  have left := mul_neg_of_pos_of_neg ht (neg_neg_of_pos (positive p))
  have right := add_nonneg (mul_nonneg ha (positive r).le)
    (mul_nonneg hb (positive (C.linkTurn Set.univ v r)).le)
  linarith

end Unfoldings.ConvexCap
