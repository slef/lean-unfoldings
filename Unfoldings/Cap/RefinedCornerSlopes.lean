module

public import Unfoldings.Cap.RefinementCurvatureSupport
public import Unfoldings.Geometry.Interior

/-! Actual directions along an old edge are tangent to the refined support crease. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- At a nonvertex point of an old edge, the actual refined incident slopes
are one or two old slopes tied along the edge direction. -/
theorem exists_tangent_incidentSlopes_on_old_edge
    {I : Type*} (original : I → Triangle) (conforming : TriangleFamily.Conforming original)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (original i).carrier) (interior (original j).carrier)))
    (slope : I → Plane) (height : I → Plane → ℝ) (parent : Face → I)
    (inside : ∀ f, (K.projectedTriangle f).carrier ⊆ (original (parent f)).carrier)
    (normal_eq : ∀ f, K.normalSlope f = slope (parent f))
    (affine : ∀ i x y, height i x - height i y = -inner ℝ (slope i) (x - y))
    (agree : ∀ i j x, x ∈ (original i).carrier → x ∈ (original j).carrier →
      height i x = height j x)
    (v : C.Vertex Set.univ) (i : I) (e : Fin 3)
    (on_edge : K.projectedVertex v ∈ (original i).edge e)
    (regular : ¬ (original i).IsVertex (K.projectedVertex v)) :
    ∃ a b : Plane,
      (∀ f k, C.vertexOfCorner Set.univ (f, k) = v → K.normalSlope f = a ∨ K.normalSlope f = b) ∧
      inner ℝ (a - b) ((original i).vertex (Triangle.next e) - (original i).vertex e) = 0 := by
  let z := K.projectedVertex v
  have zi := (original i).edge_subset e on_edge
  have hz (f : Face) (k : Fin 3) (eq : C.vertexOfCorner Set.univ (f, k) = v) :
      z ∈ (original (parent f)).carrier := by
    have h := inside f ((K.projectedTriangle f).vertex_mem k)
    rwa [← K.projectedVertex_ofCorner, eq] at h
  obtain ⟨j, candidates⟩ :=
    TriangleFamily.atMostTwo_faces_of_nonvertex original conforming separated i zi regular
  by_cases other : j ≠ i ∧ z ∈ (original j).carrier
  · obtain ⟨different, zj⟩ := other
    obtain ⟨e', d, same_edge, hit⟩ :=
      (conforming i j different.symm z ⟨zi, zj⟩).resolve_left (fun both => regular both.1)
    have same_index : e' = e := by
      by_contra different_edges
      exact regular ((original i).isVertex_of_mem_edges different_edges hit on_edge)
    subst e'
    let x := (original i).vertex e
    let y := (original i).vertex (Triangle.next e)
    have xe : x ∈ (original i).edge e := left_mem_segment ℝ _ _
    have ye : y ∈ (original i).edge e := right_mem_segment ℝ _ _
    have hx := agree i j x ((original i).edge_subset e xe)
      ((original j).edge_subset d (same_edge ▸ xe))
    have hy := agree i j y ((original i).edge_subset e ye)
      ((original j).edge_subset d (same_edge ▸ ye))
    refine ⟨slope i, slope j, ?_, ?_⟩
    · intro f k at_v
      rw [normal_eq]
      exact (candidates (parent f) (hz f k at_v)).imp (congrArg slope) (congrArg slope)
    · change inner ℝ (slope i - slope j) (y - x) = 0
      rw [inner_sub_left]
      linarith only [hx, hy, affine i y x, affine j y x]
  · refine ⟨slope i, slope i, ?_, by rw [sub_self, inner_zero_left]⟩
    intro f k equality
    rw [normal_eq]
    apply Or.inl
    apply congrArg slope
    rcases candidates (parent f) (hz f k equality) with same | same
    · exact same
    by_contra different
    exact other ⟨same ▸ different, same ▸ hz f k equality⟩

/-- In the interior of an old triangle, every refined incident slope
is exactly the old triangle's slope. -/
theorem refined_slope_eq_of_mem_old_interior
    {I : Type*} (original : I → Triangle) (conforming : TriangleFamily.Conforming original)
    (slope : I → Plane) (parent : Face → I)
    (inside : ∀ f, (K.projectedTriangle f).carrier ⊆ (original (parent f)).carrier)
    (normal_eq : ∀ f, K.normalSlope f = slope (parent f))
    (v : C.Vertex Set.univ) (i : I)
    (interior_mem : K.projectedVertex v ∈ interior (original i).carrier)
    (f : Face) (k : Fin 3) (at_v : C.vertexOfCorner Set.univ (f, k) = v) :
    K.normalSlope f = slope i := by
  rw [normal_eq]
  apply congrArg slope
  by_contra different
  have parent_mem := inside f ((K.projectedTriangle f).vertex_mem k)
  rw [← K.projectedVertex_ofCorner, at_v] at parent_mem
  rcases conforming i (parent f) (Ne.symm different) (K.projectedVertex v)
    ⟨interior_subset interior_mem, parent_mem⟩ with vertices | ⟨e, _, _, on_edge⟩
  · obtain ⟨j, at_corner⟩ := vertices.1
    apply (original i).not_mem_interior_of_mem_edge j _ interior_mem
    rw [← at_corner]
    exact left_mem_segment ℝ _ _
  · exact (original i).not_mem_interior_of_mem_edge e on_edge interior_mem

end Unfoldings.ConvexCap
