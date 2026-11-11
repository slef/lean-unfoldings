module

public import Unfoldings.Cap.DegenerateNormalCurvature
public import Unfoldings.Geometry.ConformingPointMultiplicity

/-! Refinements subordinate to conforming supports create no curvature away from old corners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {I : Type*} (original : I → Triangle)
  (conforming : TriangleFamily.Conforming original)
  (separated : Pairwise (fun i j =>
    Disjoint (interior (original i).carrier) (interior (original j).carrier)))
  (slope : I → Plane) (parent : Face → I)
  (inside : ∀ f, (K.projectedTriangle f).carrier ⊆ (original (parent f)).carrier)
  (normal_eq : ∀ f, K.normalSlope f = slope (parent f))

include conforming separated inside normal_eq in
/-- Every new vertex away from old corners is a planar or crease subdivision and is flat. -/
theorem interiorCurvature_eq_zero_off_parent_corners
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (v : C.Vertex Set.univ)
    (away : ∀ i, ¬ (original i).IsVertex (K.projectedVertex v)) :
    C.interiorAngularDefect Set.univ v = 0 := by
  have point_member (f : Face) (i : Fin 3) (at_vertex : C.vertexOfCorner Set.univ (f, i) = v) :
      K.projectedVertex v ∈ (original (parent f)).carrier := by
    have corner := (K.projectedTriangle f).vertex_mem i
    have equal : (K.projectedTriangle f).vertex i = K.projectedVertex v :=
      (K.projectedVertex_ofCorner f i).symm.trans (congrArg K.projectedVertex at_vertex)
    exact inside f (equal ▸ corner)
  obtain ⟨⟨f, i⟩, at_vertex⟩ := C.vertexOfCorner_surjective Set.univ v
  obtain ⟨other, only_two⟩ := TriangleFamily.atMostTwo_faces_of_nonvertex original conforming
    separated (parent f) (point_member f i at_vertex) (away (parent f))
  apply K.interiorCurvature_eq_zero_of_two_incidentSlopes height v (slope (parent f)) (slope other)
  intro g j at_vertex_g
  rw [normal_eq]
  exact (only_two (parent g) (point_member g j at_vertex_g)).imp
    (congrArg slope) (congrArg slope)

include conforming separated inside normal_eq in
/-- Positive refined curvature is supported on actual old triangle corners. -/
theorem exists_parent_corner_of_positive_curvature
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (v : C.Vertex Set.univ)
    (curved : 0 < C.interiorAngularDefect Set.univ v) :
    ∃ i j, (original i).vertex j = K.projectedVertex v := by
  by_contra absent
  have away (i : I) : ¬ (original i).IsVertex (K.projectedVertex v) := by
    rintro ⟨j, equal⟩
    exact absent ⟨i, j, equal⟩
  exact curved.ne' (K.interiorCurvature_eq_zero_off_parent_corners original conforming separated
    slope parent inside normal_eq height v away)

end Unfoldings.ConvexCap
