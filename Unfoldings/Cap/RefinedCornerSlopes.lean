module

public import Unfoldings.Cap.RefinementCurvatureSupport
public import Unfoldings.Roof.CapBridge
public import Unfoldings.Roof.RefinedCornerSlopes

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
  exact K.toRoof.exists_tangent_incidentSlopes_on_old_edge original conforming separated
    slope height parent inside normal_eq affine agree v i e on_edge regular

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
  exact K.toRoof.refined_slope_eq_of_mem_old_interior original conforming slope parent inside
    normal_eq v i interior_mem f k at_v

end Unfoldings.ConvexCap
