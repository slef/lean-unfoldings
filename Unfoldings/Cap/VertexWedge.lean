module

public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Geometry.MeshWedge
public import Unfoldings.Geometry.ShearWedge

/-! Strict acute-wedge progress along actual projected input edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The same narrower-than-right-angle wedge is available at every interior projected vertex. -/
theorem exists_projected_sheared_quadrant_edge (t : ℝ) (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (acute : ∀ f i, ((K.projectedTriangle f).sheared t).cornerAngle i < Real.pi / 2) :
    ∃ f i, C.vertexOfCorner Set.univ (f, i) = v ∧
      (StrictQuadrant (quadrantShear t
        (K.projectedVertex (C.vertexOfCorner Set.univ (f, Triangle.next i)) -
          K.projectedVertex v)) ∨
      StrictQuadrant (quadrantShear t
        (K.projectedVertex (C.vertexOfCorner Set.univ (f, Triangle.next (Triangle.next i))) -
          K.projectedVertex v))) := by
  obtain ⟨f, i, center, progress⟩ := exists_mesh_sheared_quadrant_edge K.projectedTriangle t
    K.footprint K.footprint_eq_union_projectedTriangles.subset (K.projectedVertex v) inside
    (K.projected_corner_of_vertex_mem v) acute
  exact ⟨f, i, K.projectedVertex_injective center, progress⟩

end Unfoldings.ConvexCap
