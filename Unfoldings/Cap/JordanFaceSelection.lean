module

public import Unfoldings.Geometry.JordanTriangleSelection
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Cap.RegionalAngles

/-! Actual Jordan closures select whole projected cap faces and all their interior vertex stars. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def jordanFaces (J : Set Plane) : Set Face :=
  ConvexCellRegion.selected (fun f => (K.projectedTriangle f).carrier)
    (PlanarTopology.closedJordanDomain J)

/-- A respected geometric curve constructs the actual whole-face filling in the cap footprint. -/
theorem jordanDomain_eq_projectedFace_union {J : Set Plane}
    (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J) :
    PlanarTopology.closedJordanDomain J =
      ⋃ f ∈ K.jordanFaces J, (K.projectedTriangle f).carrier := by
  apply TriangleFamily.jordanDomain_eq_selected_triangles K.projectedTriangle jordan
  · rw [← K.footprint_eq_union_projectedTriangles]
    exact K.convex_projection
  · rwa [← K.footprint_eq_union_projectedTriangles]
  · exact avoids

/-- Every actual original corner class strictly inside the filling has its whole star selected. -/
theorem jordanFaces_fullStar_of_interior {J : Set Plane} (w : C.Vertex Set.univ)
    (inside : K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J)) :
    C.FullStarIn (K.jordanFaces J) w := by
  intro c same
  apply TriangleFamily.jordanDomain_incident_triangle_selected K.projectedTriangle c.1 inside
  rw [← same, K.projectedVertex_ofCorner]
  exact (K.projectedTriangle c.1).vertex_mem c.2

end Unfoldings.ConvexCap
