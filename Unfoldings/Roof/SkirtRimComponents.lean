module

public import Unfoldings.Roof.SkirtRadialCuts
public import Unfoldings.Geometry.RadialTailLabels

/-! Original rim roots attach to uniquely labeled radial skirt components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {outer : Set Plane} {q : Plane}



namespace SkirtTailFamily

variable (F : K.SkirtTailFamily outer q)

def rimComponent
    (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) : F.Component :=
  (Set.mem_iUnion.mp (covered w boundary)).choose

theorem rimComponent_mem
    (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) :
    K.projectedVertex w ∈ (F.componentTail (F.rimComponent covered w boundary)).carrier :=
  (Set.mem_iUnion.mp (covered w boundary)).choose_spec

theorem rimComponent_eq_of_member
    (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w)
    (c : F.Component) (member : K.projectedVertex w ∈ (F.componentTail c).carrier) :
    F.rimComponent covered w boundary = c := by
  by_contra different
  exact Set.disjoint_left.mp (F.components_disjoint different)
    (F.rimComponent_mem covered w boundary) member

/-- A radial component cannot merge two different original rim roots, even along a flat rim. -/
theorem rim_vertices_eq_of_component (c : F.Component) (w z : C.Vertex Set.univ)
    (first : C.IsBoundaryVertex Set.univ w) (last : C.IsBoundaryVertex Set.univ z)
    (first_member : K.projectedVertex w ∈ (F.componentTail c).carrier)
    (last_member : K.projectedVertex z ∈ (F.componentTail c).carrier) : w = z :=
  K.projectedVertex_injective
    ((F.componentTail c).inner_frontier_eq_of_members K.convex_projection F.origin
      ((K.projectedVertex_mem_frontier_iff w).mpr first)
      ((K.projectedVertex_mem_frontier_iff z).mpr last) first_member last_member)

end SkirtTailFamily
end Unfoldings.ConvexRoof
