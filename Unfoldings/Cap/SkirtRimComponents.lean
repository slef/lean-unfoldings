module

public import Unfoldings.Cap.SkirtCurvatureSeeds
public import Unfoldings.Cap.Boundary
public import Unfoldings.Geometry.RadialTailLabels

/-! Original rim roots attach to uniquely labeled radial skirt components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} {q : Plane}

namespace ClipSpatialTriangles

theorem cornerTails_covers_rim (T : K.ClipSpatialTriangles Z) (origin : q ∈ interior K.footprint)
    (positive : 0 < K.roofHeight q) (lower : Z < 0)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w) :
    K.projectedVertex w ∈ ⋃ c : (T.cornerTails origin positive lower).Component,
      ((T.cornerTails origin positive lower).componentTail c).carrier := by
  obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
  have equal : (K.projectedTriangle f).vertex k = K.projectedVertex w :=
    (K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner)
  have rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint := by
    intro member
    exact ((K.projectedVertex_mem_interior_iff w).mp (equal ▸ member)) boundary
  exact equal ▸ T.cornerTails_original_rim_corner origin positive lower f k rim

end ClipSpatialTriangles

namespace SkirtTailFamily

variable (F : K.SkirtTailFamily Z q)

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

theorem rimComponent_eq_of_member (lower : Z < 0)
    (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
    (w : C.Vertex Set.univ) (boundary : C.IsBoundaryVertex Set.univ w)
    (c : F.Component) (member : K.projectedVertex w ∈ (F.componentTail c).carrier) :
    F.rimComponent covered w boundary = c := by
  by_contra different
  exact Set.disjoint_left.mp (F.components_disjoint lower different)
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
end Unfoldings.ConvexCap
