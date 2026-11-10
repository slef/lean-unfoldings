module

public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Complex.Vertices
public import Unfoldings.Geometry.MeshProgress

/-! Actual original cap edges enter a prescribed quadrant from every interior projected vertex. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def projectedVertex (v : C.Vertex Set.univ) : Plane :=
  Cap.horizontal (K.folding.toSpace Set.univ (C.vertexPoint Set.univ v))

@[simp] theorem projectedVertex_ofCorner (f : Face) (i : Fin 3) :
    K.projectedVertex (C.vertexOfCorner Set.univ (f, i)) = (K.projectedTriangle f).vertex i := rfl

theorem projectedVertex_injective : Function.Injective K.projectedVertex := by
  intro v w equal
  exact C.vertexPoint_injective Set.univ (K.projection_injective equal)

/-- A projected cap vertex contained in a projected face is one of that face's actual corners. -/
theorem projected_corner_of_vertex_mem (v : C.Vertex Set.univ) (f : Face)
    (present : K.projectedVertex v ∈ (K.projectedTriangle f).carrier) :
    ∃ i, (K.projectedTriangle f).vertex i = K.projectedVertex v := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at present
  obtain ⟨x, carrier, equal⟩ := present
  let a : C.Cell f := ⟨x, carrier⟩
  have points : C.faceMap Set.univ f a = C.vertexPoint Set.univ v :=
    K.projection_injective equal
  have corner := (C.mem_range_vertexPoint_iff Set.univ (⟨f, a⟩ : C.Total)).mp ⟨v, points.symm⟩
  obtain ⟨i, image⟩ := corner
  exact ⟨i, (congrArg (K.projectFace f) image).trans equal⟩

/-- The local progress conclusion uses actual endpoints of the original input triangle edges. -/
theorem exists_projected_quadrant_edge (v : C.Vertex Set.univ)
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (acute : ∀ f i, (K.projectedTriangle f).cornerAngle i < Real.pi / 2) :
    ∃ f i, C.vertexOfCorner Set.univ (f, i) = v ∧
      (StrictQuadrant (K.projectedVertex (C.vertexOfCorner Set.univ (f, Triangle.next i)) -
        K.projectedVertex v) ∨
      StrictQuadrant (K.projectedVertex
        (C.vertexOfCorner Set.univ (f, Triangle.next (Triangle.next i))) -
          K.projectedVertex v)) := by
  obtain ⟨f, i, center, progress⟩ := exists_mesh_quadrant_edge K.projectedTriangle K.footprint
    K.footprint_eq_union_projectedTriangles.subset (K.projectedVertex v) inside
    (K.projected_corner_of_vertex_mem v) acute
  have original : C.vertexOfCorner Set.univ (f, i) = v :=
    K.projectedVertex_injective center
  exact ⟨f, i, original, progress⟩

end Unfoldings.ConvexCap
