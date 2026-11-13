module

public import Unfoldings.Roof.DevelopmentCoordinates

public import Unfoldings.Roof.ProjectedPointCopies

/-! Actual developed values and exact vertex classification of projected face copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem toPlane_pointCopy {retain : Set C.Seam} (D : FacewiseDevelopment C retain)
    (f : Face) (p : Plane) (member : p ∈ (K.projectedTriangle f).carrier) :
    D.toPlane (K.pointCopy retain f p member) = D.roofPlacement K f p := rfl

theorem pointCopy_mem_vertices_iff (retain : Set C.Seam) (f : Face) (p : Plane)
    (member : p ∈ (K.projectedTriangle f).carrier) :
    K.pointCopy retain f p member ∈ Set.range (C.vertexPoint retain) ↔
      (K.projectedTriangle f).IsVertex p := by
  unfold pointCopy
  dsimp only [TriangleComplex.faceMap, MetricGluing.of]
  rw [C.mem_range_vertexPoint_iff]
  constructor
  · rintro ⟨i, corner⟩
    refine ⟨i, ?_⟩
    change (K.projectFaceEquiv f) ((C.triangle f).vertex i) = p
    rw [corner, AffineEquiv.apply_symm_apply]
  · rintro ⟨i, corner⟩
    refine ⟨i, ?_⟩
    apply (K.projectFaceEquiv f).injective
    exact corner.trans ((K.projectFaceEquiv f).apply_symm_apply p).symm

theorem pointCopy_mem_vertices_of_physical_vertex (retain : Set C.Seam)
    (f : Face) (p : Plane) (member : p ∈ (K.projectedTriangle f).carrier)
    (vertex : p ∈ Set.range K.projectedVertex) :
    K.pointCopy retain f p member ∈ Set.range (C.vertexPoint retain) := by
  obtain ⟨v, at_v⟩ := vertex
  obtain ⟨i, corner⟩ := K.projected_corner_of_vertex_mem v f (at_v.symm ▸ member)
  exact (K.pointCopy_mem_vertices_iff retain f p member).mpr ⟨i, corner.trans at_v⟩

end Unfoldings.ConvexRoof
