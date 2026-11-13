module

public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Geometry.ConformingTriangles

/-! Injective projection and full-edge seam classes imply geometric face-to-face conformity. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- A genuine seam crossing supplies the whole shared projected edge through the actual point. -/
theorem projected_crossing_full_edge {a b : C.Total} (crossing : C.Crosses Set.univ a b) :
    ∃ e f : Fin 3, (K.projectedTriangle a.1).edge e = (K.projectedTriangle b.1).edge f ∧
      K.projectFace a.1 a.2.val ∈ (K.projectedTriangle a.1).edge e := by
  obtain ⟨s, _kept, side, x, rfl, rfl⟩ := crossing
  refine ⟨(C.seamSide s side).edge, (C.seamSide s (!side)).edge, ?_, ?_⟩
  · cases side
    · exact K.projected_seam_edges_eq s
    · exact (K.projected_seam_edges_eq s).symm
  · change K.projectFace (C.seamSide s side).face x.val ∈
      (K.projectedTriangle (C.seamSide s side).face).edge (C.seamSide s side).edge
    rw [projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩

/-- The supplied geometric roof triangulation has no partial-edge contacts. -/
theorem projectedTriangles_conforming : TriangleFamily.Conforming K.projectedTriangle := by
  intro f g different p member
  by_cases vertex : (K.projectedTriangle f).IsVertex p
  · obtain ⟨i, at_corner⟩ := vertex
    let v := C.vertexOfCorner Set.univ (f, i)
    have at_vertex : K.projectedVertex v = p := at_corner
    obtain ⟨j, at_last⟩ := K.projected_corner_of_vertex_mem v g (at_vertex.symm ▸ member.2)
    exact Or.inl ⟨⟨i, at_corner⟩, ⟨j, at_last.trans at_vertex⟩⟩
  · have first_member : p ∈ K.projectFace f '' (C.triangle f).carrier :=
      ((C.triangle f).affineImage_carrier (K.projectFace f) (K.projectFace_injective f)).subset
        member.1
    have last_member : p ∈ K.projectFace g '' (C.triangle g).carrier :=
      ((C.triangle g).affineImage_carrier (K.projectFace g) (K.projectFace_injective g)).subset
        member.2
    obtain ⟨x, hx, first⟩ := first_member
    obtain ⟨y, hy, last⟩ := last_member
    let a : C.Total := ⟨f, ⟨x, hx⟩⟩
    let b : C.Total := ⟨g, ⟨y, hy⟩⟩
    have regular : ¬ C.IsVertex a := by
      rintro ⟨i, at_corner⟩
      exact vertex ⟨i, (congrArg (K.projectFace f) at_corner).trans first⟩
    have equal : C.faceMap Set.univ f ⟨x, hx⟩ = C.faceMap Set.univ g ⟨y, hy⟩ :=
      K.projection_injective (first.trans last.symm)
    have related : Relation.EqvGen (C.glue Set.univ) a b :=
      (C.faceMap_eq_iff Set.univ f g ⟨x, hx⟩ ⟨y, hy⟩).mp equal
    rcases (C.eqvGen_iff_of_regular Set.univ regular).mp related with same | crossing
    · exact (different (congrArg Sigma.fst same)).elim
    · obtain ⟨e, h, shared, on_edge⟩ := K.projected_crossing_full_edge crossing
      exact Or.inr ⟨e, h, shared, first ▸ on_edge⟩

end Unfoldings.ConvexRoof
