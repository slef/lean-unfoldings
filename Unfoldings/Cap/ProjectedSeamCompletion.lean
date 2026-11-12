module

public import Unfoldings.Cap.ProjectedConformity

/-! Common whole projected edges are actual original seams, with their original isometries. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem exists_seam_of_projected_shared_edge {a b : EdgeRef Face}
    (different : a.face ≠ b.face)
    (same : (K.projectedTriangle a.face).edge a.edge =
      (K.projectedTriangle b.face).edge b.edge) :
    ∃ s : C.Seam, (C.left s = a ∧ C.right s = b) ∨ (C.left s = b ∧ C.right s = a) := by
  obtain ⟨x, regular⟩ := (C.triangle a.face).exists_edge_nonvertex a.edge
  have raw_regular : ¬ C.IsVertex (C.edgePoint a x) := regular
  have projected : K.projectFace a.face x.val ∈ (K.projectedTriangle b.face).edge b.edge := by
    rw [← same, projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩
  rw [projectedTriangle, Triangle.affineImage_edge] at projected
  obtain ⟨y, hy, point⟩ := projected
  let z : (C.triangle b.face).Edge b.edge := ⟨y, hy⟩
  have related : Relation.EqvGen (C.glue Set.univ) (C.edgePoint a x) (C.edgePoint b z) :=
    (C.faceMap_eq_iff Set.univ a.face b.face _ _).mp (K.projection_injective point.symm)
  rcases (C.eqvGen_iff_of_regular Set.univ raw_regular).mp related with equal | crossing
  · exact (different (congrArg Sigma.fst equal)).elim
  · have other : ¬ C.IsVertex (C.edgePoint b z) :=
      fun vertex => regular ((C.crosses_preserves_vertex crossing).mpr vertex)
    obtain ⟨s, _kept, side, w, first, last⟩ := crossing
    have first_edge : a = C.seamSide s side := C.onEdge_unique raw_regular
      (C.edgePoint_onEdge a x) (first.symm ▸ C.edgePoint_onEdge (C.seamSide s side) w)
    have last_edge : b = C.seamSide s (!side) := C.onEdge_unique other
      (C.edgePoint_onEdge b z)
      (last.symm ▸ C.edgePoint_onEdge (C.seamSide s (!side)) (C.across s side w))
    refine ⟨s, ?_⟩
    cases side
    · exact Or.inl ⟨first_edge.symm, last_edge.symm⟩
    · exact Or.inr ⟨last_edge.symm, first_edge.symm⟩

theorem faceMap_eq_of_projected_seam (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (x : C.Cell (C.left s).face) (y : C.Cell (C.right s).face)
    (on_edge : x.val ∈ (C.triangle (C.left s).face).edge (C.left s).edge)
    (same : K.projectFace (C.left s).face x.val = K.projectFace (C.right s).face y.val) :
    C.faceMap retain (C.left s).face x = C.faceMap retain (C.right s).face y := by
  let z : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨x.val, on_edge⟩
  have coordinates : (C.identify s z).val = y.val := K.projectFace_injective _
    ((K.projectedTriangle_joined s z).symm.trans same)
  have joined := C.seam_identified retain s kept z
  change C.faceMap retain (C.left s).face ⟨x.val, _⟩ =
    C.faceMap retain (C.right s).face ⟨(C.identify s z).val, _⟩ at joined
  simpa only [coordinates] using joined

end Unfoldings.ConvexCap
