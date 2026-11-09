module

public import Unfoldings.Complex.GermEndpoints
public import Unfoldings.Complex.EmbeddedStars

/-!
# Actual edge incidence determines spatial link germs

At a vertex of a spatially foldable complex, a local edge determines its
germ. Paired local edges determine seam mates, because an original triangle
has only one corner in the chosen metric vertex class.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem linkGerm_eq_of_edge_eq {p q : C.LinkGerm retain v}
    (edges : C.germEdge p.val = C.germEdge q.val) : p = q := by
  have faces : p.val.1.1 = q.val.1.1 := congrArg EdgeRef.face edges
  have corners := F.cornerAt_faces_injective retain v
    (a₁ := ⟨p.val.1, p.property⟩) (a₂ := ⟨q.val.1, q.property⟩) faces
  exact Subtype.ext (C.germ_eq_of_corner_edge (congrArg Subtype.val corners) edges)

theorem linkGerm_mate_of_paired_edges (s : C.Seam) (kept : s ∈ retain) (side : Bool)
    {p q : C.LinkGerm retain v}
    (source : C.germEdge p.val = C.seamSide s side)
    (target : C.germEdge q.val = C.seamSide s (!side)) :
    C.linkMate retain v p = q := by
  have encoded : p.val = C.germOfEndpoint (C.seamSide s side) p.val.2 := by
    rw [← source, C.germOfEndpoint_germEdge]
  let r := C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side p.val.2)
  have crossing : C.GermCrosses retain p.val r := ⟨s, kept, side, p.val.2, encoded, rfl⟩
  let r' : C.LinkGerm retain v := ⟨r, crossing.vertex_eq.symm.trans p.property⟩
  have equal : r' = q := F.linkGerm_eq_of_edge_eq retain v
    ((C.germEdge_germOfEndpoint _ _).trans target.symm)
  apply Subtype.ext
  exact (C.mateGerm_of_crossing crossing).trans (congrArg Subtype.val equal)

theorem linkGerms_eq_or_mate_of_regular_spatial_point (embedded : F.IsEmbedded)
    {w : C.Vertex Set.univ} {p q : C.LinkGerm Set.univ w} {a b : C.Total}
    (regular : ¬ C.IsVertex a) (on_p : C.OnEdge (C.germEdge p.val) a)
    (on_q : C.OnEdge (C.germEdge q.val) b)
    (equal : F.place a.1 a.2.val = F.place b.1 b.2.val) :
    p = q ∨ C.linkMate Set.univ w p = q := by
  have related := (F.isEmbedded_iff.mp embedded) a b equal
  rcases (C.eqvGen_iff_of_regular Set.univ regular).mp related with same | crossing
  · subst b
    exact Or.inl (F.linkGerm_eq_of_edge_eq Set.univ w (C.onEdge_unique regular on_p on_q))
  · obtain ⟨s, kept, side, x, ha, hb⟩ := crossing
    have source := C.onEdge_unique regular on_p (ha ▸ C.edgePoint_onEdge _ x)
    have regular_b : ¬ C.IsVertex b := fun vertex => regular
      ((C.crosses_preserves_vertex ⟨s, kept, side, x, ha, hb⟩).mpr vertex)
    have target := C.onEdge_unique regular_b on_q (hb ▸ C.edgePoint_onEdge _ _)
    exact Or.inr (F.linkGerm_mate_of_paired_edges Set.univ w s kept side source target)

end Unfoldings.SpatialFolding
