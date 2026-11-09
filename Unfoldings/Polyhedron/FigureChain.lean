module

public import Unfoldings.Polyhedron.FigureGerms

/-!
# Ordered figure edges from the derived link chain

The endpoints of successive sections agree by the actual seam-mate pairing.
A covering link chain covers exactly the actual figure boundary; a cyclic
chain closes in the plane as well as in the surface link.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

theorem germPoint_chain_next (i : Fin n) :
    V.germPoint (C.linkTurn Set.univ v (c.point i.castSucc)) =
      V.germPoint (c.point i.succ) := by
  have equal := congrArg V.germPoint (c.next i)
  change V.germPoint (C.linkMate Set.univ v
    (C.linkTurn Set.univ v (c.point i.castSucc))) = _ at equal
  simpa only [V.germPoint_mate] using equal

theorem germPoint_chain_closes
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    V.germPoint (C.linkTurn Set.univ v c.last) = V.germPoint c.first := by
  have equal := congrArg V.germPoint closes
  simpa only [V.germPoint_mate] using equal

end Unfoldings.SpatialFolding.VertexFigure

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

include P

theorem figure_boundary_eq_chain (covers : ∀ p, c.Visited p) :
    frontier V.carrier = ⋃ i : Fin (n + 1),
      segment ℝ (V.germPoint (c.point i))
        (V.germPoint (C.linkTurn Set.univ v (c.point i))) := by
  apply Set.image_injective.mpr V.place.injective
  rw [Set.image_iUnion, P.figure_boundary_eq_union_face_sections V]
  simp_rw [V.image_germ_segment]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := (C.linkCornerEquiv Set.univ v c covers).surjective a
    exact ⟨i, ha⟩
  · rintro ⟨i, hi⟩
    exact ⟨C.linkCornerEquiv Set.univ v c covers i, hi⟩

end Unfoldings.SpatialFolding.ConvexBoundary
