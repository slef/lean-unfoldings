module

public import Unfoldings.Complex.Classes

/-! A nonvertex seam class determines its unique original seam name. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Related regular points on named original seam banks have the same original seam. -/
theorem seams_eq_of_related_regular_edgePoints (s t : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (y : (C.triangle (C.left t).face).Edge (C.left t).edge)
    (regular : ¬ C.IsVertex (C.edgePoint (C.left s) x))
    (related : Relation.EqvGen (C.glue Set.univ)
      (C.edgePoint (C.left s) x) (C.edgePoint (C.left t) y)) : s = t := by
  rcases (C.eqvGen_iff_of_regular Set.univ regular).mp related with equal | crossing
  · have edges := C.onEdge_unique regular (C.edgePoint_onEdge (C.left s) x)
      (equal.symm ▸ C.edgePoint_onEdge (C.left t) y)
    exact congrArg Prod.fst
      (C.seamSide_injective (a₁ := (s, false)) (a₂ := (t, false)) edges)
  · have last_regular : ¬ C.IsVertex (C.edgePoint (C.left t) y) :=
      fun vertex => regular ((C.crosses_preserves_vertex crossing).mpr vertex)
    obtain ⟨u, _kept, side, z, first, last⟩ := crossing
    have first_edges := C.onEdge_unique regular (C.edgePoint_onEdge (C.left s) x)
      (first.symm ▸ C.edgePoint_onEdge (C.seamSide u side) z)
    have last_edges := C.onEdge_unique last_regular (C.edgePoint_onEdge (C.left t) y)
      (last.symm ▸ C.edgePoint_onEdge (C.seamSide u (!side)) (C.across u side z))
    have first_seam := congrArg Prod.fst
      (C.seamSide_injective (a₁ := (s, false)) (a₂ := (u, side)) first_edges)
    have last_seam := congrArg Prod.fst
      (C.seamSide_injective (a₁ := (t, false)) (a₂ := (u, !side)) last_edges)
    exact first_seam.trans last_seam.symm

end Unfoldings.TriangleComplex
