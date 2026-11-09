module

public import Unfoldings.Complex.Charts

/-! An original face-interior point has exactly its one original tagged representative. -/

@[expose] public section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem faceInterior_tag_eq (retain : Set C.Seam) (f : Face) (x : C.Cell f)
    (inside : x.val ∈ interior (C.triangle f).carrier) (a : C.Total)
    (equal : C.faceMap retain f x = MetricGluing.point C.Cell (C.glue retain) a) :
    (⟨f, x⟩ : C.Total) = a := by
  have related := (C.point_eq_iff retain ⟨f, x⟩ a).mp equal
  rw [← Relation.EqvGen.reflTransGen_symmGen] at related
  rcases related.cases_head with same | ⟨b, first, _rest⟩
  · exact same
  · have support : x ∈ MetricGluing.seamSupport C.Cell (C.glue retain) f :=
      first.elim (fun h => Or.inl ⟨b, h⟩) (fun h => Or.inr ⟨b, h⟩)
    obtain ⟨e, on_edge⟩ := C.seamSupport_subset_edges retain f support
    exact ((C.triangle f).not_mem_interior_of_mem_edge e on_edge inside).elim

end Unfoldings.TriangleComplex
