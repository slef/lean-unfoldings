module

public import Unfoldings.Complex.Folding
public import Unfoldings.Geometry.Interior

/-! An embedded original face interior meets no other original face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem face_eq_of_spatial_interior (embedded : F.IsEmbedded)
    {f g : Face} (x : C.Cell f) (y : C.Cell g)
    (inside : x.val ∈ interior (C.triangle f).carrier)
    (equal : F.place f x.val = F.place g y.val) : f = g := by
  have regular : ¬ C.IsVertex (⟨f, x⟩ : C.Total) := by
    rintro ⟨i, hi⟩
    apply (C.triangle f).not_mem_interior_of_mem_edge i
      (x := x.val) (by rw [← hi]; exact left_mem_segment ℝ _ _) inside
  have related := (F.isEmbedded_iff.mp embedded) ⟨f, x⟩ ⟨g, y⟩ equal
  rcases (C.eqvGen_iff_of_regular Set.univ regular).mp related with same | crossing
  · exact congrArg Sigma.fst same
  · obtain ⟨s, _kept, side, p, source, _target⟩ := crossing
    have faces : f = (C.seamSide s side).face := congrArg Sigma.fst source
    have coordinates : x.val = p.val := congrArg (fun a : C.Total => a.2.val) source
    have on_edge : x.val ∈ (C.triangle f).edge (C.seamSide s side).edge := by
      rw [coordinates, faces]
      exact p.property
    exact ((C.triangle f).not_mem_interior_of_mem_edge _ on_edge inside).elim

theorem faceImage_disjoint_spatial_interior (embedded : F.IsEmbedded)
    {f g : Face} (different : f ≠ g) :
    Disjoint (F.place f '' interior (C.triangle f).carrier) (F.faceImage g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, inside, rfl⟩ ⟨y, hy, equal⟩
  exact different (F.face_eq_of_spatial_interior embedded
    ⟨x, interior_subset inside⟩ ⟨y, hy⟩ inside equal.symm)

end Unfoldings.SpatialFolding
