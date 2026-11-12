module

public import Unfoldings.Cap.ProjectedSeamUnique
public import Unfoldings.Complex.Neighborhood

/-! A regular point of an actual projected seam belongs to exactly its two incident faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem projected_face_eq_seamSide_of_regular (s : C.Seam) {f : Face} {p : Plane}
    (on_edge : p ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (member : p ∈ (K.projectedTriangle f).carrier)
    (regular : ∀ g i, p ≠ (K.projectedTriangle g).vertex i) :
    f = (C.left s).face ∨ f = (C.right s).face := by
  rw [projectedTriangle, Triangle.affineImage_edge] at on_edge
  rw [projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨x, on_edge, first⟩ := on_edge
  obtain ⟨y, carrier, last⟩ := member
  let a := C.edgePoint (C.left s) ⟨x, on_edge⟩
  let b := C.edgePoint (C.right s) (C.identify s ⟨x, on_edge⟩)
  let c : C.Total := ⟨f, ⟨y, carrier⟩⟩
  have raw_regular : ¬ C.IsVertex a := by
    rintro ⟨i, at_corner⟩
    exact regular (C.left s).face i
      (first.symm.trans (congrArg (K.projectFace _) at_corner.symm))
  have crossing : C.Crosses Set.univ a b := ⟨s, Set.mem_univ _, false, ⟨x, on_edge⟩, rfl, rfl⟩
  have equal : C.faceMap Set.univ a.1 a.2 = C.faceMap Set.univ c.1 c.2 :=
    K.projection_injective (first.trans last.symm)
  have related := (C.faceMap_eq_iff Set.univ _ _ _ _).mp equal
  rcases (C.eqvGen_iff_eq_or_neighbor raw_regular crossing).mp related with first | last
  · exact Or.inl (congrArg Sigma.fst first)
  · exact Or.inr (congrArg Sigma.fst last)

end Unfoldings.ConvexCap
