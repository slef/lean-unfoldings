module

public import Unfoldings.Cap.SectionTrace

/-!
# Actual original-seam transitions away from section vertices

Two original faces meeting at a projected nonvertex section point are related
by one actual original seam. This is derived from exact metric classes and
injective cap projection. Constructing sections avoiding all original vertices
is a separate geometric step.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- At a genuine nonvertex intersection, distinct original faces cross one actual original seam. -/
theorem exists_crossing_of_projected_face_intersection (f g : Face) (different : f ≠ g)
    {z : Plane} (first : z ∈ (K.projectedTriangle f).carrier)
    (last : z ∈ (K.projectedTriangle g).carrier)
    (regular : ∀ h i, z ≠ (K.projectedTriangle h).vertex i) :
    ∃ x : C.Cell f, ∃ y : C.Cell g,
      K.projectFace f x.val = z ∧ K.projectFace g y.val = z ∧
        C.Crosses Set.univ (⟨f, x⟩ : C.Total) (⟨g, y⟩ : C.Total) := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at first last
  obtain ⟨a, ha, first⟩ := first
  obtain ⟨b, hb, last⟩ := last
  let x : C.Cell f := ⟨a, ha⟩
  let y : C.Cell g := ⟨b, hb⟩
  have raw_regular : ¬ C.IsVertex (⟨f, x⟩ : C.Total) := by
    rintro ⟨i, corner⟩
    exact regular f i (first.symm.trans (congrArg (K.projectFace f) corner.symm))
  have equal : C.faceMap Set.univ f x = C.faceMap Set.univ g y :=
    K.projection_injective (first.trans last.symm)
  have related := (C.faceMap_eq_iff Set.univ f g x y).mp equal
  rcases (C.eqvGen_iff_of_regular Set.univ raw_regular).mp related with tags | crossing
  · exact (different (congrArg Sigma.fst tags)).elim
  · exact ⟨x, y, first, last, crossing⟩

/-- An interior point of an original face cannot belong to any other original closed face. -/
theorem projected_face_unique_of_interior {f g : Face} {z : Plane}
    (inside : z ∈ interior (K.projectedTriangle f).carrier)
    (member : z ∈ (K.projectedTriangle g).carrier) : g = f := by
  have carrier : (K.projectedTriangle f).carrier =
      K.projectFaceHomeomorph f '' (C.triangle f).carrier :=
    (C.triangle f).affineImage_carrier _ _
  rw [carrier, ← Homeomorph.image_interior] at inside
  rw [projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨a, ha, first⟩ := inside
  obtain ⟨b, hb, last⟩ := member
  let x : C.Cell f := ⟨a, interior_subset ha⟩
  let y : C.Cell g := ⟨b, hb⟩
  have equal : C.faceMap Set.univ f x = C.faceMap Set.univ g y :=
    K.projection_injective (first.trans last.symm)
  have related := (C.faceMap_eq_iff Set.univ f g x y).mp equal
  have tags : (⟨f, x⟩ : C.Total) = ⟨g, y⟩ := C.eq_of_related_interior ha related
  exact (congrArg Sigma.fst tags).symm

namespace SectionFaceTrace

variable {K} {p q : Plane} (T : K.SectionFaceTrace p q)

/-- Every nontrivial transition of the constructed trace is an actual original-seam crossing. -/
theorem adjacent_faces_cross (i : Fin T.turns)
    (different : T.face i.castSucc ≠ T.face i.succ)
    (regular : ∀ h j, T.point i.castSucc.succ ≠ (K.projectedTriangle h).vertex j) :
    ∃ x : C.Cell (T.face i.castSucc), ∃ y : C.Cell (T.face i.succ),
      K.projectFace (T.face i.castSucc) x.val = T.point i.castSucc.succ ∧
      K.projectFace (T.face i.succ) y.val = T.point i.castSucc.succ ∧
        C.Crosses Set.univ (⟨T.face i.castSucc, x⟩ : C.Total)
          (⟨T.face i.succ, y⟩ : C.Total) := by
  apply K.exists_crossing_of_projected_face_intersection _ _ different
    (T.point_mem_face_last i.castSucc) _ regular
  simpa only [Fin.succ_castSucc] using T.point_mem_face_first i.succ

end SectionFaceTrace
end Unfoldings.ConvexCap
