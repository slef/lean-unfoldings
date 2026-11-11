module

public import Unfoldings.Cap.SectionTransitions
public import Unfoldings.Cap.SeamDirections

/-!
# Actual transverse original seams along regular cap sections

Every change of original face label occurs on an actual original seam. Avoiding
original vertices derives transversality and identifies its whole projected
edge, including the orientation of its two face labels.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectionFaceTrace

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)

/-- Construct the actual transverse seam for each nonconstant original-face transition. -/
theorem exists_transverse_adjacent_seam (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (changes : T.face i.castSucc ≠ T.face i.succ) :
    ∃ s : C.Seam,
      ((C.left s).face = T.face i.castSucc ∧ (C.right s).face = T.face i.succ ∨
        (C.right s).face = T.face i.castSucc ∧ (C.left s).face = T.face i.succ) ∧
      T.point i.castSucc.succ ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge ∧
      orient 0 (K.projectedSeamVector s) (q - p) ≠ 0 := by
  obtain ⟨x, y, first, last, s, _retained, side, a, hx, hy⟩ :=
    T.adjacent_faces_cross i changes (regular (T.time i.castSucc.succ))
  have left_face := congrArg Sigma.fst hx
  have right_face := congrArg Sigma.fst hy
  let projection (z : C.Total) := K.projectFace z.1 z.2.val
  have first_image := congrArg projection hx
  have last_image := congrArg projection hy
  cases side
  · have meets : K.projectFace (C.left s).face a.val = T.point i.castSucc.succ :=
      first_image.symm.trans first
    refine ⟨s, Or.inl ⟨left_face.symm, right_face.symm⟩, ?_, ?_⟩
    · rw [projectedTriangle, Triangle.affineImage_edge]
      exact ⟨a.val, a.property, meets⟩
    · exact K.projectedSeamVector_transverse s a different (fun t => regular t _ _) _ meets
  · have meets : K.projectFace (C.left s).face ((C.identify s).symm a).val =
        T.point i.castSucc.succ := last_image.symm.trans last
    refine ⟨s, Or.inr ⟨left_face.symm, right_face.symm⟩, ?_, ?_⟩
    · rw [projectedTriangle, Triangle.affineImage_edge]
      exact ⟨((C.identify s).symm a).val, ((C.identify s).symm a).property, meets⟩
    · exact K.projectedSeamVector_transverse s ((C.identify s).symm a) different
        (fun t => regular t _ _) _ meets

end Unfoldings.ConvexCap.SectionFaceTrace
