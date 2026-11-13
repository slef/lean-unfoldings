module

public import Unfoldings.Complex.FaceRestriction

/-! Restricting faces preserves the original names of every pairing between remaining faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- Every original seam whose two whole faces remain is a seam of the face restriction. -/
theorem exists_restricted_seam_of_names (U : Set Face) (f g : {f : Face // f ∈ U})
    (e d : Fin 3) (s : C.Seam) (left : C.left s = ⟨f.val, e⟩)
    (right : C.right s = ⟨g.val, d⟩) :
    ∃ t : (C.restrictFaces U).Seam,
      (C.restrictFaces U).left t = ⟨f, e⟩ ∧ (C.restrictFaces U).right t = ⟨g, d⟩ := by
  have first : (C.left s).face ∈ U := by rw [left]; exact f.property
  have last : (C.right s).face ∈ U := by rw [right]; exact g.property
  let t : (C.restrictFaces U).Seam := ⟨s, first, last⟩
  refine ⟨t, ?_, ?_⟩
  · apply congrArg₂ EdgeRef.mk
    · exact Subtype.ext (congrArg EdgeRef.face left)
    · exact congrArg EdgeRef.edge left
  · apply congrArg₂ EdgeRef.mk
    · exact Subtype.ext (congrArg EdgeRef.face right)
    · exact congrArg EdgeRef.edge right

end Unfoldings.TriangleComplex
