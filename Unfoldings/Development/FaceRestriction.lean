module

public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Development

/-! Restrict an actual facewise development to selected whole faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (E : FacewiseDevelopment C retain)

open Classical in
def restrictFaces (U : Set Face) :
    FacewiseDevelopment (C.restrictFaces U) (C.restrictRetain U retain) where
  place f := E.place f.val
  joined s kept x := E.joined s.val kept x
  opposite s kept := E.opposite s.val kept

open Classical in
theorem Nonoverlapping.restrictFaces (nonoverlap : E.Nonoverlapping) (U : Set Face) :
    (E.restrictFaces U).Nonoverlapping := by
  intro f g different
  exact nonoverlap f.val g.val (fun equal => different (Subtype.ext equal))

end Unfoldings.FacewiseDevelopment
