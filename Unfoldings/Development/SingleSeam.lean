module

public import Unfoldings.Complex.HingeCoordinates
public import Unfoldings.Development

/-! Construct a genuine facewise development retaining one actual seam and opening it outward. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Only this original seam is retained; the two incident faces have the actual outward hinge. -/
def singleSeamDevelopment (s : C.Seam) (different : (C.left s).face ≠ (C.right s).face) :
    FacewiseDevelopment C {s} where
  place := C.hingeFrame s
  joined t kept x := by
    have same : t = s := Set.mem_singleton_iff.mp kept
    subst t
    rw [C.hingeFrame_left s different, C.hingeFrame_right s]
    exact ((C.seamHinge s).joined x).symm
  opposite t kept := by
    have same : t = s := Set.mem_singleton_iff.mp kept
    subst t
    rw [C.hingeFrame_left s different, C.hingeFrame_right s]
    exact (C.seamHinge s).opposite

end Unfoldings.TriangleComplex
