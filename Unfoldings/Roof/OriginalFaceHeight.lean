module

public import Unfoldings.Roof.SupportingEnvelope

/-! Original whole-face height identities, including arbitrary rim points. -/

@[expose] public section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem roofHeight_eq_supportHeight_of_mem_projectedTriangle (f : Face) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier) : K.roofHeight p = K.supportHeight f p := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at member
  obtain ⟨x, member, rfl⟩ := member
  exact (K.roofHeight_face f ⟨x, member⟩).trans (K.supportHeight_face f x).symm

end Unfoldings.ConvexRoof
