module

public import Unfoldings.Roof.SupportingEnvelope
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Convex gradient selections have straight escape rays from every omitted face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The gradient of the convex function obtained by negating the roof height. -/
def normalSlope (f : Face) : Plane := (K.normal f 2)⁻¹ • Cap.horizontal (K.normal f)

/-- Supporting affine heights have the actual negative gradient of the convex roof function. -/
theorem supportHeight_sub (f : Face) (p q : Plane) :
    K.supportHeight f q - K.supportHeight f p = -inner ℝ (K.normalSlope f) (q - p) := by
  rw [K.supportHeight_apply, K.supportHeight_apply]
  simp only [normalSlope, real_inner_smul_left, inner_sub_right]
  ring

/-- The directional gradient increases along every straight segment on a convex roof.
This uses only the two actual supporting-plane inequalities. -/
theorem normalSlope_monotone (f g : Face) (x : C.Cell f) (y : C.Cell g) :
    0 ≤ inner ℝ (K.normalSlope g - K.normalSlope f)
      (K.projectFace g y.val - K.projectFace f x.val) := by
  have first := K.face_height_le_supportHeight f g y
  have last := K.face_height_le_supportHeight g f x
  have at_first := K.supportHeight_face f x.val
  have at_last := K.supportHeight_face g y.val
  have change_first := K.supportHeight_sub f (K.projectFace f x.val) (K.projectFace g y.val)
  have change_last := K.supportHeight_sub g (K.projectFace f x.val) (K.projectFace g y.val)
  rw [inner_sub_left]
  linarith

/-- Selecting all faces whose gradients belong to one closed convex set leaves a straight
ray from every omitted face that never meets any selected face at positive distance. -/
theorem exists_gradient_selection_escape {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (nonempty : slopes.Nonempty)
    (f : Face) (omitted : K.normalSlope f ∉ slopes) (x : C.Cell f) :
    ∃ u : Plane, u ≠ 0 ∧ ∀ r : ℝ, r > 0 → ∀ g : Face, K.normalSlope g ∈ slopes →
      K.projectFace f x.val + r • u ∉ (K.projectedTriangle g).carrier := by
  obtain ⟨functional, c, below, above⟩ := geometric_hahn_banach_closed_point convex closed omitted
  let u := (InnerProductSpace.toDual ℝ Plane).symm functional
  have pairing (z : Plane) : inner ℝ z u = functional z := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have nonzero : u ≠ 0 := by
    intro zero
    obtain ⟨s, member⟩ := nonempty
    have first := below s member
    have last := above
    rw [← pairing s, zero, inner_zero_right] at first
    rw [← pairing (K.normalSlope f), zero, inner_zero_right] at last
    linarith
  refine ⟨u, nonzero, ?_⟩
  intro r positive g selected present
  rw [projectedTriangle, Triangle.affineImage_carrier] at present
  obtain ⟨y, hy, at_y⟩ := present
  have order := K.normalSlope_monotone f g x ⟨y, hy⟩
  change 0 ≤ inner ℝ (K.normalSlope g - K.normalSlope f)
    (K.projectFace g y - K.projectFace f x.val) at order
  rw [at_y, add_sub_cancel_left, real_inner_smul_right] at order
  have comparison : 0 ≤ inner ℝ (K.normalSlope g - K.normalSlope f) u :=
    nonneg_of_mul_nonneg_right order positive
  rw [inner_sub_left, pairing, pairing] at comparison
  have upper := below _ selected
  linarith

end Unfoldings.ConvexRoof
