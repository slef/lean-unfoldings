module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Angles of oppositely directed real multiples, independently of a chosen traversal direction. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reversing the incoming bank removes both scalar signs when the banks point opposite ways. -/
theorem angle_neg_smul_smul_of_mul_neg (x y : E) {a b : ℝ} (opposite : a * b < 0) :
    InnerProductGeometry.angle (-(a • x)) (b • y) = InnerProductGeometry.angle x y := by
  rw [← neg_smul]
  rcases mul_neg_iff.mp opposite with ⟨ap, bn⟩ | ⟨an, bp⟩
  · rw [InnerProductGeometry.angle_smul_left_of_neg _ _ (neg_neg_of_pos ap),
      InnerProductGeometry.angle_smul_right_of_neg _ _ bn,
      InnerProductGeometry.angle_neg_neg]
  · rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (neg_pos.mpr an),
      InnerProductGeometry.angle_smul_right_of_pos _ _ bp]

/-- Literal opposite scalar bank directions form precisely a straight projected angle. -/
theorem angle_smul_self_of_mul_neg {x : E} (nonzero : x ≠ 0) {a b : ℝ}
    (opposite : a * b < 0) :
    InnerProductGeometry.angle (a • x) (b • x) = Real.pi := by
  have same := angle_neg_smul_smul_of_mul_neg x x opposite
  rw [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_self nonzero] at same
  linarith

end Unfoldings
