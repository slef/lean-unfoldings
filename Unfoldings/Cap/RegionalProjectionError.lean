module

public import Unfoldings.Cap.RelativeFaceAngleError
public import Unfoldings.Cap.RegionalAngles

/-! Relative original corner errors sum over actual selected fans without a valence charge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
/-- A selected fan pays for its projected angle, rather than for its number of original corners. -/
theorem abs_regionalAngleExcess_le_relative_projected_sum {ε : ℝ}
    (error : K.RelativeCornerAngleError ε) (faces : Set Face) (w : C.Vertex Set.univ) :
    |K.regionalAngleExcess faces w| ≤
      ε * C.regionalCornerSum faces (fun c => (K.projectedTriangle c.1).cornerAngle c.2) w := by
  classical
  unfold regionalAngleExcess TriangleComplex.regionalCornerSum
  calc
    _ ≤ ∑ c : C.Corner,
        |if c.1 ∈ faces ∧ C.vertexOfCorner Set.univ c = w then
          (C.triangle c.1).cornerAngle c.2 - (K.projectedTriangle c.1).cornerAngle c.2 else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : C.Corner, ε *
        (if c.1 ∈ faces ∧ C.vertexOfCorner Set.univ c = w then
          (K.projectedTriangle c.1).cornerAngle c.2 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs
      · exact error c.1 c.2
      · simp only [abs_zero, mul_zero, le_refl]
    _ = _ := (Finset.mul_sum _ _ _).symm

open Classical in
/-- The projected angle of any selected star is at most its full original projected star. -/
theorem regional_projected_angle_le_total (faces : Set Face) (w : C.Vertex Set.univ) :
    C.regionalCornerSum faces (fun c => (K.projectedTriangle c.1).cornerAngle c.2) w ≤
      K.projectedTotalAngle Set.univ w := by
  classical
  unfold TriangleComplex.regionalCornerSum projectedTotalAngle
  apply Finset.sum_le_sum
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = w
  · simp only [same, and_true, ite_true]
    split_ifs
    · exact le_rfl
    · exact (K.projectedTriangle c.1).cornerAngle_pos c.2 |>.le
  · simp only [same, and_false, ite_false, le_refl]

open Classical in
/-- Every actual selected interior fan has a uniform error bound, including reflex fans. -/
theorem abs_regionalAngleExcess_le_two_pi_mul {ε : ℝ} (nonnegative : 0 ≤ ε)
    (error : K.RelativeCornerAngleError ε) (faces : Set Face) (w : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ w) :
    |K.regionalAngleExcess faces w| ≤ ε * (2 * Real.pi) := by
  have sum_bound := K.regional_projected_angle_le_total faces w
  rw [K.projectedTotalAngle_eq_two_pi w internal] at sum_bound
  exact (K.abs_regionalAngleExcess_le_relative_projected_sum error faces w).trans
    (mul_le_mul_of_nonneg_left sum_bound nonnegative)

end Unfoldings.ConvexCap
