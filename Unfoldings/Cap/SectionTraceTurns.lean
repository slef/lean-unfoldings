module

public import Unfoldings.Cap.SectionTrace

/-! The constructed original-face trace inherits the uniform actual spatial section-turn bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectionFaceTrace

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)

/-- Actual tangent directions along the constructed original-face trace turn by at most 2φ. -/
theorem sum_spatialDirection_turn_le_tilt (different : p ≠ q)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i : Fin T.turns, InnerProductGeometry.angle
      (K.spatialDirection (T.face i.castSucc) (q - p))
      (K.spatialDirection (T.face i.succ) (q - p))) ≤ 2 * φ := by
  let direction := NormedSpace.normalize (q - p)
  let length := ‖q - p‖
  let time (i : Fin (T.turns + 2)) : ℝ := length * (T.time i : ℝ)
  have nonzero : q - p ≠ 0 := sub_ne_zero.mpr different.symm
  have positive : 0 < length := norm_pos_iff.mpr nonzero
  have unit : ‖direction‖ = 1 := NormedSpace.norm_normalize nonzero
  have ordered : StrictMono time := by
    intro i j le
    exact mul_lt_mul_of_pos_left (T.increasing le) positive
  have point_eq (i : Fin (T.turns + 2)) :
      K.roofSectionPoint p direction (time i) = T.spatialPoint i := by
    have horizontal : p + time i • direction = AffineMap.lineMap p q (T.time i : ℝ) := by
      change p + (length * (T.time i : ℝ)) • NormedSpace.normalize (q - p) = _
      rw [mul_comm, mul_smul, NormedSpace.norm_smul_normalize, AffineMap.lineMap_apply_module']
      module
    change Cap.horizontalAtHeight (p + time i • direction)
      (K.roofHeight (p + time i • direction)) =
        Cap.horizontalAtHeight (T.point i) (K.roofHeight (T.point i))
    rw [horizontal]
    rfl
  have secant_eq (i : Fin (T.turns + 1)) :
      K.roofSectionSecant p direction time i =
        T.spatialPoint i.succ - T.spatialPoint i.castSucc := by
    rw [ConvexCap.roofSectionSecant, point_eq, point_eq]
  calc
    _ = ∑ i : Fin T.turns, InnerProductGeometry.angle
        (K.roofSectionSecant p direction time i.castSucc)
        (K.roofSectionSecant p direction time i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [secant_eq, secant_eq, T.spatialPoint_sub, T.spatialPoint_sub,
        InnerProductGeometry.angle_smul_left_of_pos _ _ (T.time_step_pos i.castSucc),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (T.time_step_pos i.succ)]
    _ ≤ _ :=
      K.sum_roofSection_spatial_turn_le_tilt nonnegative small tilt p direction unit time ordered

end Unfoldings.ConvexCap.SectionFaceTrace
