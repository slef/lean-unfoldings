module

public import Unfoldings.Geometry.ClippedRadialTails
public import Unfoldings.Geometry.ConvexRadialTails

/-! An entire radial component meets an inner convex rim in at most one point. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S B : Set E} {q p x y : E} (T : RadialClipTail S q p)

theorem exists_tip_scale_of_mem (member : x ∈ T.carrier) :
    ∃ a : ℝ, 0 < a ∧ q + a • (x - q) = T.tip := by
  obtain ⟨a, bounds, at_x⟩ := T.carrier_eq_image.subset member
  have positive : 0 < a := T.start_pos.trans_le bounds.1
  refine ⟨a⁻¹, inv_pos.mpr positive, ?_⟩
  have vector := congrArg (fun z : E => z - q) at_x
  simp only [add_sub_cancel_left] at vector
  have scaled := congrArg (fun z : E => q + a⁻¹ • z) vector
  simp only [smul_smul, inv_mul_cancel₀ positive.ne', one_smul, add_sub_cancel] at scaled
  exact scaled.symm

/-- The component's direction is a nonnegative multiple of every source-centered position on it. -/
theorem direction_eq_nonneg_smul_of_mem (member : x ∈ T.carrier) :
    ∃ a : ℝ, 0 ≤ a ∧ T.tip - p = a • (x - q) := by
  obtain ⟨a, positive, at_tip⟩ := T.exists_tip_scale_of_mem member
  have vector := congrArg (fun z : E => z - q) at_tip
  simp only [add_sub_cancel_left] at vector
  refine ⟨(1 - T.start) * a,
    mul_nonneg (sub_nonneg.mpr T.start_le) positive.le, ?_⟩
  calc
    T.tip - p = T.tip - (q + T.start • (T.tip - q)) :=
      congrArg (fun z : E => T.tip - z) T.seed_eq
    _ = (1 - T.start) • (T.tip - q) := by module
    _ = (1 - T.start) • (a • (x - q)) := congrArg (fun z : E => (1 - T.start) • z) vector.symm
    _ = _ := smul_smul _ _ _

/-- The inner boundary may have flat sides; convexity and the interior source suffice. -/
theorem inner_frontier_eq_of_members (convex : Convex ℝ B) (origin : q ∈ interior B)
    (first : x ∈ frontier B) (last : y ∈ frontier B)
    (first_member : x ∈ T.carrier) (last_member : y ∈ T.carrier) : x = y := by
  obtain ⟨a, apos, first_scale⟩ := T.exists_tip_scale_of_mem first_member
  obtain ⟨b, bpos, last_scale⟩ := T.exists_tip_scale_of_mem last_member
  exact frontier_eq_of_radial_rays_meet convex origin first last apos bpos
    (first_scale.trans last_scale.symm)

end Unfoldings.RadialClipTail
