module

public import Unfoldings.Geometry.RadialTailLabels

/-! Every two positions on a clipped radial tail lie on the same positive source ray. -/

@[expose] public section

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {S : Set E} {q p x y : E} (T : RadialClipTail S q p)

theorem exists_pos_smul_sub_eq_of_members (first : x ∈ T.carrier) (last : y ∈ T.carrier) :
    ∃ a : ℝ, 0 < a ∧ y - q = a • (x - q) := by
  obtain ⟨a, apos, first_scale⟩ := T.exists_tip_scale_of_mem first
  obtain ⟨b, bpos, last_scale⟩ := T.exists_tip_scale_of_mem last
  have same : a • (x - q) = b • (y - q) := by
    have equal := congrArg (fun z : E => z - q) (first_scale.trans last_scale.symm)
    simpa only [add_sub_cancel_left] using equal
  refine ⟨a / b, div_pos apos bpos, ?_⟩
  calc
    y - q = b⁻¹ • (b • (y - q)) := by
      rw [smul_smul, inv_mul_cancel₀ bpos.ne', one_smul]
    _ = b⁻¹ • (a • (x - q)) := congrArg (fun z : E => b⁻¹ • z) same.symm
    _ = (a / b) • (x - q) := by rw [smul_smul, div_eq_mul_inv, mul_comm]

end Unfoldings.RadialClipTail
