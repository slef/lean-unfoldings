module

public import Unfoldings.Geometry.RadialLocality

/-! Actual attachment at a local conical point is detected by a nonempty direction set. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A locally homogeneous direction set meets every neighborhood of its apex
exactly when it contains a direction. The direction may be zero. -/
theorem mem_closure_iff_nonempty_of_local_cone {s cone : Set E} {x : E}
    (radial : ∀ (v : E) (t : ℝ), 0 < t → (t • v ∈ cone ↔ v ∈ cone))
    {r : ℝ} (positive : 0 < r)
    (local_eq : ∀ z, dist z x < r → (z ∈ s ↔ z - x ∈ cone)) :
    x ∈ closure s ↔ cone.Nonempty := by
  constructor
  · intro member
    obtain ⟨z, hz, near⟩ := Metric.mem_closure_iff.mp member r positive
    exact ⟨z - x, (local_eq z (dist_comm x z ▸ near)).mp hz⟩
  · rintro ⟨v, hv⟩
    apply Metric.mem_closure_iff.mpr
    intro ε εpos
    obtain ⟨t, tpos, near⟩ := exists_positive_lineMap_mem_ball x (x + v)
      (lt_min positive εpos)
    have displacement : AffineMap.lineMap x (x + v) t - x = t • v := by
      simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_sub_cancel_right]
    refine ⟨AffineMap.lineMap x (x + v) t, ?_, ?_⟩
    · apply (local_eq _ (near.trans_le (min_le_left _ _))).mpr
      rw [displacement]
      exact (radial v t tpos).mpr hv
    · rw [dist_comm]
      exact near.trans_le (min_le_right _ _)

end Unfoldings
