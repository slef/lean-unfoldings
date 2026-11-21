module

public import Unfoldings.Geometry.MinorArcConnectivity

/-! Closed minor arcs are the spherical parts of cones on their endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open NormedSpace

theorem mem_closedMinorArc_iff_nonnegative_combination {u v x : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (nonantipodal : u + v ≠ 0) :
    x ∈ closedMinorArc u v ↔
      ‖x‖ = 1 ∧ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v := by
  constructor
  · intro hx
    have unit : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        closedMinorArc_subset_sphere hu hv nonantipodal hx
    refine ⟨unit, ?_⟩
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨1, 0, zero_le_one, le_rfl, by simp⟩
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨0, 1, le_rfl, zero_le_one, by simp⟩
    obtain ⟨t, ht, rfl⟩ := hx
    let c := (1 - t) • u + t • v
    have d : 0 ≤ ‖c‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    refine ⟨‖c‖⁻¹ * (1 - t), ‖c‖⁻¹ * t, mul_nonneg d (sub_nonneg.mpr ht.2.le),
      mul_nonneg d ht.1.le, ?_⟩
    change NormedSpace.normalize c = _
    rw [NormedSpace.normalize]
    dsimp only [c]
    rw [smul_add, smul_smul, smul_smul]
  · rintro ⟨unit, a, b, ha, hb, eq⟩
    have x_ne : x ≠ 0 := by
      intro zero
      rw [zero, norm_zero] at unit
      norm_num at unit
    rcases eq_or_lt_of_le ha with azero | apos
    · have beq : b = 1 := by
        rw [← azero, zero_smul, zero_add] at eq
        rw [eq, norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hb, mul_one] at unit
        exact unit
      exact Set.mem_insert_of_mem _ (Set.mem_insert_iff.mpr
        (.inl (by simpa [← azero, beq] using eq)))
    rcases eq_or_lt_of_le hb with bzero | bpos
    · have aeq : a = 1 := by
        rw [← bzero, zero_smul, add_zero] at eq
        rw [eq, norm_smul, hu, Real.norm_eq_abs, abs_of_nonneg ha, mul_one] at unit
        exact unit
      exact Set.mem_insert_iff.mpr (.inl (by simpa [← bzero, aeq] using eq))
    let t := b / (a + b)
    have ab : 0 < a + b := add_pos apos bpos
    have interval : t ∈ Set.Ioo 0 1 := ⟨div_pos bpos ab,
      (div_lt_one ab).mpr (lt_add_of_pos_left b apos)⟩
    have vector : (1 - t) • u + t • v = (a + b)⁻¹ • x := by
      rw [eq, smul_add, smul_smul, smul_smul]
      have first : 1 - t = (a + b)⁻¹ * a := by
        dsimp [t]
        field_simp
        ring
      rw [first]
      dsimp only [t]
      rw [div_eq_inv_mul]
    refine Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨t, interval, ?_⟩)
    rw [vector, normalize_smul_of_pos (inv_pos.mpr ab), normalize_eq_self_of_norm_eq_one unit]

end Unfoldings
