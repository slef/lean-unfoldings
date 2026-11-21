module

public import Unfoldings.Geometry.SphericalConvex
public import Unfoldings.Geometry.MinorArcConnectivity

/-! The gnomonic image of a planar segment is the actual closed spherical minor arc. -/

@[expose] public section

noncomputable section

namespace Unfoldings

private theorem normalize_image_segment_eq_closedMinorArc {u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    NormedSpace.normalize '' segment ℝ u v = closedMinorArc u v := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, b, ha, hb, sum, rfl⟩, rfl⟩
    by_cases zero_a : a = 0
    · have one_b : b = 1 := by linarith
      simp only [zero_a, one_b, zero_smul, one_smul, zero_add,
        NormedSpace.normalize_eq_self_of_norm_eq_one hv, closedMinorArc, Set.mem_insert_iff,
        true_or, or_true]
    · by_cases zero_b : b = 0
      · have one_a : a = 1 := by linarith
        simp only [zero_b, one_a, zero_smul, one_smul, add_zero,
          NormedSpace.normalize_eq_self_of_norm_eq_one hu, closedMinorArc, Set.mem_insert_iff,
          true_or]
      · have relation : a = 1 - b := by linarith
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (show NormedSpace.normalize (a • u + b • v) ∈ openMinorArc u v from
            ⟨b, ⟨lt_of_le_of_ne hb (Ne.symm zero_b),
              by linarith [lt_of_le_of_ne ha (Ne.symm zero_a)]⟩, by rw [← relation]⟩))
  · intro on_arc
    rcases Set.mem_insert_iff.mp on_arc with same | on_arc
    · exact ⟨u, left_mem_segment ℝ _ _,
        (NormedSpace.normalize_eq_self_of_norm_eq_one hu).trans same.symm⟩
    · rcases Set.mem_insert_iff.mp on_arc with same | on_arc
      · exact ⟨v, right_mem_segment ℝ _ _,
          (NormedSpace.normalize_eq_self_of_norm_eq_one hv).trans same.symm⟩
      · obtain ⟨t, ht, rfl⟩ := on_arc
        exact ⟨_, ⟨1 - t, t, sub_nonneg.mpr ht.2.le, ht.1.le, by ring, rfl⟩, rfl⟩

private theorem normalize_image_segment_smul_subset {u v : Space} {s t : ℝ}
    (s_pos : 0 < s) (t_pos : 0 < t) :
    NormedSpace.normalize '' segment ℝ (s • u) (t • v) ⊆
      NormedSpace.normalize '' segment ℝ u v := by
  rintro _ ⟨_, ⟨a, b, ha, hb, sum, rfl⟩, rfl⟩
  let total := a * s + b * t
  have total_pos : 0 < total := by
    have a_or_b : 0 < a ∨ 0 < b := by
      by_contra! both
      linarith [both.1, both.2]
    rcases a_or_b with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h s_pos) (mul_nonneg hb t_pos.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha s_pos.le) (mul_pos h t_pos)
  have coefficient_sum : (a * s / total) + (b * t / total) = 1 := by
    rw [← add_div]
    exact div_self total_pos.ne'
  refine ⟨(a * s / total) • u + (b * t / total) • v,
    ⟨_, _, div_nonneg (mul_nonneg ha s_pos.le) total_pos.le,
      div_nonneg (mul_nonneg hb t_pos.le) total_pos.le, coefficient_sum, rfl⟩, ?_⟩
  have scaled : (a * s / total) • u + (b * t / total) • v =
      total⁻¹ • (a • (s • u) + b • (t • v)) := by
    simp only [smul_add, smul_smul, div_eq_mul_inv]
    rw [mul_comm (a * s), mul_comm (b * t)]
  rw [scaled, NormedSpace.normalize_smul_of_pos (inv_pos.mpr total_pos)]

private theorem normalize_image_segment_smul_eq {u v : Space} {s t : ℝ}
    (s_pos : 0 < s) (t_pos : 0 < t) :
    NormedSpace.normalize '' segment ℝ (s • u) (t • v) =
      NormedSpace.normalize '' segment ℝ u v := by
  apply (normalize_image_segment_smul_subset s_pos t_pos).antisymm
  have reverse := normalize_image_segment_smul_subset (u := s • u) (v := t • v)
    (inv_pos.mpr s_pos) (inv_pos.mpr t_pos)
  simpa only [smul_smul, inv_mul_cancel₀ s_pos.ne', inv_mul_cancel₀ t_pos.ne', one_smul]
    using reverse

/-- Rescaling a minor arc to an affine height-one plane yields the closed
segment joining its rescaled endpoints. -/
theorem image_heightOne_closedMinorArc {u v a : Space} (uu : ‖u‖ = 1) (vu : ‖v‖ = 1)
    (up : 0 < inner ℝ u a) (vp : 0 < inner ℝ v a) :
    (fun n : Space => (inner ℝ n a)⁻¹ • n) '' closedMinorArc u v =
      segment ℝ ((inner ℝ u a)⁻¹ • u) ((inner ℝ v a)⁻¹ • v) := by
  let x := (inner ℝ u a)⁻¹ • u
  let y := (inner ℝ v a)⁻¹ • v
  have x_height : inner ℝ x a = 1 := by
    dsimp only [x]
    rw [real_inner_smul_left, inv_mul_cancel₀ up.ne']
  have y_height : inner ℝ y a = 1 := by
    dsimp only [y]
    rw [real_inner_smul_left, inv_mul_cancel₀ vp.ne']
  have arc : NormedSpace.normalize '' segment ℝ x y = closedMinorArc u v :=
    (normalize_image_segment_smul_eq (inv_pos.mpr up) (inv_pos.mpr vp)).trans
      (normalize_image_segment_eq_closedMinorArc uu vu)
  have recover {z : Space} (mem : z ∈ segment ℝ x y) :
      (inner ℝ (NormedSpace.normalize z) a)⁻¹ • NormedSpace.normalize z = z := by
    have height : inner ℝ z a = 1 := by
      obtain ⟨s, t, _, _, sum, rfl⟩ := mem
      have hs : inner ℝ (s • x) a = s := by
        rw [real_inner_smul_left, x_height, mul_one]
      have ht : inner ℝ (t • y) a = t := by
        rw [real_inner_smul_left, y_height, mul_one]
      rw [inner_add_left, hs, ht]
      exact sum
    have hs : inner ℝ (NormedSpace.normalize z) a = ‖z‖⁻¹ := by
      rw [NormedSpace.normalize, real_inner_smul_left, height, mul_one]
    rw [hs, inv_inv, NormedSpace.norm_smul_normalize]
  change (fun n : Space => (inner ℝ n a)⁻¹ • n) '' closedMinorArc u v = segment ℝ x y
  rw [← arc, Set.image_image]
  ext p
  constructor
  · rintro ⟨z, h, rfl⟩
    change (inner ℝ (NormedSpace.normalize z) a)⁻¹ • NormedSpace.normalize z ∈ segment ℝ x y
    rwa [recover h]
  · intro h
    exact ⟨p, h, recover h⟩

namespace Cap

/-- Normalizing the upward affine lift of a straight segment preserves precisely
the minor-arc carrier between the two unit endpoint images. -/
theorem gnomonicNormal_image_segment (u v : Plane) :
    gnomonicNormal '' segment ℝ u v = closedMinorArc (gnomonicNormal u) (gnomonicNormal v) := by
  have image_lift : northLift '' segment ℝ u v = segment ℝ (northLift u) (northLift v) := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, b, ha, hb, sum, rfl⟩, rfl⟩
      exact ⟨a, b, ha, hb, sum, (northLift_combo u v a b sum).symm⟩
    · rintro ⟨a, b, ha, hb, sum, rfl⟩
      exact ⟨a • u + b • v, ⟨a, b, ha, hb, sum, rfl⟩, northLift_combo u v a b sum⟩
  have rescale (p : Plane) : northLift p = ‖northLift p‖ • gnomonicNormal p :=
    (NormedSpace.norm_smul_normalize _).symm
  have comp : NormedSpace.normalize '' (northLift '' segment ℝ u v) =
      gnomonicNormal '' segment ℝ u v := by rw [Set.image_image]; rfl
  rw [← comp, image_lift, rescale u, rescale v,
    normalize_image_segment_smul_eq (norm_pos_iff.mpr (northLift_ne_zero u))
      (norm_pos_iff.mpr (northLift_ne_zero v))]
  exact normalize_image_segment_eq_closedMinorArc (gnomonicNormal_unit u) (gnomonicNormal_unit v)

end Cap
end Unfoldings
