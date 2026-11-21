module

public import Unfoldings.Geometry.ConvexChordTurns
public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Tactic.Module

/-! A chord line meets the boundary of a strictly convex set only at its ends. -/

@[expose] public section

noncomputable section

namespace Unfoldings

attribute [local instance] Complex.finrank_real_complex_fact

private theorem smul_eq_of_areaForm_zero {u v : ℂ} (u_ne : u ≠ 0)
    (zero : Complex.orientation.areaForm u v = 0) : ∃ r : ℝ, v = r • u := by
  let r := inner ℝ u v / ‖u‖ ^ 2
  let w := v - r • u
  have norm_pos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr u_ne) _
  have orthogonal : inner ℝ u w = 0 := by
    change inner ℝ u (v - r • u) = 0
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    unfold r
    rw [div_mul_cancel₀ _ norm_pos.ne', sub_self]
  have parallel : Complex.orientation.areaForm u w = 0 := by
    change Complex.orientation.areaForm u (v - r • u) = 0
    rw [map_sub, map_smul, zero, Complex.orientation.areaForm_apply_self, smul_zero, sub_zero]
  have identity := Complex.orientation.inner_sq_add_areaForm_sq u w
  rw [orthogonal, parallel] at identity
  have norm_zero : ‖w‖ ^ 2 = 0 := by
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left norm_pos.ne'
  rw [pow_two] at norm_zero
  exact ⟨r, sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp norm_zero).elim id id))⟩

/-- In a strictly convex closed planar region, no third frontier point lies
on the straight line through two different frontier points. -/
theorem areaForm_chord_ne_zero_of_frontier {K : Set ℂ} (closed : IsClosed K)
    (strict : StrictConvex ℝ K) {x y z : ℂ}
    (hx : x ∈ frontier K) (hy : y ∈ frontier K) (hz : z ∈ frontier K)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) :
    Complex.orientation.areaForm (y - x) (z - x) ≠ 0 := by
  intro zero
  obtain ⟨r, along⟩ := smul_eq_of_areaForm_zero (sub_ne_zero.mpr xy.symm) zero
  have z_eq : z = r • (y - x) + x := by rw [← along, sub_add_cancel]
  have inK (p : ℂ) (h : p ∈ frontier K) : p ∈ K := closed.frontier_subset h
  have ruled_out {a b c : ℂ} (ha : a ∈ frontier K) (hb : b ∈ frontier K)
      (hc : c ∈ frontier K) (ab : a ≠ b) {t : ℝ} (ht : t ∈ Set.Ioo 0 1)
      (eq : AffineMap.lineMap a b t = c) : False := by
    have mem : c ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht, eq⟩
    exact hc.2 (strict.openSegment_subset (inK a ha) (inK b hb) ab mem)
  have ne_zero : r ≠ 0 := fun h => xz (by rw [z_eq, h, zero_smul, zero_add])
  have ne_one : r ≠ 1 := fun h => yz (by rw [z_eq, h, one_smul, sub_add_cancel])
  rcases lt_or_gt_of_ne ne_zero with r_neg | r_pos
  · have denom : 0 < 1 - r := by linarith
    have t : -r / (1 - r) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨div_pos (neg_pos.mpr r_neg) denom, (div_lt_one denom).mpr (by linarith)⟩
    apply ruled_out hz hy hx yz.symm t
    have direction : y - z = (1 - r) • (y - x) := by
      rw [z_eq]
      module
    rw [AffineMap.lineMap_apply_module', direction, smul_smul,
      div_mul_cancel₀ _ denom.ne', z_eq, ← add_assoc, ← add_smul, neg_add_cancel,
      zero_smul, zero_add]
  · rcases lt_or_gt_of_ne ne_one with inside | beyond
    · exact ruled_out hx hy hz xy ⟨r_pos, inside⟩
        ((AffineMap.lineMap_apply_module' x y r).trans z_eq.symm)
    · apply ruled_out hx hz hy xz
        (show r⁻¹ ∈ Set.Ioo (0 : ℝ) 1 from ⟨inv_pos.mpr r_pos, inv_lt_one_of_one_lt₀ beyond⟩)
      rw [AffineMap.lineMap_apply_module', along, smul_smul, inv_mul_cancel₀ ne_zero,
        one_smul, sub_add_cancel]

end Unfoldings
