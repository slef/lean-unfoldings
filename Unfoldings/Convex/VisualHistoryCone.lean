module

public import Unfoldings.Convex.HistoryCone
public import Mathlib.Data.Fin.VecNotation

/-! An exact angular description of the positive polar of two planar viewing rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry Real

private theorem planar_parseval {x y : Plane} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (perpendicular : inner ℝ x y = 0) (d : Plane) :
    inner ℝ x d ^ 2 + inner ℝ y d ^ 2 = ‖d‖ ^ 2 := by
  let pair : Fin 2 → Plane := ![x, y]
  have orthonormal : Orthonormal ℝ pair := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pair, hx, hy, perpendicular,
        show inner ℝ y x = 0 from (real_inner_comm x y).trans perpendicular]
  have card : Fintype.card (Fin 2) = Module.finrank ℝ Plane := by simp [Plane]
  let basis := basisOfOrthonormalOfCardEqFinrank orthonormal card
  let B := basis.toOrthonormalBasis
    (show Orthonormal ℝ basis from
      coe_basisOfOrthonormalOfCardEqFinrank orthonormal card ▸ orthonormal)
  have coe : (B : Fin 2 → Plane) = pair :=
    (Module.Basis.coe_toOrthonormalBasis _ _).trans
      (coe_basisOfOrthonormalOfCardEqFinrank orthonormal card)
  have h := B.sum_inner_mul_inner d d
  simp only [Fin.sum_univ_two, coe, pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm x d, real_inner_comm y d, ← pow_two, ← pow_two] at h
  exact h

/-- The intersection of the two positive half-planes is the angular sector
centered at the sum of the unit normals, with aperture the supplement of their angle. -/
theorem positivePolar_pair_iff_angle {u v z : Plane} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (distinct : 0 < angle u v) (short : angle u v < π) (z_ne : z ≠ 0) :
    (0 ≤ inner ℝ u z ∧ 0 ≤ inner ℝ v z) ↔ angle (u + v) z ≤ (π - angle u v) / 2 := by
  let a := u + v
  let b := u - v
  have u_ne := norm_ne_zero_iff.mp (by simp [hu] : ‖u‖ ≠ 0)
  have an : a ≠ 0 := by
    intro zero
    have eq : v = (-1 : ℝ) • u := by
      rw [neg_one_smul]
      exact eq_neg_of_add_eq_zero_right zero
    exact short.ne (angle_eq_pi_iff.mpr ⟨u_ne, -1, by norm_num, eq⟩)
  have bn : b ≠ 0 := by
    intro zero
    have eq : v = (1 : ℝ) • u := by
      simpa only [one_smul] using (sub_eq_zero.mp zero).symm
    exact distinct.ne' (angle_eq_zero_iff.mpr ⟨u_ne, 1, by norm_num, eq⟩)
  have ap := norm_pos_iff.mpr an
  have bp := norm_pos_iff.mpr bn
  have orthogonal : inner ℝ a b = 0 := by
    simp only [a, b, inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, hu, hv,
      real_inner_comm v u]
    ring
  have parseval := planar_parseval (x := ‖a‖⁻¹ • a) (y := ‖b‖⁻¹ • b)
    (by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ap.le), inv_mul_cancel₀ ap.ne'])
    (by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr bp.le), inv_mul_cancel₀ bp.ne'])
    (by rw [real_inner_smul_left, real_inner_smul_right, orthogonal]; ring) z
  rw [real_inner_smul_left, real_inner_smul_left] at parseval
  let X := inner ℝ a z
  let Y := inner ℝ b z
  change (‖a‖⁻¹ * X) ^ 2 + (‖b‖⁻¹ * Y) ^ 2 = ‖z‖ ^ 2 at parseval
  have scaled : ‖b‖ ^ 2 * X ^ 2 + ‖a‖ ^ 2 * Y ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖z‖ ^ 2 := by
    field_simp [ap.ne', bp.ne'] at parseval
    linear_combination parseval
  have sum_sq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 4 := by
    simp only [a, b, norm_add_pow_two_real, norm_sub_pow_two_real, hu, hv]
    ring
  let w := (π - angle u v) / 2
  have w_nonneg : 0 ≤ w := by dsimp [w]; linarith
  have w_half : w ≤ π / 2 := by dsimp [w]; linarith
  have cos_w : cos w ^ 2 = ‖b‖ ^ 2 / 4 := by
    have half : π / 2 - angle u v / 2 = w := by dsimp [w]; ring
    dsimp only [b]
    rw [← half, Real.cos_pi_div_two_sub, norm_sub_pow_two_real, hu, hv,
      inner_eq_cos_angle_of_norm_eq_one hu hv]
    have ht := cos_two_mul_eq_one_sub (angle u v / 2)
    rw [show 2 * (angle u v / 2) = angle u v by ring] at ht
    linarith
  let margin := cos w * (‖a‖ * ‖z‖)
  have margin_nonneg : 0 ≤ margin := by
    exact mul_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], w_half⟩) (by positivity)
  have difference : X ^ 2 - margin ^ 2 = (‖a‖ ^ 2 / 4) * (X ^ 2 - Y ^ 2) := by
    dsimp only [margin]
    rw [mul_pow, mul_pow, cos_w]
    linear_combination (1 / 4 : ℝ) * scaled - X ^ 2 / 4 * sum_sq
  have squared : margin ^ 2 ≤ X ^ 2 ↔ Y ^ 2 ≤ X ^ 2 := by
    have h : 0 < ‖a‖ ^ 2 / 4 := by positivity
    rw [← sub_nonneg, difference, mul_nonneg_iff_of_pos_left h, sub_nonneg]
  have split_x : X = inner ℝ u z + inner ℝ v z := inner_add_left _ _ _
  have split_y : Y = inner ℝ u z - inner ℝ v z := inner_sub_left _ _ _
  change _ ↔ angle a z ≤ w
  rw [angle_le_iff_cos_mul_norm_le an z_ne w_nonneg (by linarith [pi_pos])]
  change _ ↔ margin ≤ X
  constructor
  · rintro ⟨first, last⟩
    have hx : 0 ≤ X := by linarith
    have y_le : |Y| ≤ X := abs_le.mpr ⟨by linarith, by linarith⟩
    apply (sq_le_sq₀ margin_nonneg hx).mp (squared.mpr ?_)
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) y_le 2)
  · intro le
    have hx := margin_nonneg.trans le
    have hy := squared.mp ((sq_le_sq₀ margin_nonneg hx).mpr le)
    have y_le : |Y| ≤ X := (sq_le_sq₀ (abs_nonneg _) hx).mp (by simpa only [sq_abs] using hy)
    obtain ⟨left, right⟩ := abs_le.mp y_le
    constructor <;> linarith

namespace SlopeEnvelope

/-- Extremal viewing rays reduce the whole progress-body support test to two
half-planes. Their opposite positive polar is exactly the adaptive history cone. -/
theorem historyCone_iff_angle_of_extremal_rays {L : Set Plane} {p u v z : Plane}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (distinct : 0 < angle u v) (short : angle u v < π)
    (first : ∃ w ∈ L, ∃ t : ℝ, 0 < t ∧ p - w = t • u)
    (last : ∃ w ∈ L, ∃ t : ℝ, 0 < t ∧ p - w = t • v)
    (enclose : ∀ w ∈ L, InDirectionWedge u v (p - w))
    (z_ne : z ≠ 0) :
    z ∈ historyCone L p ↔ angle (u + v) z ≤ (π - angle u v) / 2 := by
  rw [← positivePolar_pair_iff_angle hu hv distinct short z_ne]
  constructor
  · intro cone
    have heading {x : Plane} (bank : ∃ w ∈ L, ∃ t : ℝ, 0 < t ∧ p - w = t • x) :
        0 ≤ inner ℝ x z := by
      obtain ⟨w, hw, t, ht, equal⟩ := bank
      have support : 0 ≤ inner ℝ (p - w) z := by
        rw [inner_sub_left, sub_nonneg]
        exact cone w hw
      rw [equal, real_inner_smul_left] at support
      exact nonneg_of_mul_nonneg_right support ht
    exact ⟨heading first, heading last⟩
  · rintro ⟨first, last⟩ w hw
    obtain ⟨s, t, hs, ht, equal⟩ := enclose w hw
    have support : 0 ≤ inner ℝ (p - w) z := by
      rw [equal, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      exact add_nonneg (mul_nonneg hs first) (mul_nonneg ht last)
    simpa only [inner_sub_left, sub_nonneg] using support

end SlopeEnvelope
end Unfoldings
