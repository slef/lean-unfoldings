module

public import Unfoldings.Geometry.RadialChordBounds
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Small equilateral triangles remain acute after radial projection. -/

@[expose] public section

namespace Unfoldings

open NormedSpace InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The chord triangle is acute at the first corner when the height and
radius bounds ensure that its two adjacent squared chords exceed the opposite one. -/
theorem inner_normalized_edges_pos_of_equilateral {n a b c : E} {h L : ℝ}
    (unit : ‖n‖ = 1) (heightA : inner ℝ n a = h) (heightB : inner ℝ n b = h)
    (heightC : inner ℝ n c = h) (radiusA : ‖a‖ ≤ 1) (radiusB : ‖b‖ ≤ 1)
    (radiusC : ‖c‖ ≤ 1) (hpos : 0 < h) (hle : h ≤ 1) (Lpos : 0 < L)
    (ab : ‖b - a‖ = L) (ac : ‖c - a‖ = L) (bc : ‖b - c‖ = L)
    (small : 2 * h ^ 2 * L < (2 * h ^ 2 - 1) * h) :
    0 < inner ℝ (normalize b - normalize a) (normalize c - normalize a) := by
  have ab' := (normalized_chord_sq_bounds unit heightB heightA radiusB radiusA hpos hle).1
  have ac' := (normalized_chord_sq_bounds unit heightC heightA radiusC radiusA hpos hle).1
  have bc' := (normalized_chord_sq_bounds unit heightB heightC radiusB radiusC hpos hle).2
  rw [ab] at ab'
  rw [ac] at ac'
  rw [bc] at bc'
  have radial {v : E} (hv : inner ℝ n v = h) : h ≤ ‖v‖ := by
    have h' := abs_real_inner_le_norm n v
    rwa [unit, one_mul, hv, abs_of_pos hpos] at h'
  have cmp := radial heightA
  have hterm : 0 ≤ 2 * h ^ 2 - 1 := by
    by_contra! bad
    have impossible : (2 * h ^ 2 - 1) * h < 0 := mul_neg_of_neg_of_pos bad hpos
    have left : 0 ≤ 2 * h ^ 2 * L := by positivity
    linarith only [small, impossible, left]
  have lowerB : ‖a‖ - L ≤ ‖b‖ := by
    have h := norm_sub_norm_le a b
    rw [norm_sub_rev, ab] at h
    linarith only [h]
  have lowerC : ‖a‖ - L ≤ ‖c‖ := by
    have h := norm_sub_norm_le a c
    rw [norm_sub_rev, ac] at h
    linarith only [h]
  have strong : ‖a‖ < h ^ 2 * (‖b‖ + ‖c‖) := by
    have left := mul_le_mul_of_nonneg_left
      (add_le_add lowerB lowerC) (sq_nonneg h)
    have right := mul_le_mul_of_nonneg_left cmp hterm
    nlinarith only [left, right, small]
  let scale := ‖a‖ * ‖b‖ * ‖c‖
  have positive : 0 < scale := by
    dsimp [scale]
    exact mul_pos (mul_pos (hpos.trans_le cmp) (hpos.trans_le (radial heightB)))
      (hpos.trans_le (radial heightC))
  have boundAB : h ^ 2 * L ^ 2 * ‖c‖ ≤ scale * ‖normalize b - normalize a‖ ^ 2 := by
    convert mul_le_mul_of_nonneg_right ab' (norm_nonneg c) using 1
    dsimp [scale]
    ring
  have boundAC : h ^ 2 * L ^ 2 * ‖b‖ ≤ scale * ‖normalize c - normalize a‖ ^ 2 := by
    convert mul_le_mul_of_nonneg_right ac' (norm_nonneg b) using 1
    dsimp [scale]
    ring
  have boundBC : scale * ‖normalize b - normalize c‖ ^ 2 ≤ L ^ 2 * ‖a‖ := by
    convert mul_le_mul_of_nonneg_right bc' (norm_nonneg a) using 1
    dsimp [scale]
    ring
  have strict := mul_lt_mul_of_pos_left strong (pow_pos Lpos 2)
  have chord : ‖normalize b - normalize c‖ ^ 2 <
      ‖normalize b - normalize a‖ ^ 2 + ‖normalize c - normalize a‖ ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left positive).mp
    nlinarith only [strict, boundAB, boundAC, boundBC]
  have diff : normalize b - normalize c =
      (normalize b - normalize a) - (normalize c - normalize a) := by abel
  rw [diff, norm_sub_sq_real] at chord
  linarith only [chord]

/-- With the same smallness condition, radial normalization preserves the
acute angle at the first corner of the equilateral triangle. -/
theorem angle_normalized_edges_lt_pi_div_two_of_equilateral {n a b c : E} {h L : ℝ}
    (unit : ‖n‖ = 1) (heightA : inner ℝ n a = h) (heightB : inner ℝ n b = h)
    (heightC : inner ℝ n c = h) (radiusA : ‖a‖ ≤ 1) (radiusB : ‖b‖ ≤ 1)
    (radiusC : ‖c‖ ≤ 1) (hpos : 0 < h) (hle : h ≤ 1) (Lpos : 0 < L)
    (ab : ‖b - a‖ = L) (ac : ‖c - a‖ = L) (bc : ‖b - c‖ = L)
    (small : 2 * h ^ 2 * L < (2 * h ^ 2 - 1) * h) :
    angle (normalize b - normalize a) (normalize c - normalize a) < Real.pi / 2 := by
  have h := inner_normalized_edges_pos_of_equilateral unit heightA heightB heightC
    radiusA radiusB radiusC hpos hle Lpos ab ac bc small
  exact lt_of_not_ge (fun wide => h.not_ge (inner_nonpos_iff_pi_div_two_le_angle.mpr wide))

end Unfoldings
