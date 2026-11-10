module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Radial distance along an entire segment

An outward scalar product characterizes monotonicity on all points of a
segment. Comparing the two endpoint distances alone is insufficient.
-/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dist_lineMap_sq (a b c : E) (t : ℝ) :
    dist a (AffineMap.lineMap b c t) ^ 2 = dist a b ^ 2 +
      2 * t * inner ℝ (b - a) (c - b) + t ^ 2 * ‖c - b‖ ^ 2 := by
  simp only [dist_eq_norm', AffineMap.lineMap_apply_module']
  have expression : t • (c - b) + b - a = (b - a) + t • (c - b) := by abel
  rw [expression, norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- An outward edge increases distance at every parameter, not just at its endpoints. -/
theorem dist_lineMap_le_of_inner_nonneg (a b c : E)
    (outward : 0 ≤ inner ℝ (b - a) (c - b)) {t s : ℝ} (nonnegative : 0 ≤ t) (ordered : t ≤ s) :
    dist a (AffineMap.lineMap b c t) ≤ dist a (AffineMap.lineMap b c s) := by
  have factor : 0 ≤ (s - t) *
      (2 * inner ℝ (b - a) (c - b) + (s + t) * ‖c - b‖ ^ 2) :=
    mul_nonneg (sub_nonneg.mpr ordered)
      (add_nonneg (mul_nonneg (by norm_num) outward)
        (mul_nonneg (by linarith) (sq_nonneg _)))
  have first := dist_lineMap_sq a b c t
  have last := dist_lineMap_sq a b c s
  have delta : dist a (AffineMap.lineMap b c s) ^ 2 -
      dist a (AffineMap.lineMap b c t) ^ 2 =
      (s - t) * (2 * inner ℝ (b - a) (c - b) + (s + t) * ‖c - b‖ ^ 2) := by
    rw [first, last]
    ring
  nlinarith [dist_nonneg (x := a) (y := AffineMap.lineMap b c t),
    dist_nonneg (x := a) (y := AffineMap.lineMap b c s)]

/-- A nonconstant outward edge strictly increases distance along its whole length. -/
theorem dist_lineMap_lt_of_inner_nonneg (a b c : E)
    (outward : 0 ≤ inner ℝ (b - a) (c - b)) (different : b ≠ c)
    {t s : ℝ} (nonnegative : 0 ≤ t) (ordered : t < s) :
    dist a (AffineMap.lineMap b c t) < dist a (AffineMap.lineMap b c s) := by
  have length_pos : 0 < ‖c - b‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr different.symm))
  have factor : 0 < (s - t) *
      (2 * inner ℝ (b - a) (c - b) + (s + t) * ‖c - b‖ ^ 2) :=
    mul_pos (sub_pos.mpr ordered)
      (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) outward)
        (mul_pos (by linarith) length_pos))
  have first := dist_lineMap_sq a b c t
  have last := dist_lineMap_sq a b c s
  have delta : dist a (AffineMap.lineMap b c s) ^ 2 -
      dist a (AffineMap.lineMap b c t) ^ 2 =
      (s - t) * (2 * inner ℝ (b - a) (c - b) + (s + t) * ‖c - b‖ ^ 2) := by
    rw [first, last]
    ring
  nlinarith [dist_nonneg (x := a) (y := AffineMap.lineMap b c t),
    dist_nonneg (x := a) (y := AffineMap.lineMap b c s)]

/-- Whole-segment radial monotonicity forces the initial outward scalar product. -/
theorem inner_nonneg_of_monotone_dist_lineMap (a b c : E)
    (monotone : Monotone (fun t : unitInterval => dist a (AffineMap.lineMap b c (t : ℝ)))) :
    0 ≤ inner ℝ (b - a) (c - b) := by
  by_contra negative
  have negative : inner ℝ (b - a) (c - b) < 0 := lt_of_not_ge negative
  let h := inner ℝ (b - a) (c - b)
  let q := ‖c - b‖ ^ 2
  let t := min 1 (-h / (q + 1))
  have qnonneg : 0 ≤ q := sq_nonneg _
  have positive : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr negative) (by linarith))
  have small : t ≤ 1 := min_le_left _ _
  have product : t * (q + 1) ≤ -h :=
    (le_div_iff₀ (by linarith : 0 < q + 1)).mp (min_le_right _ _)
  have bound := monotone (show (0 : unitInterval) ≤ ⟨t, positive.le, small⟩ from positive.le)
  have base : dist a b ≤ dist a (AffineMap.lineMap b c t) := by
    change dist a (AffineMap.lineMap b c (0 : ℝ)) ≤ _ at bound
    simpa only [AffineMap.lineMap_apply_zero] using bound
  have formula := dist_lineMap_sq a b c t
  have scalar : t * (2 * h + t * q) < 0 :=
    mul_neg_of_pos_of_neg positive (by nlinarith)
  have delta : dist a (AffineMap.lineMap b c t) ^ 2 - dist a b ^ 2 = t * (2 * h + t * q) := by
    rw [formula]
    dsimp [h, q]
    ring
  nlinarith [dist_nonneg (x := a) (y := b), dist_nonneg (x := a) (y := AffineMap.lineMap b c t)]

theorem monotone_dist_lineMap_iff (a b c : E) :
    Monotone (fun t : unitInterval => dist a (AffineMap.lineMap b c (t : ℝ))) ↔
      0 ≤ inner ℝ (b - a) (c - b) := by
  constructor
  · exact inner_nonneg_of_monotone_dist_lineMap a b c
  · intro outward t s ordered
    exact dist_lineMap_le_of_inner_nonneg a b c outward t.property.1 ordered

end Unfoldings
