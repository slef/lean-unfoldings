module

public import Unfoldings.Geometry.RegularPolygonSelector
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.VecNotation

/-! The regular selector is exactly the fan of triangles to its consecutive ring vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real

variable (frame : Plane ≃ₗᵢ[ℝ] ℂ) {k : ℕ}

/-- The last index repeats the first ring vertex. -/
def regularRingVertex (k : ℕ) (radius : ℝ) (j : ℕ) : Plane :=
  radius • frame.symm (polarRay (2 * (j : ℝ) * (π / k)))

private theorem regular_step_bounds (sides : 3 ≤ k) :
    0 < π / (k : ℝ) ∧ 2 * (π / (k : ℝ)) < π := by
  have positive : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have upper : π / (k : ℝ) ≤ π / 3 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by exact_mod_cast sides)
  exact ⟨div_pos pi_pos positive, by linarith only [upper, pi_pos]⟩

private theorem regular_period (sides : 3 ≤ k) :
    (k : ℝ) * (2 * (π / (k : ℝ))) = 2 * π := by
  have nonzero : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [nonzero] <;> ring

private theorem ring_inner_side (R : ℝ) (j : ℕ) (i : Fin k) :
    inner ℝ (regularSideNormal frame i) (regularRingVertex frame k R j) =
      R * cos ((2 * (j : ℝ) - (2 * i.val + 1)) * (π / k)) := by
  rw [regularRingVertex, inner_smul_right]
  change R * inner ℝ (frame.symm _) (frame.symm _) = _
  rw [frame.symm.inner_map_map, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    polarRay_re, polarRay_im, polarRay_re, polarRay_im, mul_neg, sub_neg_eq_add, ← cos_sub]
  congr 2
  ring

/-- All ring vertices, including the repeated endpoint, satisfy every support inequality. -/
theorem regularRingVertex_mem (sides : 3 ≤ k) {R : ℝ} (nonnegative : 0 ≤ R)
    {j : ℕ} (within : j ≤ k) : regularRingVertex frame k R j ∈ regularSlopePolygon frame k R := by
  let x := π / (k : ℝ)
  have positive := (regular_step_bounds sides).1
  intro i
  rw [ring_inner_side]
  apply mul_le_mul_of_nonneg_left _ nonnegative
  let d : ℝ := 2 * (j : ℝ) - (2 * i.val + 1)
  change cos (d * x) ≤ cos x
  have sep : 1 ≤ |d| := by
    rcases le_or_gt j i.val with before | after
    · have le_real : (j : ℝ) ≤ i.val := by exact_mod_cast before
      have negative : d ≤ -1 := by dsimp only [d]; linarith only [le_real]
      rw [abs_of_nonpos (negative.trans (by norm_num))]
      linarith only [negative]
    · have le_real : (i.val : ℝ) + 1 ≤ j := by exact_mod_cast after
      have above : 1 ≤ d := by dsimp only [d]; linarith only [le_real]
      rwa [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans above)]
  have up : |d| ≤ 2 * (k : ℝ) - 1 := by
    have left : (i.val : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
    have right : (j : ℝ) ≤ k := by exact_mod_cast within
    have j_nonneg : (0 : ℝ) ≤ j := by positivity
    have i_nonneg : (0 : ℝ) ≤ i.val := by positivity
    exact abs_le.mpr ⟨by dsimp only [d]; linarith only [left, j_nonneg],
      by dsimp only [d]; linarith only [right, i_nonneg]⟩
  have lower : x ≤ |d * x| := by
    rw [abs_mul, abs_of_pos positive]
    exact (one_mul x).symm.trans_le (mul_le_mul_of_nonneg_right sep positive.le)
  have upper : |d * x| ≤ 2 * π - x := by
    rw [abs_mul, abs_of_pos positive]
    calc
      _ ≤ (2 * (k : ℝ) - 1) * x := mul_le_mul_of_nonneg_right up positive.le
      _ = _ := by linarith only [regular_period sides]
  rw [← cos_abs]
  by_cases near : |d * x| ≤ π
  · exact cos_le_cos_of_nonneg_of_le_pi positive.le near lower
  · rw [← cos_two_pi_sub |d * x|]
    exact cos_le_cos_of_nonneg_of_le_pi positive.le
      (by linarith only [le_of_not_ge near]) (by linarith only [upper])

private theorem regular_sector_direction (sides : 3 ≤ k) (p : Plane) :
    ∃ (i : Fin k) (θ : ℝ), θ ∈ Set.Icc (2 * (i.val : ℝ) * (π / k))
      (2 * ((i.val : ℝ) + 1) * (π / k)) ∧ frame p = ‖p‖ • polarRay θ := by
  let x := π / (k : ℝ)
  have x_pos : 0 < x := (regular_step_bounds sides).1
  have two_pos : 0 < 2 * x := by positivity
  let arg := (frame p).arg
  let θ := if arg < 0 then arg + 2 * π else arg
  have range : 0 ≤ θ ∧ θ < 2 * π := by
    unfold θ
    split_ifs with h
    · exact ⟨by linarith only [Complex.neg_pi_lt_arg (frame p), pi_pos], by linarith only [h]⟩
    · exact ⟨le_of_not_gt h, by linarith only [Complex.arg_le_pi (frame p), pi_pos]⟩
  let index := ⌊θ / (2 * x)⌋₊
  have within : index < k := by
    apply (Nat.floor_lt (div_nonneg range.1 two_pos.le)).2
    exact (div_lt_iff₀ two_pos).2 ((regular_period sides).symm ▸ range.2)
  have earliest := (le_div_iff₀ two_pos).mp (Nat.floor_le (div_nonneg range.1 two_pos.le))
  have latest := (div_lt_iff₀ two_pos).mp (Nat.lt_floor_add_one (θ / (2 * x)))
  refine ⟨⟨index, within⟩, θ, ⟨by linarith only [earliest], by linarith only [latest]⟩, ?_⟩
  have unchanged : polarRay θ = polarRay arg := by
    unfold θ
    split_ifs
    · apply Complex.ext
      · simp only [polarRay_re, cos_add_two_pi]
      · simp only [polarRay_im, sin_add_two_pi]
    · rfl
  rw [unchanged, ← frame.norm_map p]
  apply Complex.ext
  · simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, polarRay_re, Complex.norm_mul_cos_arg, arg]
  · simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, polarRay_im, Complex.norm_mul_sin_arg, arg]

private theorem regularFan_contains (sides : 3 ≤ k) {R : ℝ} (positive : 0 < R)
    {p : Plane} (inside : p ∈ regularSlopePolygon frame k R) :
    ∃ i : Fin k, p ∈ convexHull ℝ
      ({0, regularRingVertex frame k R i.val, regularRingVertex frame k R (i.val + 1)} :
        Set Plane) := by
  let x := π / (k : ℝ)
  have ⟨x_pos, x_small⟩ := regular_step_bounds sides
  obtain ⟨i, θ, sector, polar⟩ := regular_sector_direction frame sides p
  let left := 2 * (i.val : ℝ) * x
  let right := 2 * ((i.val : ℝ) + 1) * x
  have width : right - left = 2 * x := by dsimp only [left, right]; ring
  obtain ⟨c, c_nonneg, d, d_nonneg, direction⟩ :=
    polarRay_mem_positive_span left right θ (by rw [width]; positivity)
      (width.symm ▸ x_small) sector
  let a := ‖p‖ * c / R
  let b := ‖p‖ * d / R
  have a_nonneg : 0 ≤ a := div_nonneg (mul_nonneg (norm_nonneg _) c_nonneg) positive.le
  have b_nonneg : 0 ≤ b := div_nonneg (mul_nonneg (norm_nonneg _) d_nonneg) positive.le
  let l := regularRingVertex frame k R i.val
  let r := regularRingVertex frame k R (i.val + 1)
  have representation : p = a • l + b • r := by
    apply frame.injective
    rw [polar, direction]
    simp only [map_add, map_smul, regularRingVertex, frame.apply_symm_apply, smul_add, smul_smul,
      l, r, a, b, Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ positive.ne']
    rfl
  have left_support : inner ℝ (regularSideNormal frame i) l = R * cos x := by
    dsimp only [l]
    rw [ring_inner_side, show (2 * (i.val : ℝ) - (2 * i.val + 1)) * x = -x by ring,
      cos_neg]
  have right_support : inner ℝ (regularSideNormal frame i) r = R * cos x := by
    dsimp only [r]
    rw [ring_inner_side, Nat.cast_add, Nat.cast_one,
      show (2 * ((i.val : ℝ) + 1) - (2 * i.val + 1)) * x = x by ring]
  have limit := inside i
  rw [representation, inner_add_right, inner_smul_right, inner_smul_right, left_support,
    right_support, ← add_mul] at limit
  have normal_pos : 0 < R * cos x := mul_pos positive (cos_pos_of_mem_Ioo
    ⟨by linarith only [x_pos, pi_pos], by linarith only [x_small]⟩)
  have sum_le : a + b ≤ 1 := (mul_le_mul_iff_of_pos_right normal_pos).mp
    (limit.trans_eq (one_mul _).symm)
  let weight : Fin 3 → ℝ := ![1 - (a + b), a, b]
  let vertex : Fin 3 → Plane := ![0, l, r]
  refine ⟨i, mem_convexHull_of_exists_fintype weight vertex ?_ ?_ ?_ ?_⟩
  · intro j
    fin_cases j
    · exact sub_nonneg.mpr sum_le
    · exact a_nonneg
    · exact b_nonneg
  · simp [weight, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> simp [vertex, l, r]
  · simpa [weight, vertex, Fin.sum_univ_succ] using representation.symm

/-- The exact closed halfplane selector agrees with its straightened polar fan. -/
theorem regularSlopePolygon_eq_iUnion_fan (sides : 3 ≤ k) {R : ℝ} (positive : 0 < R) :
    regularSlopePolygon frame k R = ⋃ i : Fin k, convexHull ℝ
      ({0, regularRingVertex frame k R i.val, regularRingVertex frame k R (i.val + 1)} :
        Set Plane) := by
  apply Set.Subset.antisymm
  · intro p inside
    exact Set.mem_iUnion.mpr (regularFan_contains frame sides positive inside)
  · apply Set.iUnion_subset
    intro i
    let P := regularPolygonSideDirections frame sides positive
    apply convexHull_min (s := _) _ P.convex
    have zero : (0 : Plane) ∈ regularSlopePolygon frame k R := fun j => (P.strict j).le
    intro q mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mem
    rcases mem with rfl | rfl | rfl
    · exact zero
    · exact regularRingVertex_mem frame sides positive.le i.isLt.le
    · exact regularRingVertex_mem frame sides positive.le i.isLt

end Unfoldings
