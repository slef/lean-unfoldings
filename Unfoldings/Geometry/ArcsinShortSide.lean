module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-! A polynomial enclosure for the short spherical sides used in counting. -/

@[expose] public section

namespace Unfoldings

open Real

private theorem arcsin_majorant_derivative {x : ℝ} (nonnegative : 0 ≤ x) (small : x ≤ 0.574) :
    1 / √(1 - x ^ 2) ≤ 1 + x ^ 2 / 2 + 3 * x ^ 4 / 8 + x ^ 6 / 2 := by
  let u := x ^ 2
  let p := 1 + u / 2 + 3 * u ^ 2 / 8 + u ^ 3 / 2
  let t := √(1 - u)
  have u0 : 0 ≤ u := sq_nonneg _
  have u1 : u ≤ 1 / 3 := (pow_le_pow_left₀ nonnegative small 2).trans (by norm_num)
  have u2 := pow_le_pow_left₀ u0 u1 2
  have u3 := pow_le_pow_left₀ u0 u1 3
  have u4 := pow_le_pow_left₀ u0 u1 4
  have t_pos : 0 < t := sqrt_pos.mpr (by linarith only [u1])
  have p_pos : 0 ≤ p := by dsimp only [p]; positivity
  have bracket : 0 ≤ 3 / 8 - 47 / 64 * u - 17 / 64 * u ^ 2 - u ^ 3 / 8 - u ^ 4 / 4 := by
    linarith only [u1, u2, u3, u4]
  have factored : p ^ 2 * (1 - u) =
      1 + u ^ 3 * (3 / 8 - 47 / 64 * u - 17 / 64 * u ^ 2 - u ^ 3 / 8 - u ^ 4 / 4) := by
    dsimp only [p]
    ring
  have times : 1 ≤ (p * t) ^ 2 := by
    rw [mul_pow, show t ^ 2 = 1 - u from sq_sqrt (by linarith only [u1]), factored]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg u0 _) bracket)
  have h : 1 ≤ p * t := (sq_le_sq₀ zero_le_one (mul_nonneg p_pos t_pos.le)).mp (by
    simpa only [one_pow] using times)
  have bound : 1 / t ≤ p := (div_le_iff₀ t_pos).mpr h
  change 1 / t ≤ 1 + x ^ 2 / 2 + 3 * x ^ 4 / 8 + x ^ 6 / 2
  convert bound using 1
  dsimp only [p, u]
  ring

/-- Inverse sine costs at most the stated polynomial factor on short sides. -/
theorem arcsin_le_short_side_polynomial {x : ℝ} (nonnegative : 0 ≤ x) (small : x ≤ 0.574) :
    arcsin x ≤ x * (1 + x ^ 2 / 6 + x ^ 4 / 10) := by
  let f (x : ℝ) := x + x ^ 3 / 6 + 3 * x ^ 5 / 40 + x ^ 7 / 14 - arcsin x
  have con : Continuous f := by
    unfold f
    fun_prop
  have derivative (t : ℝ) (w : t ∈ Set.Icc 0 (0.574 : ℝ)) :
      HasDerivAt f (1 + t ^ 2 / 2 + 3 * t ^ 4 / 8 + t ^ 6 / 2 - 1 / √(1 - t ^ 2)) t := by
    have n : t ≠ -1 := by linarith only [w.1]
    have p : t ≠ 1 := by linarith only [w.2]
    have d := ((((hasDerivAt_id t).add ((hasDerivAt_pow 3 t).div_const 6)).add
      (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)).add
      ((hasDerivAt_pow 7 t).div_const 14)).sub (hasDerivAt_arcsin n p)
    convert d using 1 <;> first | rfl | (try simp; ring)
  have monotone := monotoneOn_of_deriv_nonneg (convex_Icc 0 (0.574 : ℝ)) con.continuousOn
    (fun t ht => (derivative t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(derivative t (interior_subset ht)).deriv]
      exact sub_nonneg.mpr (arcsin_majorant_derivative (interior_subset ht).1 (interior_subset ht).2))
  have initial : f 0 = 0 := by simp [f]
  have bound := monotone (show (0 : ℝ) ∈ Set.Icc 0 (0.574 : ℝ) from ⟨le_rfl, by norm_num⟩)
    (show x ∈ Set.Icc 0 (0.574 : ℝ) from ⟨nonnegative, small⟩) nonnegative
  rw [initial] at bound
  have tail : x ^ 7 / 14 ≤ x ^ 5 / 40 := by
    have hx : x ^ 2 ≤ (0.574 : ℝ) ^ 2 := pow_le_pow_left₀ nonnegative small 2
    have lead := mul_le_mul_of_nonneg_right (hx.trans (by norm_num : (0.574 : ℝ) ^ 2 ≤ 14 / 40))
      (pow_nonneg nonnegative 5)
    nlinarith only [lead]
  dsimp only [f] at bound
  nlinarith only [bound, tail]

end Unfoldings
