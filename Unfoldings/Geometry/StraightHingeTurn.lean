module

public import Unfoldings.Geometry.StraightHingeAngle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Sharp total turn across a sequence of creases on a straight projected path. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real Set InnerProductGeometry
open scoped BigOperators

theorem straightHingeAngle_eq_angle (a b c p : ℝ) :
    straightHingeAngle a b c p =
      angle (WithLp.toLp 2 ![a, b, c] : Space) (WithLp.toLp 2 ![1, 0, p] : Space) := by
  rw [straightHingeAngle, straightHingeCos, angle]
  congr 1
  have n1 : ‖(WithLp.toLp 2 ![a, b, c] : Space)‖ = sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rfl
  have n2 : ‖(WithLp.toLp 2 ![1, 0, p] : Space)‖ = sqrt (1 + p ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change sqrt ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + p ^ 2) = _
    norm_num
  rw [n1, n2]
  simp only [PiLp.inner_apply, Fin.sum_univ_three]
  change (a + c * p) / _ = (1 * a + 0 * b + p * c) / _
  ring

private theorem squareSlope_le_of_endpoints
    {a b c p₀ p₁ p B : ℝ} (transverse : b ≠ 0) (hp : p ∈ Ioo p₀ p₁)
    (first : p₀ ^ 2 + straightHingeTransverse a b c p₀ ^ 2 ≤ B)
    (last : p₁ ^ 2 + straightHingeTransverse a b c p₁ ^ 2 ≤ B) :
    p ^ 2 + straightHingeTransverse a b c p ^ 2 ≤ B := by
  let t := (p - p₀) / (p₁ - p₀)
  let q (x : ℝ) := straightHingeTransverse a b c x
  have porder : 0 < p₁ - p₀ := sub_pos.mpr (hp.1.trans hp.2)
  have tpos : 0 ≤ t := div_nonneg (sub_nonneg.mpr hp.1.le) porder.le
  have tsmall : t ≤ 1 := (div_le_one porder).mpr (sub_le_sub_right hp.2.le _)
  have lin : p = (1 - t) * p₀ + t * p₁ := by
    dsimp [t]
    field_simp [porder.ne']
    ring
  have linq : q p = (1 - t) * q p₀ + t * q p₁ := by
    change straightHingeTransverse a b c p = _
    rw [lin]
    dsimp [q, straightHingeTransverse]
    field_simp [transverse]
    ring
  have convex : p ^ 2 + q p ^ 2 ≤
      (1 - t) * (p₀ ^ 2 + q p₀ ^ 2) + t * (p₁ ^ 2 + q p₁ ^ 2) := by
    have nonneg := mul_nonneg (mul_nonneg (sub_nonneg.mpr tsmall) tpos)
      (add_nonneg (sq_nonneg (p₁ - p₀)) (sq_nonneg (q p₁ - q p₀)))
    rw [linq]
    conv_lhs => rw [lin]
    nlinarith only [nonneg]
  exact convex.trans (by
    have h := add_le_add (mul_le_mul_of_nonneg_left first (sub_nonneg.mpr tsmall))
      (mul_le_mul_of_nonneg_left last tpos)
    simpa only [q, sub_mul, sub_add_cancel, one_mul] using h)

private theorem transverse_le_sin_mul_norm {p q phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : p ^ 2 + q ^ 2 ≤ tan phi ^ 2) :
    |q| ≤ sin phi * sqrt (1 + p ^ 2 + q ^ 2) := by
  let B := p ^ 2 + q ^ 2
  have norm_pos : 0 ≤ 1 + B := by dsimp [B]; positivity
  have sn : 0 ≤ sin phi := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos])
  have cn : 0 < cos phi := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], small⟩
  have m := mul_le_mul_of_nonneg_right tilt (sq_nonneg (cos phi))
  have eq : tan phi ^ 2 * cos phi ^ 2 = sin phi ^ 2 := by
    rw [tan_eq_sin_div_cos, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ cn.ne')]
  rw [eq] at m
  apply (sq_le_sq₀ (abs_nonneg q) (mul_nonneg sn (sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, show 1 + p ^ 2 + q ^ 2 = 1 + B by dsimp [B]; ring, sq_sqrt norm_pos]
  calc
    q ^ 2 ≤ B := le_add_of_nonneg_left (sq_nonneg p)
    _ = B * cos phi ^ 2 + B * sin phi ^ 2 := by
      rw [← mul_add, add_comm (cos phi ^ 2), sin_sq_add_cos_sq, mul_one]
    _ ≤ sin phi ^ 2 * (1 + B) := by dsimp [B] at *; nlinarith only [m]

/-- The sharp absolute turn budget at a transverse hinge follows from
the slope bound at its two incident facets. -/
theorem abs_straightHingeAngle_sub_le_sin {a b c p₀ p₁ phi : ℝ} (transverse : b ≠ 0)
    (ordered : p₀ ≤ p₁) (nonnegative : 0 ≤ phi) (small : phi < π / 2)
    (first : p₀ ^ 2 + straightHingeTransverse a b c p₀ ^ 2 ≤ tan phi ^ 2)
    (last : p₁ ^ 2 + straightHingeTransverse a b c p₁ ^ 2 ≤ tan phi ^ 2) :
    |straightHingeAngle a b c p₁ - straightHingeAngle a b c p₀| ≤
      sin phi * (arctan p₁ - arctan p₀) :=
  abs_straightHingeAngle_sub_le transverse ordered fun _ hp =>
    transverse_le_sin_mul_norm nonnegative small
      (squareSlope_le_of_endpoints transverse hp first last)

/-- The local bound is independent of the order of the two facets. -/
theorem abs_straightHingeAngle_sub_le_sin_abs {a b c p₀ p₁ phi : ℝ} (transverse : b ≠ 0)
    (nonnegative : 0 ≤ phi) (small : phi < π / 2)
    (first : p₀ ^ 2 + straightHingeTransverse a b c p₀ ^ 2 ≤ tan phi ^ 2)
    (last : p₁ ^ 2 + straightHingeTransverse a b c p₁ ^ 2 ≤ tan phi ^ 2) :
    |straightHingeAngle a b c p₁ - straightHingeAngle a b c p₀| ≤
      sin phi * |arctan p₁ - arctan p₀| := by
  rcases le_total p₀ p₁ with ordered | ordered
  · rw [abs_of_nonneg (sub_nonneg.mpr (arctan_strictMono.monotone ordered))]
    exact abs_straightHingeAngle_sub_le_sin transverse ordered nonnegative small first last
  · rw [abs_sub_comm (straightHingeAngle a b c p₁), abs_sub_comm (arctan p₁),
      abs_of_nonneg (sub_nonneg.mpr (arctan_strictMono.monotone ordered))]
    exact abs_straightHingeAngle_sub_le_sin transverse ordered nonnegative small last first

/-- Along a straight projected traversal, convexity makes the directional
slopes monotone. The hinge contributions telescope to the sharp total bound
regardless of the number of creases. -/
theorem sum_straightHinge_turn_le {n : ℕ} {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2)
    (p : Fin (n + 1) → ℝ) (a b c : Fin n → ℝ)
    (ordered : ∀ k : Fin n, p k.castSucc ≤ p k.succ)
    (transverse : ∀ k, b k ≠ 0)
    (first : ∀ k, p k.castSucc ^ 2 +
      straightHingeTransverse (a k) (b k) (c k) (p k.castSucc) ^ 2 ≤ tan phi ^ 2)
    (last : ∀ k, p k.succ ^ 2 +
      straightHingeTransverse (a k) (b k) (c k) (p k.succ) ^ 2 ≤ tan phi ^ 2)
    (start : -tan phi ≤ p 0) (finish : p (Fin.last n) ≤ tan phi) :
    (∑ k : Fin n, |straightHingeAngle (a k) (b k) (c k) (p k.succ) -
      straightHingeAngle (a k) (b k) (c k) (p k.castSucc)|) ≤ 2 * phi * sin phi := by
  have bank := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun k _ =>
    abs_straightHingeAngle_sub_le_sin (transverse k) (ordered k) nonnegative small (first k)
      (last k))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at bank
  have remove_first := Fin.sum_univ_succ (fun j => arctan (p j))
  have remove_last := Fin.sum_univ_castSucc (fun j => arctan (p j))
  have difference :
      (∑ k : Fin n, arctan (p k.succ)) - ∑ k : Fin n, arctan (p k.castSucc) =
        arctan (p (Fin.last n)) - arctan (p 0) := by
    linarith only [remove_first, remove_last]
  rw [difference] at bank
  have tanAngle := arctan_tan (by linarith [pi_pos] : -(π / 2) < phi) small
  have lo := arctan_strictMono.monotone start
  have hi := arctan_strictMono.monotone finish
  rw [arctan_neg, tanAngle] at lo
  rw [tanAngle] at hi
  have sine : 0 ≤ sin phi := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos])
  have bound := mul_le_mul_of_nonneg_left
    (show arctan (p (Fin.last n)) - arctan (p 0) ≤ 2 * phi by linarith only [lo, hi]) sine
  exact bank.trans (bound.trans_eq (mul_comm _ _))

end Unfoldings
