module

public import Unfoldings.FewestNets.RevisedLatitudeMetricRows
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Sharp tangential bounds for a full sampled base on each row. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real

/-- The unrounded count of samples before any special refinement. -/
def rowSampling (a : ℝ) (j : ℕ) : ℝ := 2 * π * sin (colatitude a j) / spacing a

variable {a : ℝ}

theorem interiorSampling_lb (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (lower : 0 < j) (upper : j < stripCount a) :
    21.79 < rowSampling a j := by
  have base := interior_sine_sharp positive small lower upper
  have rp := radius_pos positive
  have bp := spacing_pos positive
  have weighted := mul_lt_mul_of_pos_left base (mul_pos (by norm_num : (0 : ℝ) < 2) pi_pos)
  change 21.79 < 2 * π * sin (colatitude a j) / spacing a
  apply (lt_div_iff₀ bp).mpr
  have small' := mul_le_mul_of_nonneg_right small rp.le
  have allowance : 21.79 * spacing a ≤ (2 / 1.0795) * (π * radius a) := by
    unfold spacing
    linarith only [small', mul_pos pi_pos rp]
  exact allowance.trans_lt (by linarith only [weighted])

theorem interiorSize_lb (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (lower : 0 < j) (upper : j < stripCount a) : 22 ≤ rowSize a j := by
  have p : ¬ (j = 0 ∨ j = stripCount a) := not_or.mpr ⟨lower.ne', upper.ne⟩
  rw [rowSize, ite_eq_right p]
  have bound := (interiorSampling_lb positive small lower upper).trans_le
    (Nat.le_ceil (rowSampling a j))
  change (21.79 : ℝ) < (⌈rowSampling a j⌉₊ : ℝ) at bound
  have cast : (21 : ℝ) < (⌈rowSampling a j⌉₊ : ℝ) := (by norm_num : (21 : ℝ) < 21.79).trans bound
  exact Nat.succ_le_of_lt (Nat.cast_lt.mp cast)

theorem polarSize_lt_refinedSampling (positive : 0 < a) (small : a ≤ π / 6) :
    (polarSize a : ℝ) < 2.206 * polarSampling a := by
  have q := (polarSampling_bounds positive small).1
  unfold polarSize
  rw [Nat.cast_max, Nat.cast_ofNat]
  apply max_lt
  · linarith only [q]
  · have same : 2 * π * sin (AcuteLatitudeGrid.polarRadius a) / (0.6 * spacing a) =
      (5 / 3 : ℝ) * polarSampling a := by unfold polarSampling; ring
    rw [same]
    have nonnegative : 0 ≤ (5 / 3 : ℝ) * polarSampling a := by linarith only [q]
    linarith only [Nat.ceil_lt_add_one nonnegative, q]

/-- At least the stated multiple of the target spacing is retained by a
spherical latitude base before division by the chart denominator. -/
theorem rawBaseWidth_bounds (positive : 0 < a) (small : a ≤ π / 6)
    {j : ℕ} (valid : j ≤ stripCount a) :
    let θ := π / (rowSize a j : ℝ)
    let raw := 2 * sin (colatitude a j) * sin θ
    (if j = 0 ∨ j = stripCount a then 0.432 else 0.952) * spacing a < raw ∧
      raw ≤ localSpacing a j := by
  let k := rowSize a j
  let θ := π / (k : ℝ)
  let q := rowSampling a j
  let s := sin (colatitude a j)
  let b := spacing a
  have kp : 0 < (k : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small valid)
  have sp : 0 < s := sin_pos_of_mem_Ioo (colatitude_mem positive small valid)
  have bp : 0 < b := spacing_pos positive
  have tp : 0 < θ := div_pos pi_pos kp
  have upper : 2 * s * sin θ ≤ localSpacing a j := by
    have h := (div_le_iff₀ (localSpacing_pos positive j)).mp (sampling_le_rowSize positive small j)
    refine (mul_le_mul_of_nonneg_left (sin_le tp.le) (by positivity)).trans ?_
    dsimp only [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ kp).mpr
    linarith only [h]
  have normalize : (q / (k : ℝ)) * b = 2 * s * θ := by
    have multiply : q * b = 2 * π * s := div_mul_cancel₀ _ bp.ne'
    calc
      _ = (q * b) / (k : ℝ) := by ring
      _ = _ := by rw [multiply]; dsimp only [θ]; ring
  refine ⟨?_, upper⟩
  by_cases polar : j = 0 ∨ j = stripCount a
  · have same : q = polarSampling a := by
      have sine : s = sin (AcuteLatitudeGrid.polarRadius a) := by
        rcases polar with rfl | rfl
        · simp [s, colatitude]
        · dsimp only [s]
          rw [colatitude_last positive small, sin_pi_sub]
      unfold q rowSampling polarSampling
      rw [show sin (colatitude a j) = _ from sine]
    have six : 6 ≤ k := by
      dsimp only [k, rowSize]
      rw [ite_eq_left polar]
      exact (polarSize_bounds positive small).1
    have cap : (k : ℝ) < 2.206 * q := by
      dsimp only [k, rowSize]
      rw [ite_eq_left polar, same]
      exact polarSize_lt_refinedSampling positive small
    have θupper : θ ≤ π / 6 := div_le_div_of_nonneg_left pi_pos.le (by norm_num)
      (by exact_mod_cast six)
    have sn : (3 / π) * θ ≤ sin θ := by
      let u := 6 * θ / π
      have up : 0 ≤ u := by dsimp [u]; positivity
      have ule : u ≤ 1 := by
        apply (div_le_one pi_pos).mpr
        change 6 * θ ≤ π
        linarith only [θupper]
      have c := strictConcaveOn_sin_Icc.concaveOn.2
        (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
        (show π / 6 ∈ Set.Icc 0 π from ⟨by positivity, by linarith only [pi_pos]⟩)
        (sub_nonneg.mpr ule) up (sub_add_cancel 1 u)
      simp only [smul_eq_mul, mul_zero, zero_add, sin_zero, sin_pi_div_six] at c
      have inner : u * (π / 6) = θ := by dsimp [u]; field_simp [pi_ne_zero]
      have outer : u * (1 / 2) = (3 / π) * θ := by dsimp [u]; ring
      rwa [inner, outer] at c
    have relative : 1 / (2.206 : ℝ) < q / (k : ℝ) := by
      apply (lt_div_iff₀ kp).mpr
      linarith only [cap]
    rw [ite_eq_left polar]
    calc
      _ < ((3 / π) * (1 / 2.206)) * b := by
        apply mul_lt_mul_of_pos_right _ bp
        rw [show (3 / π) * (1 / 2.206) = 3 / (π * 2.206) by ring]
        apply (lt_div_iff₀ (by positivity)).mpr
        linarith only [pi_lt_d6]
      _ ≤ (3 / π) * (q / (k : ℝ) * b) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right relative.le bp.le) (by positivity)
      _ ≤ _ := by
        rw [normalize]
        simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left sn
          (show 0 ≤ 2 * s by positivity)
  · obtain ⟨low_ne, up_ne⟩ := not_or.mp polar
    have low : 0 < j := Nat.pos_of_ne_zero low_ne
    have hi : j < stripCount a := lt_of_le_of_ne valid up_ne
    have qmin : 21.79 < q := interiorSampling_lb positive small low hi
    have twenty_two : 22 ≤ k := interiorSize_lb positive small low hi
    have cap : (k : ℝ) < q + 1 := by
      dsimp only [k, rowSize]
      rw [ite_eq_right polar]
      exact Nat.ceil_lt_add_one ((by norm_num : (0 : ℝ) < 21.79).trans qmin).le
    have θsmall : θ ≤ 0.143 := by
      have h : (22 : ℝ) ≤ k := by exact_mod_cast twenty_two
      apply (div_le_iff₀ kp).mpr
      have pi_upper : π < 3.141593 := pi_lt_d6
      linarith only [h, pi_upper]
    have sine : 0.9965 * θ < sin θ := by
      have sq := pow_le_pow_left₀ tp.le θsmall 2
      have cube : θ ^ 3 / 6 ≤ 0.0035 * θ := by
        rw [show θ ^ 3 / 6 = (θ ^ 2 / 6) * θ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith only [sq]) tp.le
      linarith only [sin_gt_sub_cube tp, cube]
    have relative : (21.79 / 22.79 : ℝ) ≤ q / (k : ℝ) := by
      apply (le_div_iff₀ kp).mpr
      have h := mul_le_mul_of_nonneg_left cap.le (show 0 ≤ (21.79 / 22.79 : ℝ) by norm_num)
      norm_num at h ⊢
      linarith only [h, qmin]
    rw [ite_eq_right polar]
    calc
      _ < (0.9965 * (21.79 / 22.79)) * b := mul_lt_mul_of_pos_right (by norm_num) bp
      _ ≤ 0.9965 * (q / (k : ℝ) * b) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right relative bp.le) (by norm_num)
      _ ≤ _ := by
        rw [normalize]
        simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left sine.le
          (show 0 ≤ 2 * s by positivity)

end Unfoldings.FewestNets.RevisedLatitudeGrid
