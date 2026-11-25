module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Exact row spacing and the number of triangles in the parameter latitude strips. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The prescribed meridional length scale. -/
def latitudeRadius (a : ℝ) : ℝ := 4 * √a / 25

/-- The prescribed upper bound on the arclength between successive row vertices. -/
def latitudeSpacing (a : ℝ) : ℝ := 0.45 * a * latitudeRadius a

/-- Integer number of annular strips. -/
def latitudeStripCount (a : ℝ) : ℕ := ⌈(π - latitudeRadius a) / latitudeRadius a⌉₊

/-- Constant gap between adjacent annular rows. -/
def latitudeRowStep (a : ℝ) : ℝ := (π - latitudeRadius a) / latitudeStripCount a

/-- Row colatitude, including the two rows adjacent to the poles. -/
def latitudeColatitude (a : ℝ) (j : ℕ) : ℝ := latitudeRadius a / 2 + j * latitudeRowStep a

/-- Number of equally spaced vertices at one colatitude. -/
def latitudeRowSize (a : ℝ) (j : ℕ) : ℕ :=
  ⌈2 * π * sin (latitudeColatitude a j) / latitudeSpacing a⌉₊

/-- Each triangle in a parameter strip advances exactly one of its two rows. -/
def latitudeTriangleCount (a : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (latitudeStripCount a), (latitudeRowSize a j + latitudeRowSize a (j + 1))

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive in
theorem latitudeRadius_pos : 0 < latitudeRadius a :=
  div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 positive)) (by norm_num)

include small in
theorem latitudeRadius_lt : latitudeRadius a < 0.116 := by
  have sq : (√a) ^ 2 ≤ π / 6 := by
    by_cases ha : 0 ≤ a
    · simpa only [Real.sq_sqrt ha] using small
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha)]
      exact le_of_eq (zero_pow (by norm_num : (2 : ℕ) ≠ 0)) |>.trans (by positivity)
  have root_lt : √a < 0.725 := by
    by_contra! big
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 0.725 by norm_num) big 2
    nlinarith only [sq, this, small, Real.pi_lt_d4]
  unfold latitudeRadius
  linarith only [root_lt]

include positive in
theorem latitudeSpacing_div_radius : latitudeSpacing a / latitudeRadius a = 0.45 * a := by
  unfold latitudeSpacing
  exact mul_div_cancel_right₀ _ (latitudeRadius_pos positive).ne'

include positive small in
theorem latitudeSpacing_lt : latitudeSpacing a < 0.236 * latitudeRadius a := by
  have rate : 0.45 * a < 0.236 := by linarith only [small, Real.pi_lt_d4]
  exact mul_lt_mul_of_pos_right rate (latitudeRadius_pos positive)

include positive in
theorem latitudeSpacing_mul_radius : latitudeSpacing a * latitudeRadius a = 0.01152 * a ^ 2 := by
  unfold latitudeSpacing latitudeRadius
  have square := Real.sq_sqrt positive.le
  calc
    _ = 0.01152 * a * (√a) ^ 2 := by ring
    _ = _ := by rw [square]; ring

include positive small in
theorem latitudeStripCount_pos : 0 < latitudeStripCount a := by
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (by linarith only [latitudeRadius_lt (a := a) small, Real.pi_gt_d2])
    (latitudeRadius_pos positive)

include positive small in
theorem latitudeStripCount_lt : (latitudeStripCount a : ℝ) < π / latitudeRadius a := by
  have nonnegative : 0 ≤ (π - latitudeRadius a) / latitudeRadius a :=
    div_nonneg (by linarith only [latitudeRadius_lt (a := a) small, Real.pi_gt_d2])
      (latitudeRadius_pos positive).le
  apply (Nat.ceil_lt_add_one nonnegative).trans_le
  rw [sub_div, div_self (latitudeRadius_pos positive).ne', sub_add_cancel]

include positive small in
theorem latitudeRowStep_bounds : 0.963 * latitudeRadius a < latitudeRowStep a ∧
    latitudeRowStep a ≤ latitudeRadius a := by
  let r := latitudeRadius a
  let J := latitudeStripCount a
  have r_pos := latitudeRadius_pos positive
  have J_pos : 0 < (J : ℝ) := Nat.cast_pos.mpr (latitudeStripCount_pos positive small)
  have r_small : r < 0.037 * π := by
    linarith only [latitudeRadius_lt (a := a) small, Real.pi_gt_d2]
  have cap := (lt_div_iff₀ r_pos).mp (latitudeStripCount_lt positive small)
  have floor := (div_le_iff₀ r_pos).mp (Nat.le_ceil ((π - r) / r))
  change 0.963 * r < (π - r) / J ∧ (π - r) / J ≤ r
  constructor
  · apply (lt_div_iff₀ J_pos).mpr
    have bound := mul_lt_mul_of_pos_left cap (show (0 : ℝ) < 0.963 by norm_num)
    linarith only [r_small, bound]
  · apply (div_le_iff₀ J_pos).mpr
    change π - r ≤ (J : ℝ) * r at floor
    exact mul_comm (J : ℝ) r ▸ floor

include positive small in
theorem latitudeColatitude_last : latitudeColatitude a (latitudeStripCount a) =
    π - latitudeRadius a / 2 := by
  have J_ne : (latitudeStripCount a : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (latitudeStripCount_pos positive small)).ne'
  unfold latitudeColatitude latitudeRowStep
  field_simp [J_ne]
  ring

include positive small in
theorem latitudeColatitude_bounds {j : ℕ} (row : j ≤ latitudeStripCount a) :
    latitudeRadius a / 2 ≤ latitudeColatitude a j ∧
      latitudeColatitude a j ≤ π - latitudeRadius a / 2 := by
  have step_pos : 0 < latitudeRowStep a :=
    (mul_pos (by norm_num : 0 < (0.963 : ℝ)) (latitudeRadius_pos positive)).trans
      (latitudeRowStep_bounds positive small).1
  have monotone : Monotone (latitudeColatitude a) := by
    intro i j order
    unfold latitudeColatitude
    gcongr
  exact ⟨by simpa [latitudeColatitude] using monotone (Nat.zero_le j),
    (monotone row).trans_eq (latitudeColatitude_last positive small)⟩

/-- A strip's sine trapezoid lies below the cosine drop. -/
private theorem sine_trapezoid_le {u d : ℝ} (pos : 0 < d) (start : 0 ≤ u) (finish : u + d < π) :
    d * (sin u + sin (u + d)) ≤ 2 * (cos u - cos (u + d)) := by
  have dm : d / 2 < π / 2 := by linarith [Real.pi_pos]
  have cp : 0 < cos (d / 2) :=
    cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], dm⟩
  have tangent := Real.le_tan (by linarith only [pos]) dm
  rw [tan_eq_sin_div_cos, le_div_iff₀ cp] at tangent
  have nonnegative : 0 ≤ sin (u + d / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  let m := u + d / 2
  have start_eq : u = m - d / 2 := by unfold m; ring
  have finish_eq : u + d = m + d / 2 := by unfold m; ring
  have sine_add : sin u + sin (u + d) = 2 * sin m * cos (d / 2) := by
    calc
      _ = sin (m - d / 2) + sin (m + d / 2) :=
        congrArg₂ (· + ·) (congrArg sin start_eq) (congrArg sin finish_eq)
      _ = _ := by rw [sin_sub m (d / 2), sin_add m (d / 2)]; ring
  have cosine_sub : cos u - cos (u + d) = 2 * sin m * sin (d / 2) := by
    calc
      _ = cos (m - d / 2) - cos (m + d / 2) :=
        congrArg₂ (· - ·) (congrArg cos start_eq) (congrArg cos finish_eq)
      _ = _ := by rw [cos_sub m (d / 2), cos_add m (d / 2)]; ring
  change 0 ≤ sin m at nonnegative
  rw [sine_add, cosine_sub]
  have scaled := mul_le_mul_of_nonneg_left tangent nonnegative
  nlinarith only [scaled]

private theorem sum_differences (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (f j - f (j + 1)) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- Telescoping the cosine drops bounds the sine sum for any equally spaced rows. -/
theorem latitude_sine_sum_le_of_spacing {d : ℝ} {J : ℕ} (ℓ : ℕ → ℝ)
    (d_pos : 0 < d) (row_succ : ∀ j, ℓ (j + 1) = ℓ j + d)
    (rows : ∀ j ≤ J, ℓ j ∈ Set.Ico 0 π) :
    (∑ j ∈ Finset.range J, (sin (ℓ j) + sin (ℓ (j + 1)))) ≤ 4 / d := by
  have strip (j : ℕ) (member : j ∈ Finset.range J) :
      d * (sin (ℓ j) + sin (ℓ (j + 1))) ≤ 2 * (cos (ℓ j) - cos (ℓ (j + 1))) := by
    have less := Finset.mem_range.mp member
    have ends := (rows (j + 1) (Nat.succ_le_of_lt less)).2
    rw [row_succ j] at ends ⊢
    exact sine_trapezoid_le d_pos (rows j less.le).1 ends
  apply (le_div_iff₀ d_pos).mpr
  rw [mul_comm, Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range J, 2 * (cos (ℓ j) - cos (ℓ (j + 1))) := Finset.sum_le_sum strip
    _ = 2 * (cos (ℓ 0) - cos (ℓ J)) := by
      rw [← Finset.mul_sum]
      exact congrArg (fun x : ℝ => 2 * x) (sum_differences (fun j => cos (ℓ j)) J)
    _ ≤ 4 := by linarith only [cos_le_one (ℓ 0), neg_one_le_cos (ℓ J)]

include positive small in
theorem latitude_sine_sum_le :
    (∑ j ∈ Finset.range (latitudeStripCount a),
      (sin (latitudeColatitude a j) + sin (latitudeColatitude a (j + 1)))) ≤
        4 / latitudeRowStep a := by
  let d := latitudeRowStep a
  let r := latitudeRadius a
  let ℓ := latitudeColatitude a
  have r_pos := latitudeRadius_pos positive
  have d_pos : 0 < d :=
    (mul_pos (by norm_num : 0 < (0.963 : ℝ)) r_pos).trans (latitudeRowStep_bounds positive small).1
  have row_succ (j : ℕ) : ℓ (j + 1) = ℓ j + d := by
    unfold ℓ latitudeColatitude
    push_cast
    ring
  apply latitude_sine_sum_le_of_spacing ℓ d_pos row_succ
  intro j hj
  obtain ⟨low, high⟩ := latitudeColatitude_bounds positive small hj
  exact ⟨by linarith only [low, r_pos], by linarith only [high, r_pos]⟩

/-- Bound the number of sweep triangles using the ceilings on both rows of each strip. -/
theorem latitudeCeilingSum_le {b d : ℝ} {J : ℕ} (ℓ : ℕ → ℝ)
    (b_pos : 0 < b) (d_pos : 0 < d) (row_succ : ∀ j, ℓ (j + 1) = ℓ j + d)
    (rows : ∀ j ≤ J, ℓ j ∈ Set.Ico 0 π) :
    ((∑ j ∈ Finset.range J, (⌈2 * π * sin (ℓ j) / b⌉₊ +
      ⌈2 * π * sin (ℓ (j + 1)) / b⌉₊) : ℕ) : ℝ) ≤ 2 * J + 8 * π / (b * d) := by
  have estimate (j : ℕ) (row : j ≤ J) :
      ((⌈2 * π * sin (ℓ j) / b⌉₊ : ℕ) : ℝ) ≤ 2 * π * sin (ℓ j) / b + 1 := by
    have sine := sin_nonneg_of_nonneg_of_le_pi (rows j row).1 (rows j row).2.le
    exact (Nat.ceil_lt_add_one (div_nonneg
      (mul_nonneg (by positivity : 0 ≤ 2 * π) sine) b_pos.le)).le
  push_cast
  calc
    _ ≤ ∑ j ∈ Finset.range J, (2 + (2 * π / b) * (sin (ℓ j) + sin (ℓ (j + 1)))) := by
      apply Finset.sum_le_sum
      intro j member
      have row := Finset.mem_range.mp member
      convert add_le_add (estimate j row.le) (estimate (j + 1) (Nat.succ_le_of_lt row)) using 1
      ring
    _ = 2 * J + (2 * π / b) *
        (∑ j ∈ Finset.range J, (sin (ℓ j) + sin (ℓ (j + 1)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ 2 * J + (2 * π / b) * (4 / d) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left (latitude_sine_sum_le_of_spacing ℓ d_pos row_succ rows)
        (div_nonneg (by positivity : 0 ≤ 2 * π) b_pos.le)) _
    _ = _ := by field_simp <;> ring

include positive small in
/-- The paper's explicit triangle bound, before straightening the grid on the sphere. -/
theorem latitudeTriangleCount_lt : (latitudeTriangleCount a : ℝ) < 2283 / a ^ 2 := by
  let r := latitudeRadius a
  let b := latitudeSpacing a
  let d := latitudeRowStep a
  let J := latitudeStripCount a
  let ℓ := latitudeColatitude a
  have r_pos : 0 < r := latitudeRadius_pos positive
  have b_pos : 0 < b := mul_pos (mul_pos (by norm_num) positive) r_pos
  have d_lower : 0.963 * r < d := (latitudeRowStep_bounds positive small).1
  have d_pos : 0 < d := (mul_pos (by norm_num : 0 < (0.963 : ℝ)) r_pos).trans d_lower
  have r_small : r < 0.116 := latitudeRadius_lt small
  have b_small : b < 0.236 * r := latitudeSpacing_lt positive small
  have before : (latitudeTriangleCount a : ℝ) ≤ 2 * J + 8 * π / (b * d) := by
    apply latitudeCeilingSum_le ℓ b_pos d_pos
    · intro j
      unfold ℓ latitudeColatitude
      push_cast
      ring
    · intro j hj
      obtain ⟨low, high⟩ := latitudeColatitude_bounds positive small hj
      exact ⟨by linarith only [low, r_pos], by linarith only [high, r_pos]⟩
  have J_bound : (J : ℝ) * r < π :=
    (lt_div_iff₀ r_pos).mp (latitudeStripCount_lt positive small)
  have length : r / d < 1 / 0.963 := by
    apply (div_lt_div_iff₀ d_pos (by norm_num)).mpr
    simpa only [mul_comm, one_mul] using d_lower
  have br_pos := mul_pos b_pos r_pos
  have br : b * r = 0.01152 * a ^ 2 := latitudeSpacing_mul_radius positive
  have first_cost : 2 * (J : ℝ) * (b * r) < 2 * 3.1416 * (0.236 * 0.116) := by
    have J_upper := J_bound.trans Real.pi_lt_d4
    have b_upper : b < 0.236 * 0.116 :=
      b_small.trans (mul_lt_mul_of_pos_left r_small (by norm_num))
    have estimate := mul_lt_mul J_upper b_upper.le b_pos (by norm_num : 0 ≤ (3.1416 : ℝ))
    nlinarith only [estimate]
  have second_cost : (8 * π / (b * d)) * (b * r) < 8 * 3.1416 / 0.963 := by
    calc
      _ = (8 * π) * (r / d) := by field_simp <;> ring
      _ < _ := by
        have estimate := mul_lt_mul Real.pi_lt_d4 length.le (div_pos r_pos d_pos)
          (by norm_num : 0 ≤ (3.1416 : ℝ))
        linarith only [estimate]
  have scaled := mul_le_mul_of_nonneg_right before br_pos.le
  apply (lt_div_iff₀ (pow_pos positive 2)).mpr
  nlinarith only [first_cost, second_cost, scaled,
    congrArg (fun x : ℝ => (latitudeTriangleCount a : ℝ) * x) br]

end Unfoldings.FewestNets
