module

public import Unfoldings.FewestNets.LatitudeRows

/-! Row scales and the exact midpoint-sweep triangle count for the acute latitude grid. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real

/-- The meridional length prescribed away from the poles. -/
def radius (a : ℝ) : ℝ := 0.322 * √a

/-- The target upper bound on the arclength of a row interval. -/
def spacing (a : ℝ) : ℝ := 0.56 * a * radius a

/-- Colatitude of the first row. -/
def polarRadius (a : ℝ) : ℝ := √a / 12

/-- The number of annular strips between the two polar cells. -/
def stripCount (a : ℝ) : ℕ := ⌈(π - 2 * polarRadius a) / radius a⌉₊

/-- The meridional separation of consecutive rows. -/
def rowStep (a : ℝ) : ℝ := (π - 2 * polarRadius a) / stripCount a

/-- Colatitude of row `j` for `0 ≤ j ≤ stripCount a`. -/
def colatitude (a : ℝ) (j : ℕ) : ℝ := polarRadius a + j * rowStep a

/-- Number of sample sites on one row. -/
def rowSize (a : ℝ) (j : ℕ) : ℕ := ⌈2 * π * sin (colatitude a j) / spacing a⌉₊

/-- Each midpoint advance contributes one annular triangle. -/
def triangleCount (a : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (stripCount a), (rowSize a j + rowSize a (j + 1))

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive in
theorem polarRadius_pos : 0 < polarRadius a := by
  unfold polarRadius
  positivity

include positive in
theorem radius_pos : 0 < radius a := by
  unfold radius
  positivity

include positive in
theorem spacing_pos : 0 < spacing a := by
  unfold spacing
  exact mul_pos (mul_pos (by norm_num) positive) (radius_pos positive)

theorem radius_eq_polarRadius : radius a = 3.864 * polarRadius a := by
  unfold radius polarRadius
  ring

include small in
theorem radius_lt : radius a < 0.234 := by
  have first := latitudeRadius_lt (a := a) small
  unfold latitudeRadius at first
  unfold radius
  linarith only [first]

include small in
theorem polarRadius_lt : polarRadius a < 0.061 := by
  have first := radius_lt (a := a) small
  rw [radius_eq_polarRadius] at first
  linarith only [first]

include positive small in
theorem spacing_lt : spacing a < 0.294 * radius a := by
  apply mul_lt_mul_of_pos_right _ (radius_pos positive)
  linarith only [small, pi_lt_d4]

include positive in
theorem spacing_mul_radius : spacing a * radius a = 0.05806304 * a ^ 2 := by
  unfold spacing radius
  calc
    _ = 0.05806304 * a * (√a) ^ 2 := by ring
    _ = _ := by rw [sq_sqrt positive.le]; ring

include small in
private theorem meridian_pos : 0 < π - 2 * polarRadius a := by
  linarith only [polarRadius_lt small, pi_gt_d2]

include positive small in
theorem stripCount_pos : 0 < stripCount a :=
  Nat.one_le_ceil_iff.mpr (div_pos (meridian_pos small) (radius_pos positive))

include positive small in
theorem stripCount_mul_radius_lt :
    (stripCount a : ℝ) * radius a < π - 2 * polarRadius a + radius a := by
  have rp := radius_pos positive
  have h := Nat.ceil_lt_add_one (div_nonneg (meridian_pos small).le rp.le)
  change (stripCount a : ℝ) < _ at h
  calc
    _ < ((π - 2 * polarRadius a) / radius a + 1) * radius a :=
      mul_lt_mul_of_pos_right h rp
    _ = _ := by field_simp [rp.ne']

include positive small in
theorem rowStep_bounds : 0.928 * radius a < rowStep a ∧ rowStep a ≤ radius a := by
  have J_pos : 0 < (stripCount a : ℝ) := Nat.cast_pos.mpr (stripCount_pos positive small)
  have floor := (div_le_iff₀ (radius_pos positive)).mp
    (Nat.le_ceil ((π - 2 * polarRadius a) / radius a))
  have ceiling := stripCount_mul_radius_lt positive small
  have margin : 0.928 * radius a < 0.072 * (π - 2 * polarRadius a) := by
    linarith only [radius_lt small, polarRadius_lt small, pi_gt_d2]
  unfold rowStep
  constructor
  · apply (lt_div_iff₀ J_pos).mpr
    nlinarith only [ceiling, margin]
  · apply (div_le_iff₀ J_pos).mpr
    change π - 2 * polarRadius a ≤ radius a * (stripCount a : ℝ)
    rw [mul_comm (radius a)]
    exact floor

include positive small in
theorem rowStep_pos : 0 < rowStep a :=
  (mul_pos (by norm_num : 0 < (0.928 : ℝ)) (radius_pos positive)).trans
    (rowStep_bounds positive small).1

theorem colatitude_succ (j : ℕ) : colatitude a (j + 1) = colatitude a j + rowStep a := by
  unfold colatitude
  push_cast
  ring

include positive small in
theorem colatitude_last : colatitude a (stripCount a) = π - polarRadius a := by
  have J_ne : (stripCount a : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (stripCount_pos positive small)).ne'
  unfold colatitude rowStep
  field_simp [J_ne]
  ring

include positive small in
theorem colatitude_strictMono : StrictMono (colatitude a) := by
  intro i j order
  unfold colatitude
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr order) (rowStep_pos positive small)) _

include positive small in
theorem colatitude_bounds {j : ℕ} (row : j ≤ stripCount a) :
    colatitude a j ∈ Set.Icc (polarRadius a) (π - polarRadius a) := by
  have increasing := (colatitude_strictMono positive small).monotone
  exact ⟨by simpa [colatitude] using increasing (Nat.zero_le j),
    (increasing row).trans_eq (colatitude_last positive small)⟩

include positive small in
theorem colatitude_mem {j : ℕ} (row : j ≤ stripCount a) :
    colatitude a j ∈ Set.Ioo 0 π := by
  obtain ⟨low, high⟩ := colatitude_bounds positive small row
  exact ⟨(polarRadius_pos positive).trans_le low,
    high.trans_lt (by linarith only [polarRadius_pos positive])⟩

include positive small in
theorem rowSize_pos {j : ℕ} (row : j ≤ stripCount a) : 0 < rowSize a j := by
  have sine := sin_pos_of_mem_Ioo (colatitude_mem positive small row)
  exact Nat.one_le_ceil_iff.mpr
    (div_pos (mul_pos (by positivity) sine) (spacing_pos positive))

include positive small in
/-- The exact midpoint sweep contributes fewer than `476/a²` annular triangles. -/
theorem triangleCount_lt : (triangleCount a : ℝ) < 476 / a ^ 2 := by
  let r := radius a
  let b := spacing a
  let d := rowStep a
  let J := stripCount a
  have rp : 0 < r := radius_pos positive
  have bp : 0 < b := spacing_pos positive
  have dp : 0 < d := rowStep_pos positive small
  have raw : (triangleCount a : ℝ) ≤ 2 * J + 8 * π / (b * d) := by
    apply latitudeCeilingSum_le (colatitude a) bp dp colatitude_succ
    intro j hj
    obtain ⟨low, high⟩ := colatitude_mem positive small hj
    exact ⟨low.le, high⟩
  have width : b < (0.294 : ℝ) * 0.234 :=
    (spacing_lt positive small).trans (mul_lt_mul_of_pos_left (radius_lt small) (by norm_num))
  have rows : (J : ℝ) * r < 3.1416 + 0.234 := by
    change (stripCount a : ℝ) * radius a < _
    linarith only [stripCount_mul_radius_lt positive small, radius_lt small,
      polarRadius_pos positive, pi_lt_d4]
  have ratio : r / d < 1 / 0.928 := by
    apply (div_lt_div_iff₀ dp (by norm_num)).mpr
    simpa only [mul_comm, one_mul] using (rowStep_bounds positive small).1
  have first : 2 * (J : ℝ) * (b * r) < 2 * (3.1416 + 0.234) * (0.294 * 0.234) := by
    have h := mul_lt_mul rows width.le bp (by norm_num : (0 : ℝ) ≤ 3.1416 + 0.234)
    nlinarith only [h]
  have second : (8 * π / (b * d)) * (b * r) < 8 * 3.1416 / 0.928 := by
    calc
      _ = (8 * π) * (r / d) := by field_simp <;> ring
      _ < _ := by
        have h := mul_lt_mul pi_lt_d4 ratio.le (div_pos rp dp)
          (by norm_num : 0 ≤ (3.1416 : ℝ))
        linarith only [h]
  have scaled := mul_le_mul_of_nonneg_right raw (mul_pos bp rp).le
  have br : b * r = 0.05806304 * a ^ 2 := spacing_mul_radius positive
  apply (lt_div_iff₀ (pow_pos positive 2)).mpr
  nlinarith only [first, second, scaled,
    congrArg (fun x : ℝ => (triangleCount a : ℝ) * x) br]

end Unfoldings.FewestNets.AcuteLatitudeGrid
