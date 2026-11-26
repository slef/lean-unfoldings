module

public import Unfoldings.FewestNets.AcuteLatitudeChartAngles
public import Unfoldings.FewestNets.RevisedLatitudeAnnularSides

/-! Exact sine and base angle formulas in the horizontal-base chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real InnerProductGeometry

variable {a : ℝ} {positive : 0 < a} {small : a ≤ π / 6} {i : AnnularTriangle a}
  (D : AnnularChartData positive small i)

/-- The planar apex sine retains the full base width over height. -/
theorem planar_apex_sine {x y b H : ℝ} (xp : 0 < x) (hp : 0 < H) :
    let L : ℂ := ⟨-x, b⟩
    let R : ℂ := ⟨x, b⟩
    let A : ℂ := ⟨y, b - H⟩
    let e := (y - x) / H
    let w := (y + x) / H
    sin (angle (L - A) (R - A)) =
      (2 * x / H) / (√(1 + e ^ 2) * √(1 + w ^ 2)) := by
  let L : ℂ := ⟨-x, b⟩
  let R : ℂ := ⟨x, b⟩
  let A : ℂ := ⟨y, b - H⟩
  let e := (y - x) / H
  let w := (y + x) / H
  change sin (angle (L - A) (R - A)) = _
  rw [angle_comm, AcuteLatitudeGrid.latitude_apex_angle (neg_lt_self xp) hp, sin_sub,
    sin_arctan, sin_arctan, cos_arctan, cos_arctan]
  simp only [latitudeEastRatio, latitudeWestRatio, sub_neg_eq_add]
  change (w / √(1 + w ^ 2)) * (1 / √(1 + e ^ 2)) -
    (1 / √(1 + w ^ 2)) * (e / √(1 + e ^ 2)) = (2 * x / H) / (√(1 + e ^ 2) * √(1 + w ^ 2))
  dsimp only [w, e]
  field_simp [hp.ne', show √(1 + ((y - x) / H) ^ 2) ≠ 0 by positivity,
    show √(1 + ((y + x) / H) ^ 2) ≠ 0 by positivity]
  ring

private theorem planar_angle_from_horizontal {z : ℂ} {H : ℝ} (Hp : 0 < H)
    (im : |z.im| = H) :
    angle (1 : ℂ) z = π / 2 - arctan (z.re / H) := by
  have zn : z ≠ 0 := by
    intro eq
    rw [eq, Complex.zero_im, abs_zero] at im
    exact Hp.ne' im.symm
  let q := z.re / H
  have Hsq : z.im ^ 2 = H ^ 2 := by
    rw [← im, sq_abs]
  have norm_z : ‖z‖ = H * √(1 + q ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two z.re, ← pow_two z.im, mul_pow, sq_sqrt (by positivity), Hsq]
    dsimp only [q]
    field_simp [Hp.ne']
    ring
  have c : cos (angle (1 : ℂ) z) = cos (π / 2 - arctan q) := by
    rw [Complex.angle_one_left zn, cos_abs, Complex.cos_arg zn, cos_pi_div_two_sub,
      sin_arctan, norm_z]
    dsimp only [q]
    ring
  exact strictAntiOn_cos.injOn ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    ⟨by linarith only [arctan_lt_pi_div_two q], by linarith only [neg_pi_div_two_lt_arctan q]⟩ c

private theorem abs_arctan_le_of_abs_le {t x : ℝ} (h : |t| ≤ x) : |arctan t| ≤ arctan x := by
  obtain ⟨l, u⟩ := abs_le.mp h
  have low := arctan_mono l
  rw [arctan_neg] at low
  exact abs_le.mpr ⟨low, arctan_mono u⟩

/-- Each planar base angle is within arctan of the long-side ratio of a right angle. -/
theorem planar_base_angles :
    let L : ℂ := ⟨-D.halfBase, D.base⟩
    let R : ℂ := ⟨D.halfBase, D.base⟩
    let A : ℂ := ⟨D.apex, D.base - D.height⟩
    |angle (R - L) (A - L) - π / 2| ≤ arctan 0.335 ∧
      |angle (L - R) (A - R) - π / 2| ≤ arctan 0.335 := by
  let L : ℂ := ⟨-D.halfBase, D.base⟩
  let R : ℂ := ⟨D.halfBase, D.base⟩
  let A : ℂ := ⟨D.apex, D.base - D.height⟩
  let H := D.height
  have width : R - L = (2 * D.halfBase) • (1 : ℂ) := by
    apply Complex.ext <;> simp [R, L, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring
  have rev : L - R = (2 * D.halfBase) • (-1 : ℂ) := by
    apply Complex.ext <;> simp [L, R] <;> ring
  have re_left : |(A - L).re| ≤ 0.335 * H := by
    change |D.apex - (-D.halfBase)| ≤ _
    rw [sub_neg_eq_add]
    exact (abs_add_le _ _).trans D.displacement_small.le
  have re_right : |(A - R).re| ≤ 0.335 * H :=
    (abs_sub _ _).trans D.displacement_small.le
  have im (z : ℂ) (h : z.im = D.base) : |(A - z).im| = H := by
    rw [Complex.sub_im, h]
    change |D.base - H - D.base| = H
    rw [show D.base - H - D.base = -H by ring, abs_neg, abs_of_pos D.height_pos]
  have err {z : ℂ} (re : |z.re| ≤ 0.335 * H) (vertical : |z.im| = H) :
      |angle (1 : ℂ) z - π / 2| ≤ arctan 0.335 := by
    rw [planar_angle_from_horizontal D.height_pos vertical]
    rw [show π / 2 - arctan (z.re / H) - π / 2 = -arctan (z.re / H) by ring, abs_neg]
    apply abs_arctan_le_of_abs_le
    rw [abs_div, abs_of_pos D.height_pos]
    exact (div_le_iff₀ D.height_pos).mpr re
  change |angle (R - L) (A - L) - π / 2| ≤ arctan 0.335 ∧
    |angle (L - R) (A - R) - π / 2| ≤ arctan 0.335
  have hp := mul_pos (by norm_num : (0 : ℝ) < 2) D.base_pos
  rw [width, rev, angle_smul_left_of_pos _ _ hp, angle_smul_left_of_pos _ _ hp]
  refine ⟨err re_left (im L rfl), ?_⟩
  have h : angle (-1 : ℂ) (A - R) = angle (1 : ℂ) (-(A - R)) := by
    simpa only [neg_neg] using angle_neg_neg (1 : ℂ) (-(A - R))
  rw [h]
  apply err
  · rwa [Complex.neg_re, abs_neg]
  · rw [Complex.neg_im, abs_neg]
    exact im R rfl


/-- The product of the two normalized long-side lengths. -/
def AnnularChartData.apexLengthFactor : ℝ :=
  √(1 + ((D.apex - D.halfBase) / D.height) ^ 2) *
    √(1 + ((D.apex + D.halfBase) / D.height) ^ 2)

theorem AnnularChartData.apexLengthFactor_pos : 0 < D.apexLengthFactor := by
  unfold AnnularChartData.apexLengthFactor
  positivity

theorem AnnularChartData.apexLengthFactor_le_mean :
    D.apexLengthFactor ≤ 1 + (D.apex ^ 2 + D.halfBase ^ 2) / D.height ^ 2 := by
  let t := (D.apex - D.halfBase) / D.height
  let u := (D.apex + D.halfBase) / D.height
  let s := √(1 + t ^ 2)
  let q := √(1 + u ^ 2)
  have s2 : s ^ 2 = 1 + t ^ 2 := sq_sqrt (by positivity)
  have q2 : q ^ 2 = 1 + u ^ 2 := sq_sqrt (by positivity)
  have algebra : (t ^ 2 + u ^ 2) / 2 =
      (D.apex ^ 2 + D.halfBase ^ 2) / D.height ^ 2 := by
    unfold t u
    ring
  change s * q ≤ _
  rw [← algebra]
  nlinarith only [sq_nonneg (s - q), s2, q2]

theorem AnnularChartData.apexLengthFactor_le :
    D.apexLengthFactor ≤ if isPolarStrip a i.1.val then 1.059 else 1.0562 := by
  apply D.apexLengthFactor_le_mean.trans
  have rp := radius_pos positive
  have bh : spacing a / (2 * 0.9612) ≤ 0.1395 * radius a := by
    apply (div_le_iff₀ (by norm_num)).mpr
    linarith only [spacing_lt positive small, rp]
  have hx : |D.halfBase| ≤ spacing a / (2 * 0.9612) := by
    apply D.halfBase_bound.le.trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    cases pol : isPolarRow a (baseRow i) <;> simp [pol, widthFactor] <;>
      linarith only [spacing_pos positive]
  have sqx := pow_le_pow_left₀ (abs_nonneg _) (hx.trans bh) 2
  have sqy := pow_le_pow_left₀ (abs_nonneg _) (D.apex_bound.le.trans bh) 2
  rw [sq_abs] at sqx sqy
  have upper := D.height_coarse_lower
  cases pol : isPolarStrip a i.1.val <;> simp only [pol, Bool.false_eq_true, ite_true, ite_false] at upper ⊢
  · have h := pow_le_pow_left₀ (show 0 ≤ 0.834 * radius a from by positivity) upper.le 2
    have scale := (div_le_iff₀ (pow_pos D.height_pos 2)).mpr
      (show D.apex ^ 2 + D.halfBase ^ 2 ≤ 0.0562 * D.height ^ 2 from by
        ring_nf at h sqx sqy ⊢
        nlinarith only [h, sqx, sqy, sq_nonneg (radius a)])
    linarith only [scale]
  · have h := pow_le_pow_left₀ (show 0 ≤ 0.815 * radius a from by positivity) upper.le 2
    have scale := (div_le_iff₀ (pow_pos D.height_pos 2)).mpr
      (show D.apex ^ 2 + D.halfBase ^ 2 ≤ 0.059 * D.height ^ 2 from by
        ring_nf at h sqx sqy ⊢
        nlinarith only [h, sqx, sqy, sq_nonneg (radius a)])
    linarith only [scale]

end Unfoldings.FewestNets.RevisedLatitudeGrid
