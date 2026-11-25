module

public import Unfoldings.FewestNets.LatitudeChordSupport
public import Unfoldings.FewestNets.LatitudeMetricRows

/-! The polar fans also consist of supporting chord triangles of the sampled sphere. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

/-- The pole and its two adjacent ring vertices have this common supporting
normal, only slightly farther from the pole than half the ring radius. -/
theorem latitude_north_polar_secant {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (longitude : ℝ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 0.26 * latitudeRadius a ∧
      let h := π / (latitudeRowSize a 0 : ℝ)
      let n := latitudeSite θ longitude
      let d := cos θ
      inner ℝ n (latitudeSite 0 longitude) = d ∧
      inner ℝ n (latitudeSite (latitudeRadius a / 2) (longitude + h)) = d ∧
      inner ℝ n (latitudeSite (latitudeRadius a / 2) (longitude - h)) = d := by
  let r := latitudeRadius a
  let L := r / 2
  let h := π / (latitudeRowSize a 0 : ℝ)
  have rp : 0 < r := latitudeRadius_pos positive
  have L_pos : 0 < L := by positivity
  have L_small : L < π / 2 := by dsimp only [L, r]; linarith only [latitudeRadius_lt small, pi_gt_three]
  have sine := latitude_sin_half_radius positive small
  change 0.999 * L < sin L at sine
  have sine_pos : 0 < sin L := (mul_pos (by norm_num) L_pos).trans sine
  have h_nonneg : 0 ≤ h := by positivity
  have h_le : h ≤ 0.237 := by
    have spacing := (latitudeLongitudeStep_bounds positive small
      (show 0 ≤ latitudeStripCount a from Nat.zero_le _)).2
    have left : latitudeLongitudeStep a 0 = 2 * h := by
      dsimp only [latitudeLongitudeStep, h]
      ring
    have right : sin (latitudeColatitude a 0) = sin L := by simp [latitudeColatitude, L, r]
    rw [left, right] at spacing
    have actual := (le_div_iff₀ sine_pos).mp spacing
    have upper := latitudeSpacing_lt positive small
    have expected : 0.236 * r ≤ (2 * 0.237) * sin L := by
      dsimp only [L] at sine
      linarith only [sine, rp]
    have bound := le_of_mul_le_mul_right (actual.trans (upper.le.trans expected)) sine_pos
    linarith only [bound]
  have cos_h : 0.97 ≤ cos h := by
    have cap := pow_le_pow_left₀ h_nonneg h_le 2
    linarith only [cap, one_sub_sq_div_two_le_cos (x := h)]
  have cp : 0 < cos h := (by norm_num : (0 : ℝ) < 0.97).trans_le cos_h
  have drop : 0 < 1 - cos L := by
    have h := cos_lt_cos_of_nonneg_of_le_pi (show 0 ≤ (0 : ℝ) by norm_num)
      (show L ≤ π by linarith only [L_small, pi_pos]) L_pos
    rwa [cos_zero, ← sub_pos] at h
  let k := (1 - cos L) / (sin L * cos h)
  have kp : 0 < k := div_pos drop (mul_pos sine_pos cp)
  have k_small : k < 0.26 * r := by
    apply (div_lt_iff₀ (mul_pos sine_pos cp)).mpr
    have lower := mul_le_mul (le_of_lt sine) cos_h (by norm_num : (0 : ℝ) ≤ 0.97)
      (sine_pos.le)
    have m := mul_le_mul_of_nonneg_left lower (by positivity : 0 ≤ 0.26 * r)
    have value : (0.26 * r) * (0.999 * L * 0.97) = (0.26 * 0.999 * 0.97 / 2) * r ^ 2 := by
      dsimp only [L]
      ring
    have square : L ^ 2 / 2 = r ^ 2 / 8 := by dsimp only [L]; ring
    rw [value] at m
    linarith only [one_sub_sq_div_two_le_cos (x := L), square, m, sq_pos_of_pos rp]
  let θ := arctan k
  have θ_pos : 0 < θ := arctan_pos.mpr kp
  have θ_small : θ < 0.26 * r := (arctan_le_self kp.le).trans_lt k_small
  have same : sin θ * (sin L * cos h) = cos θ * (1 - cos L) := by
    have sine_form : sin θ = k * cos θ := by
      dsimp only [θ]
      rw [sin_arctan, cos_arctan, mul_one_div]
    have defining : k * (sin L * cos h) = 1 - cos L :=
      div_mul_cancel₀ _ (mul_pos sine_pos cp).ne'
    rw [sine_form]
    linear_combination cos θ * defining
  refine ⟨θ, θ_pos, θ_small, ?_, ?_, ?_⟩
  · simpa only [add_zero, zero_sub, cos_neg, sin_zero, zero_mul, sub_zero]
      using latitudeSite_inner θ 0 longitude 0
  · rw [latitudeSite_inner, cos_sub]
    change cos L * cos θ + sin L * sin θ - sin L * sin θ * (1 - cos h) = cos θ
    linarith only [same]
  · exact (latitudeSymmetric_support_eq θ L longitude h).trans (by
      rw [latitudeSite_inner, cos_sub]
      linarith only [same])

end Unfoldings.FewestNets
