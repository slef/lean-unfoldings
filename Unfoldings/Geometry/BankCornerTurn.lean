module

public import Unfoldings.Geometry.RadialRightCorner

/-! Exact real turns and the two occupied apertures at a radial bank bend. -/

@[expose] public section

namespace Unfoldings

/-- Forward turning between incident edges, measured in the common radial frame. -/
noncomputable def radialBankTurn (radial incoming outgoing : ℂ) : ℝ :=
  (outgoing / radial).arg - (incoming / radial).arg

/-- Strict radial progress keeps the signed turn in the principal argument interval. -/
theorem radialBankTurn_bounds (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    -Real.pi < radialBankTurn radial incoming outgoing ∧
      radialBankTurn radial incoming outgoing < Real.pi := by
  have i := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos first)))
  have o := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos last)))
  dsimp only [radialBankTurn]
  constructor <;> linarith [i.1, i.2, o.1, o.2]

/-- The real turn is the principal argument of the outgoing-to-incoming edge ratio. -/
theorem radialBankTurn_eq_arg (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    radialBankTurn radial incoming outgoing = (outgoing / incoming).arg := by
  have i := complex_div_re_pos_of_inner_pos first
  have o := complex_div_re_pos_of_inner_pos last
  have nonzero (z : ℂ) (h : 0 < z.re) : z ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at h
    exact lt_irrefl _ h
  have rne : radial ≠ 0 := by
    intro h
    rw [h, div_zero, Complex.zero_re] at i
    exact lt_irrefl _ i
  have ratio : (outgoing / radial) / (incoming / radial) = outgoing / incoming := by
    exact div_div_div_cancel_right₀ rne _ _
  have angle := Complex.arg_div_coe_angle (nonzero _ o) (nonzero _ i)
  rw [ratio, ← Real.Angle.coe_sub] at angle
  have bounds := radialBankTurn_bounds radial incoming outgoing first last
  have left := Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨Complex.neg_pi_lt_arg (outgoing / incoming), Complex.arg_le_pi _⟩
  have right := Real.Angle.toReal_coe_eq_self_iff.mpr ⟨bounds.1, bounds.2.le⟩
  exact right.symm.trans ((congrArg Real.Angle.toReal angle).symm.trans left)

/-- The occupied left aperture is pi minus the original forward turn. -/
theorem radialLeftCornerWidth_eq_pi_sub_turn (radial incoming outgoing : ℂ) :
    radialLeftCornerWidth radial incoming outgoing =
      Real.pi - radialBankTurn radial incoming outgoing := by
  unfold radialLeftCornerWidth radialBankTurn
  ring

/-- The occupied right aperture is pi plus the original forward turn. -/
theorem radialRightCornerWidth_eq_pi_add_turn (radial incoming outgoing : ℂ) :
    radialRightCornerWidth radial incoming outgoing =
      Real.pi + radialBankTurn radial incoming outgoing := by
  have sum := radialCornerWidths_add radial incoming outgoing
  rw [radialLeftCornerWidth_eq_pi_sub_turn] at sum
  linarith

/-- Rotating the outgoing and incoming edges by different prescribed lifts changes the
real turn by their difference, provided the resulting lift stays in the principal interval. -/
theorem radialBankTurn_rotation (radial radial' incoming outgoing : ℂ) (a b : ℝ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing)
    (first' : 0 < inner ℝ radial' (polarRay a * incoming))
    (last' : 0 < inner ℝ radial' (polarRay b * outgoing))
    (bounds : -Real.pi < radialBankTurn radial incoming outgoing + (b - a) ∧
      radialBankTurn radial incoming outgoing + (b - a) ≤ Real.pi) :
    radialBankTurn radial' (polarRay a * incoming) (polarRay b * outgoing) =
      radialBankTurn radial incoming outgoing + (b - a) := by
  have ine : incoming ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at first
    exact lt_irrefl _ first
  have one : outgoing ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at last
    exact lt_irrefl _ last
  have ratio : (polarRay b * outgoing) / (polarRay a * incoming) =
      polarRay (b - a) * (outgoing / incoming) := by
    rw [← polarRay_div]
    ring
  rw [radialBankTurn_eq_arg radial' _ _ first' last', ratio]
  have modulo := Complex.arg_mul_coe_angle (polarRay_ne_zero (b - a)) (div_ne_zero one ine)
  have polar : ((polarRay (b - a)).arg : Real.Angle) = (b - a : ℝ) := by
    change (Complex.arg (↑((b - a : ℝ) : Real.Angle).toCircle) : Real.Angle) = _
    exact Real.Angle.arg_toCircle _
  rw [polar, ← radialBankTurn_eq_arg radial _ _ first last, ← Real.Angle.coe_add,
    add_comm] at modulo
  have principal := Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨Complex.neg_pi_lt_arg (polarRay (b - a) * (outgoing / incoming)), Complex.arg_le_pi _⟩
  exact principal.symm.trans ((congrArg Real.Angle.toReal modulo).trans
    (Real.Angle.toReal_coe_eq_self_iff.mpr bounds))

private theorem polarRay_add_full_turn (θ : ℝ) : polarRay (θ + 2 * Real.pi) = polarRay θ := by
  apply Complex.ext
  · simp only [polarRay_re, Real.cos_add_two_pi]
  · simp only [polarRay_im, Real.sin_add_two_pi]

/-- Radial progress throughout the scaled opening rules out passing either end
of the principal argument interval. Thus the final real turn needs no branch assumption. -/
theorem radialBankTurn_rotation_of_intermediate_radial
    (radial radial' incoming outgoing : ℂ) (a b : ℝ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing)
    (first' : 0 < inner ℝ radial' (polarRay a * incoming))
    (last' : 0 < inner ℝ radial' (polarRay b * outgoing))
    (intermediate : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℂ,
      0 < inner ℝ r (polarRay (u * a) * incoming) ∧
        0 < inner ℝ r (polarRay (u * b) * outgoing)) :
    radialBankTurn radial' (polarRay a * incoming) (polarRay b * outgoing) =
      radialBankTurn radial incoming outgoing + (b - a) := by
  let θ := radialBankTurn radial incoming outgoing
  have original := radialBankTurn_bounds radial incoming outgoing first last
  change -Real.pi < θ ∧ θ < Real.pi at original
  have no_half_turn (u : ℝ) (time : u ∈ Set.Icc (0 : ℝ) 1)
      (target : θ + u * (b - a) = Real.pi ∨ θ + u * (b - a) = -Real.pi) : False := by
    obtain ⟨r, hi, ho⟩ := intermediate u time
    rcases target with pos | neg
    · have half : θ + (u * b - u * a) = Real.pi := by linarith
      have bounds : -Real.pi < θ + (u * b - u * a) ∧ θ + (u * b - u * a) ≤ Real.pi := by
        rw [half]
        exact ⟨by linarith [Real.pi_pos], le_rfl⟩
      have turn := radialBankTurn_rotation radial r incoming outgoing (u * a) (u * b)
        first last hi ho bounds
      have smaller := (radialBankTurn_bounds r _ _ hi ho).2
      exact (lt_irrefl _) ((turn.trans half) ▸ smaller)
    · have lifted : 0 < inner ℝ r (polarRay (u * b + 2 * Real.pi) * outgoing) := by
        rw [polarRay_add_full_turn]
        exact ho
      have half : θ + (u * b + 2 * Real.pi - u * a) = Real.pi := by linarith
      have bounds : -Real.pi < θ + (u * b + 2 * Real.pi - u * a) ∧
          θ + (u * b + 2 * Real.pi - u * a) ≤ Real.pi := by
        rw [half]
        exact ⟨by linarith [Real.pi_pos], le_rfl⟩
      have turn := radialBankTurn_rotation radial r incoming outgoing (u * a)
        (u * b + 2 * Real.pi) first last hi lifted bounds
      have smaller := (radialBankTurn_bounds r _ _ hi lifted).2
      exact (lt_irrefl _) ((turn.trans half) ▸ smaller)
  apply radialBankTurn_rotation radial radial' incoming outgoing a b first last first' last'
  change -Real.pi < θ + (b - a) ∧ θ + (b - a) ≤ Real.pi
  constructor
  · by_contra h
    have δpos : 0 < a - b := by linarith [original.1, le_of_not_gt h]
    let u := (θ + Real.pi) / (a - b)
    have time : u ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [original.1]) δpos.le,
      (div_le_one δpos).mpr (by linarith [le_of_not_gt h])⟩
    have mul := div_mul_cancel₀ (θ + Real.pi) δpos.ne'
    change u * (a - b) = _ at mul
    exact no_half_turn u time (Or.inr (by linarith))
  · by_contra h
    have δpos : 0 < b - a := by linarith [original.2, lt_of_not_ge h]
    let u := (Real.pi - θ) / (b - a)
    have time : u ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [original.2]) δpos.le,
      (div_le_one δpos).mpr (by linarith [lt_of_not_ge h])⟩
    have mul := div_mul_cancel₀ (Real.pi - θ) δpos.ne'
    change u * (b - a) = _ at mul
    exact no_half_turn u time (Or.inl (by linarith))

end Unfoldings
