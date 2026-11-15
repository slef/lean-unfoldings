module

public import Unfoldings.Cone.RotatedSectorRecognition
public import Unfoldings.Geometry.OpeningCommonDirection
public import Unfoldings.Geometry.PositiveGapAngle
public import Mathlib.Tactic.FieldSimp

/-! Original strictly outward incident edges determine the occupied left corner sector. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- Keep the real width between the outgoing ray and reversed incoming ray. -/
def radialLeftCornerWidth (radial incoming outgoing : ℂ) : ℝ :=
  Real.pi + (incoming / radial).arg - (outgoing / radial).arg

/-- The original outgoing bank direction is the first oriented sector axis. -/
def radialLeftCornerFrame (radial outgoing : ℂ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation (Circle.exp (radial.arg + (outgoing / radial).arg))

/-- Positive radial progress keeps the complementary corner width strictly below a full turn. -/
theorem radialLeftCornerWidth_bounds (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    0 < radialLeftCornerWidth radial incoming outgoing ∧
      radialLeftCornerWidth radial incoming outgoing < 2 * Real.pi := by
  have α := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos last)))
  have β := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos first)))
  dsimp [radialLeftCornerWidth]
  constructor <;> linarith [α.1, α.2, β.1, β.2]

/-- Exact positive-radius polar coordinates in the actual original source-relative frame. -/
theorem polarRay_arg_eq_normalized (z : ℂ) (nonzero : z ≠ 0) :
    polarRay z.arg = z / (‖z‖ : ℂ) := by
  have norm_nonzero : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero)
  apply (eq_div_iff norm_nonzero).mpr
  have same : (‖z‖ : ℂ) * polarRay z.arg = z := Complex.norm_mul_exp_arg_mul_I z
  exact (mul_comm _ _).trans same

theorem polarRay_arg_add_arg_div (p d : ℂ) (p_nonzero : p ≠ 0) (d_nonzero : d ≠ 0) :
    polarRay (p.arg + (d / p).arg) = d / (‖d‖ : ℂ) := by
  rw [polarRay_add, polarRay_arg_eq_normalized p p_nonzero,
    polarRay_arg_eq_normalized (d / p) (div_ne_zero d_nonzero p_nonzero),
    norm_div, Complex.ofReal_div]
  have pnorm_nonzero : (‖p‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr p_nonzero)
  have dnorm_nonzero : (‖d‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d_nonzero)
  field_simp

/-- The original source-circle normal is strictly inside the selected left sector. -/
theorem radialLeftCorner_normal_mem (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    Complex.I * radial ∈ interior (radialLeftCornerFrame radial outgoing ''
      closedAngularSector (radialLeftCornerWidth radial incoming outgoing)) := by
  have radial_nonzero : radial ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have α := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos last)))
  have β := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (complex_div_re_pos_of_inner_pos first)))
  let θ := Real.pi / 2 - (outgoing / radial).arg
  have heading : θ ∈ Set.Ioo 0 (radialLeftCornerWidth radial incoming outgoing) := by
    dsimp [θ, radialLeftCornerWidth]
    constructor <;> linarith [α.1, α.2, β.1, β.2]
  let H := (radialLeftCornerFrame radial outgoing).toHomeomorph
  change Complex.I * radial ∈ interior
    (H '' closedAngularSector (radialLeftCornerWidth radial incoming outgoing))
  rw [← H.image_interior]
  refine ⟨(‖radial‖ : ℂ) * polarRay θ,
    polar_mem_interior_closedAngularSector _ _ θ (norm_pos_iff.mpr radial_nonzero) heading, ?_⟩
  have placed := rotate_polar_point (radial.arg + (outgoing / radial).arg) θ ‖radial‖₊
  have angle : radial.arg + (outgoing / radial).arg + θ = radial.arg + Real.pi / 2 := by
    dsimp [θ]
    ring
  rw [angle] at placed
  have quarter : polarRay (Real.pi / 2) = Complex.I := by apply Complex.ext <;> simp
  have original : (‖radial‖ : ℂ) * polarRay radial.arg = radial :=
    Complex.norm_mul_exp_arg_mul_I radial
  calc
    _ = (‖radial‖ : ℂ) * polarRay (radial.arg + Real.pi / 2) := placed
    _ = Complex.I * ((‖radial‖ : ℂ) * polarRay radial.arg) := by
      rw [polarRay_add, quarter]
      ring
    _ = _ := congrArg (Complex.I * ·) original

/-- Rescaling a genuine ray generator by a positive scalar preserves the whole ray. -/
theorem nonnegativeRay_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (direction : E) {r : ℝ} (positive : 0 < r) :
    nonnegativeRay (r • direction) = nonnegativeRay direction := by
  ext v
  constructor
  · rintro ⟨t, nonnegative, equal⟩
    exact ⟨t * r, mul_nonneg nonnegative positive.le, by rwa [smul_smul] at equal⟩
  · rintro ⟨t, nonnegative, equal⟩
    refine ⟨t / r, div_nonneg nonnegative positive.le, ?_⟩
    rwa [smul_smul, div_mul_cancel₀ _ positive.ne']

theorem image_nonnegativeRay {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F) (direction : E) :
    L '' nonnegativeRay direction = nonnegativeRay (L direction) := by
  ext v
  constructor
  · rintro ⟨w, ⟨t, nonnegative, rfl⟩, rfl⟩
    exact ⟨t, nonnegative, by rw [map_smul]⟩
  · rintro ⟨t, nonnegative, rfl⟩
    exact ⟨t • direction, ⟨t, nonnegative, rfl⟩, by rw [map_smul]⟩

theorem nonnegativeRay_eq_complex_range (direction : ℂ) :
    nonnegativeRay direction = Set.range (fun r : ℝ≥0 => (r : ℂ) * direction) := by
  ext v
  constructor
  · rintro ⟨t, nonnegative, equal⟩
    refine ⟨⟨t, nonnegative⟩, ?_⟩
    change (t : ℂ) * direction = v
    simpa only [Complex.real_smul] using equal.symm
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.coe_nonneg, by rw [Complex.real_smul]⟩

/-- Normalizing an original edge leaves its actual whole bank ray unchanged. -/
theorem nonnegativeRay_div_norm (direction : ℂ) (nonzero : direction ≠ 0) :
    nonnegativeRay (direction / (‖direction‖ : ℂ)) = nonnegativeRay direction := by
  have same : direction / (‖direction‖ : ℂ) = ‖direction‖⁻¹ • direction := by
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  rw [same]
  exact nonnegativeRay_pos_smul direction (inv_pos.mpr (norm_pos_iff.mpr nonzero))

/-- The sector's two banks are exactly the original outgoing and reversed incoming edge rays. -/
theorem radialLeftCorner_bank_rays (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    nonnegativeRay (-incoming) ∪ nonnegativeRay outgoing =
      radialLeftCornerFrame radial outgoing ''
        (Set.range (fun r : ℝ≥0 => (r : ℂ)) ∪ Set.range (fun r : ℝ≥0 =>
          (r : ℂ) * polarRay (radialLeftCornerWidth radial incoming outgoing))) := by
  have radial_nonzero : radial ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have incoming_nonzero : incoming ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_right, lt_self_iff_false] at first
  have outgoing_nonzero : outgoing ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_right, lt_self_iff_false] at last
  let F := radialLeftCornerFrame radial outgoing
  let width := radialLeftCornerWidth radial incoming outgoing
  have initial : F.toLinearMap 1 = outgoing / (‖outgoing‖ : ℂ) := by
    change polarRay (radial.arg + (outgoing / radial).arg) * 1 = _
    rw [mul_one, polarRay_arg_add_arg_div radial outgoing radial_nonzero outgoing_nonzero]
  have terminal : F.toLinearMap (polarRay width) = -incoming / (‖incoming‖ : ℂ) := by
    change polarRay (radial.arg + (outgoing / radial).arg) * polarRay width = _
    rw [← polarRay_add]
    have angle : radial.arg + (outgoing / radial).arg + width =
        radial.arg + (incoming / radial).arg + Real.pi := by
      dsimp [width, radialLeftCornerWidth]
      ring
    have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
    rw [angle, polarRay_add,
      polarRay_arg_add_arg_div radial incoming radial_nonzero incoming_nonzero, half]
    ring
  have real_ray : Set.range (fun r : ℝ≥0 => (r : ℂ)) = nonnegativeRay (1 : ℂ) := by
    rw [nonnegativeRay_eq_complex_range]
    simp only [mul_one]
  rw [Set.image_union, real_ray, ← nonnegativeRay_eq_complex_range]
  change nonnegativeRay (-incoming) ∪ nonnegativeRay outgoing =
    F.toLinearMap '' nonnegativeRay 1 ∪ F.toLinearMap '' nonnegativeRay (polarRay width)
  rw [image_nonnegativeRay, image_nonnegativeRay, initial, terminal,
    nonnegativeRay_div_norm outgoing outgoing_nonzero]
  have negative_normalized : nonnegativeRay (-incoming / (‖incoming‖ : ℂ)) =
      nonnegativeRay (-incoming) := by
    simpa only [norm_neg] using
      nonnegativeRay_div_norm (-incoming) (neg_ne_zero.mpr incoming_nonzero)
  rw [negative_normalized, Set.union_comm]

/-- The corner aperture is the positive geometric angle of the actual original bank vectors. -/
theorem radialLeftCornerWidth_eq_positiveGapAngle (radial incoming outgoing : ℂ)
    (first : 0 < inner ℝ radial incoming) (last : 0 < inner ℝ radial outgoing) :
    radialLeftCornerWidth radial incoming outgoing = positiveGapAngle outgoing (-incoming) := by
  have radial_nonzero : radial ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_left, lt_self_iff_false] at first
  have incoming_nonzero : incoming ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_right, lt_self_iff_false] at first
  have outgoing_nonzero : outgoing ≠ 0 := by
    intro zero
    simp only [zero, inner_zero_right, lt_self_iff_false] at last
  obtain ⟨positive, small⟩ := radialLeftCornerWidth_bounds radial incoming outgoing first last
  symm
  apply positiveGapAngle_of_normalized_rotation outgoing (-incoming) outgoing_nonzero
    positive small
  rw [norm_neg, ← polarRay_arg_add_arg_div radial outgoing radial_nonzero outgoing_nonzero,
    ← polarRay_add]
  have angle : radialLeftCornerWidth radial incoming outgoing +
      (radial.arg + (outgoing / radial).arg) =
        radial.arg + (incoming / radial).arg + Real.pi := by
    dsimp [radialLeftCornerWidth]
    ring
  have half : polarRay Real.pi = -1 := by apply Complex.ext <;> simp
  rw [angle, polarRay_add,
    polarRay_arg_add_arg_div radial incoming radial_nonzero incoming_nonzero, half]
  ring

end Unfoldings
