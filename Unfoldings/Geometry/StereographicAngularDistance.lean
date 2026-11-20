module

public import Unfoldings.Geometry.StereographicChord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Angular distances and the diameter bound in the centered chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry

private theorem sq_sin_half_angle {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.sin (angle u v / 2) ^ 2 = ‖u - v‖ ^ 2 / 4 := by
  have cos := cos_angle_mul_norm_mul_norm u v
  rw [hu, hv, mul_one, mul_one] at cos
  have sin := Real.cos_two_mul' (angle u v / 2)
  have trig := Real.sin_sq_add_cos_sq (angle u v / 2)
  rw [show 2 * (angle u v / 2) = angle u v by ring] at sin
  rw [norm_sub_pow_two_real, hu, hv]
  linarith

/-- On the unit disk, angular separation of the images is no more than
twice the planar distance. The proof uses the exact chord formula. -/
theorem angle_inverseStereographic_le {x y : Plane} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    angle (inverseStereographic x) (inverseStereographic y) ≤ 2 * ‖x - y‖ := by
  let d := ‖x - y‖
  let a := ‖x‖
  let b := ‖y‖
  have d0 : 0 ≤ d := norm_nonneg _
  have d_ab : d ≤ a + b := norm_sub_le x y
  have ab_le : a + b ≤ 2 := by dsimp [a, b]; linarith
  have d_le : d ≤ 2 := d_ab.trans ab_le
  have ab_nonneg : 0 ≤ a + b := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have ab2 : ((a + b) / 2) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (div_nonneg ab_nonneg (by norm_num))
      (zero_le_one : (0 : ℝ) ≤ 1)).2 (show (a + b) / 2 ≤ 1 by linarith)
    simpa only [one_pow] using h
  have chord_den : (1 + d ^ 2 / 4) ^ 2 ≤ (1 + a ^ 2) * (1 + b ^ 2) := by
    have square := (sq_le_sq₀ d0 ab_nonneg).2 d_ab
    calc
      _ ≤ (1 + ((a + b) / 2) ^ 2) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 (by linarith)
      _ ≤ _ := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr ab2) (sq_nonneg ((a - b) / 2)),
          sq_nonneg (((a - b) / 2) ^ 2)]
  let θ := angle (inverseStereographic x) (inverseStereographic y) / 2
  have θ0 : 0 ≤ θ := by dsimp [θ]; exact div_nonneg (angle_nonneg _ _) (by norm_num)
  have θ_le : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    linarith [angle_le_pi (inverseStereographic x) (inverseStereographic y)]
  have sin_sq : Real.sin θ ^ 2 = d ^ 2 / ((1 + a ^ 2) * (1 + b ^ 2)) := by
    dsimp [θ, a, b, d]
    rw [sq_sin_half_angle (inverseStereographic_unit x) (inverseStereographic_unit y),
      inverseStereographic_chord_sq]
    ring
  have sine_bound : Real.sin θ ≤ d / (1 + d ^ 2 / 4) := by
    apply (sq_le_sq₀ (Real.sin_nonneg_of_nonneg_of_le_pi θ0
      (by linarith [Real.pi_pos])) (by positivity)).mp
    rw [sin_sq, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) chord_den
  let t := Real.arctan (d / 2)
  have t0 : 0 ≤ t := Real.arctan_nonneg.mpr (by positivity)
  have t_le : t ≤ Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_mono (by linarith)
  have sin_t : Real.sin (2 * t) = d / (1 + d ^ 2 / 4) := by
    dsimp [t]
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have h : 0 < Real.sqrt (1 + (d / 2) ^ 2) := by positivity
    rw [show 2 * (d / 2 / Real.sqrt (1 + (d / 2) ^ 2)) *
        (1 / Real.sqrt (1 + (d / 2) ^ 2)) =
      d / Real.sqrt (1 + (d / 2) ^ 2) ^ 2 by field_simp [h.ne']]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have angle_bound : θ ≤ 2 * t :=
    (Real.strictMonoOn_sin.le_iff_le ⟨by linarith [Real.pi_pos], θ_le⟩
      ⟨by linarith [Real.pi_pos], by linarith⟩).mp (sine_bound.trans_eq sin_t.symm)
  have arc := Real.arctan_le_self (show 0 ≤ d / 2 by positivity)
  change t ≤ d / 2 at arc
  calc
    angle (inverseStereographic x) (inverseStereographic y) = 2 * θ := by dsimp [θ]; ring
    _ ≤ 2 * d := by linarith

end Unfoldings.Cap
