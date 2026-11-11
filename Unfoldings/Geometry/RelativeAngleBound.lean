module

public import Unfoldings.Geometry.ComplexHingeTurn
public import Unfoldings.Geometry.ComplexHeadingTransport

/-!
# Comparing planar directions through oriented reference rays

If two pairs lie on the same respective side of their reference rays, their
angular distance is bounded by the reference-ray distance plus the difference
of their angles from those rays. This transfers a one-direction alignment to
all directions once both face charts have small projection-angle distortion.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Positive complex halfplanes give the exact difference of angles from their boundary ray. -/
theorem complex_angle_eq_abs_sub_of_same_halfplane {r x y : ℂ}
    (first : 0 < (starRingEnd ℂ r * x).im) (last : 0 < (starRingEnd ℂ r * y).im) :
    InnerProductGeometry.angle x y =
      |InnerProductGeometry.angle r x - InnerProductGeometry.angle r y| := by
  let L := Complex.orthonormalBasisOneI.repr
  have first_area : 0 < orient 0 (L r) (L x) := by
    simpa only [L, orient_complex_repr_zero] using first
  have last_area : 0 < orient 0 (L r) (L y) := by
    simpa only [L, orient_complex_repr_zero] using last
  calc
    _ = InnerProductGeometry.angle (L x) (L y) := (L.toLinearIsometry.angle_map _ _).symm
    _ = |InnerProductGeometry.angle (L r) (L x) -
        InnerProductGeometry.angle (L r) (L y)| :=
      angle_eq_abs_sub_of_same_halfplane first_area last_area
    _ = _ := congrArg abs (congrArg₂ (· - ·)
      (L.toLinearIsometry.angle_map r x) (L.toLinearIsometry.angle_map r y))

/-- Either common complex halfplane gives the same exact angular subtraction. -/
theorem complex_angle_eq_abs_sub_of_cross_product_pos {r x y : ℂ}
    (sides : 0 < (starRingEnd ℂ r * x).im * (starRingEnd ℂ r * y).im) :
    InnerProductGeometry.angle x y =
      |InnerProductGeometry.angle r x - InnerProductGeometry.angle r y| := by
  rcases mul_pos_iff.mp sides with positive | negative
  · exact complex_angle_eq_abs_sub_of_same_halfplane positive.1 positive.2
  · have reverse (v : ℂ) : (starRingEnd ℂ (-r) * v).im = -(starRingEnd ℂ r * v).im := by
      simp only [map_neg, neg_mul, Complex.neg_im]
    have equal := complex_angle_eq_abs_sub_of_same_halfplane
      (r := -r) (x := x) (y := y)
      (by rw [reverse]; exact neg_pos.mpr negative.1)
      (by rw [reverse]; exact neg_pos.mpr negative.2)
    rw [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_left] at equal
    have difference : (Real.pi - InnerProductGeometry.angle r x) -
        (Real.pi - InnerProductGeometry.angle r y) =
      -(InnerProductGeometry.angle r x - InnerProductGeometry.angle r y) := by ring
    rwa [difference, abs_neg] at equal

/-- Actual planar direction comparison from an aligned reference pair and angular distortions. -/
theorem complex_relative_angle_le {r s x y : ℂ}
    (rne : r ≠ 0) (sne : s ≠ 0) (yne : y ≠ 0)
    (sides : 0 < (starRingEnd ℂ r * x).im * (starRingEnd ℂ s * y).im) :
    InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle r s +
      |InnerProductGeometry.angle r x - InnerProductGeometry.angle s y| := by
  let z := NormedSpace.normalize (r / s)
  let c := ‖r / s‖⁻¹
  have quotient_ne := div_ne_zero rne sne
  have positive : 0 < c := inv_pos.mpr (norm_pos_iff.mpr quotient_ne)
  have unit : ‖z‖ = 1 := NormedSpace.norm_normalize quotient_ne
  have zne : z ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at unit
    norm_num at unit
  have aligns : z * s = c • r := by
    change (‖r / s‖⁻¹ • (r / s)) * s = c • r
    simp only [Complex.real_smul]
    rw [mul_assoc, div_mul_cancel₀ _ sne]
  have scaled_cross : (starRingEnd ℂ (c • r) * (z * y)).im =
      c * (starRingEnd ℂ r * (z * y)).im := by
    simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have last_cross : c * (starRingEnd ℂ r * (z * y)).im = (starRingEnd ℂ s * y).im := by
    rw [← scaled_cross, ← aligns]
    exact complex_cross_mul_unit z s y unit
  have aligned_sides : 0 < (starRingEnd ℂ r * x).im * (starRingEnd ℂ r * (z * y)).im := by
    apply (mul_pos_iff_of_pos_left positive).mp
    calc
      _ = (starRingEnd ℂ r * x).im * (c * (starRingEnd ℂ r * (z * y)).im) := by ring
      _ > 0 := by rw [last_cross]; exact sides
  have last_angle : InnerProductGeometry.angle r (z * y) = InnerProductGeometry.angle s y := by
    calc
      _ = InnerProductGeometry.angle (c • r) (z * y) :=
        (InnerProductGeometry.angle_smul_left_of_pos _ _ positive).symm
      _ = InnerProductGeometry.angle (z * s) (z * y) := by rw [aligns]
      _ = _ := Complex.angle_mul_left zne s y
  have rotation_angle : InnerProductGeometry.angle (z * y) y = InnerProductGeometry.angle r s := by
    calc
      _ = InnerProductGeometry.angle (z * y) (1 * y) := by rw [one_mul]
      _ = InnerProductGeometry.angle z 1 := Complex.angle_mul_right yne z 1
      _ = InnerProductGeometry.angle (z * s) (1 * s) := (Complex.angle_mul_right sne z 1).symm
      _ = InnerProductGeometry.angle (c • r) s := by rw [aligns, one_mul]
      _ = _ := InnerProductGeometry.angle_smul_left_of_pos _ _ positive
  have residual := complex_angle_eq_abs_sub_of_cross_product_pos aligned_sides
  rw [last_angle] at residual
  calc
    _ ≤ InnerProductGeometry.angle x (z * y) + InnerProductGeometry.angle (z * y) y :=
      InnerProductGeometry.angle_le_angle_add_angle _ _ _
    _ = _ := by rw [residual, rotation_angle]; ring

/-- A one-direction alignment transfers to all actual directions with two angular-error budgets. -/
theorem linear_relative_angle_le (F G : Plane →ₗ[ℝ] ℂ) {u v : Plane}
    (une : u ≠ 0) (vne : v ≠ 0) (fu_ne : F u ≠ 0) (gu_ne : G u ≠ 0) (gv_ne : G v ≠ 0)
    {B ε η : ℝ} (reference : InnerProductGeometry.angle (F u) (G u) ≤ B)
    (first_error : |InnerProductGeometry.angle u v - InnerProductGeometry.angle (F u) (F v)| ≤ ε)
    (last_error : |InnerProductGeometry.angle u v - InnerProductGeometry.angle (G u) (G v)| ≤ η)
    (sides : orient 0 u v ≠ 0 →
      0 < (starRingEnd ℂ (F u) * F v).im * (starRingEnd ℂ (G u) * G v).im) :
    InnerProductGeometry.angle (F v) (G v) ≤ B + ε + η := by
  have εnonneg := (abs_nonneg _).trans first_error
  have ηnonneg := (abs_nonneg _).trans last_error
  by_cases collinear : orient 0 u v = 0
  · obtain ⟨c, expression⟩ := exists_lineMap_of_orient_eq_zero une.symm collinear
    rw [AffineMap.lineMap_apply_module'] at expression
    simp only [sub_zero, add_zero] at expression
    have cne : c ≠ 0 := by
      intro zero
      exact vne (by rw [expression, zero, zero_smul])
    rw [expression, map_smul, map_smul, InnerProductGeometry.angle_smul_smul cne]
    exact reference.trans (by linarith)
  · have first_bounds := abs_le.mp first_error
    have last_bounds := abs_le.mp last_error
    have difference : |InnerProductGeometry.angle (F u) (F v) -
        InnerProductGeometry.angle (G u) (G v)| ≤ ε + η :=
      abs_le.mpr ⟨by linarith [first_bounds.1, last_bounds.2],
        by linarith [first_bounds.2, last_bounds.1]⟩
    have comparison := complex_relative_angle_le fu_ne gu_ne gv_ne (sides collinear)
    linarith

end Unfoldings
