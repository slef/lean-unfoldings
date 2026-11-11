module

public import Unfoldings.Geometry.AcuteWedgeFrame

/-! A closed acute wedge and all sufficiently close directions share one open quadrant. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem angle_one_mul_polarRay {r a : ℝ} (positive : 0 < r)
    (nonnegative : 0 ≤ a) (small : a ≤ Real.pi) :
    InnerProductGeometry.angle (1 : ℂ) ((r : ℂ) * polarRay a) = a := by
  rw [← Complex.real_smul, InnerProductGeometry.angle_smul_right_of_pos _ _ positive]
  simpa only [polarRay_zero, sub_zero] using angle_polarRay 0 a
    (by simpa only [sub_zero] using nonnegative) (by simpa only [sub_zero] using small)

theorem angle_I_mul_polarRay {r a : ℝ} (positive : 0 < r)
    (nonnegative : 0 ≤ a) (small : a ≤ Real.pi / 2) :
    InnerProductGeometry.angle Complex.I ((r : ℂ) * polarRay a) = Real.pi / 2 - a := by
  rw [← Complex.real_smul, InnerProductGeometry.angle_smul_right_of_pos _ _ positive]
  have quarter : polarRay (Real.pi / 2) = Complex.I := by apply Complex.ext <;> simp
  calc
    _ = InnerProductGeometry.angle (polarRay a) (polarRay (Real.pi / 2)) := by
      rw [quarter, InnerProductGeometry.angle_comm]
    _ = _ := angle_polarRay a _ (by linarith) (by linarith [Real.pi_pos])

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

/-- Every original nonzero wedge direction has the same positive margin from both quadrant axes. -/
theorem axis_bounds {x : Plane} (inside : InDirectionWedge u v x) (nonzero : x ≠ 0) :
    InnerProductGeometry.angle (1 : ℂ) (B.place x) ≤ Real.pi / 2 - B.margin ∧
      InnerProductGeometry.angle Complex.I (B.place x) ≤ Real.pi / 2 - B.margin := by
  have first_length := norm_pos_iff.mpr B.first_ne
  have last_length := norm_pos_iff.mpr B.last_ne
  have margin_nonnegative := B.positive.le
  have margin_small : B.margin ≤ Real.pi / 2 := by linarith [B.small, Real.pi_pos]
  have upper_nonnegative : 0 ≤ Real.pi / 2 - B.margin := by linarith
  have upper_small : Real.pi / 2 - B.margin ≤ Real.pi / 2 := by linarith [B.positive]
  have first_real : InnerProductGeometry.angle (1 : ℂ) (B.place u) ≤ Real.pi / 2 - B.margin := by
    rw [B.first, angle_one_mul_polarRay first_length margin_nonnegative
      (margin_small.trans (by linarith [Real.pi_pos]))]
    linarith [B.small]
  have last_real : InnerProductGeometry.angle (1 : ℂ) (B.place v) ≤ Real.pi / 2 - B.margin := by
    rw [B.last, angle_one_mul_polarRay last_length upper_nonnegative
      (upper_small.trans (by linarith [Real.pi_pos]))]
  have first_imaginary : InnerProductGeometry.angle Complex.I (B.place u) ≤
      Real.pi / 2 - B.margin := by
    rw [B.first, angle_I_mul_polarRay first_length margin_nonnegative margin_small]
  have last_imaginary : InnerProductGeometry.angle Complex.I (B.place v) ≤
      Real.pi / 2 - B.margin := by
    rw [B.last, angle_I_mul_polarRay last_length upper_nonnegative upper_small]
    linarith [B.small]
  have mapped : InDirectionWedge (B.place u) (B.place v) (B.place x) := by
    obtain ⟨a, b, apos, bpos, expression⟩ := inside
    exact ⟨a, b, apos, bpos, by rw [expression, map_add, map_smul, map_smul]⟩
  have first_ne : B.place u ≠ 0 := by simpa only [map_zero] using B.place.injective.ne B.first_ne
  have last_ne : B.place v ≠ 0 := by simpa only [map_zero] using B.place.injective.ne B.last_ne
  have xne : B.place x ≠ 0 := by simpa only [map_zero] using B.place.injective.ne nonzero
  exact ⟨angle_le_of_inDirectionWedge_axis_bounds one_ne_zero first_ne last_ne xne
      upper_nonnegative upper_small first_real last_real mapped,
    angle_le_of_inDirectionWedge_axis_bounds Complex.I_ne_zero first_ne last_ne xne
      upper_nonnegative upper_small first_imaginary last_imaginary mapped⟩

/-- Every actual direction close to that closed wedge lies strictly in the same open quadrant. -/
theorem quadrant_of_angle_close {x : Plane} (inside : InDirectionWedge u v x) (nonzero : x ≠ 0)
    {y : ℂ} (close : InnerProductGeometry.angle (B.place x) y < B.margin) :
    0 < y.re ∧ 0 < y.im := by
  have bounds := B.axis_bounds inside nonzero
  have real_positive := inner_pos_of_angle_close bounds.1 close (by linarith)
  have imaginary_positive := inner_pos_of_angle_close bounds.2 close (by linarith)
  constructor
  · simpa only [Complex.inner, map_one, mul_one] using real_positive
  · simpa [Complex.inner] using imaginary_positive

/-- Transport an already calibrated complex direction into this wedge's fixed quadrant frame. -/
theorem quadrant_of_projected_angle_close {x : Plane}
    (inside : InDirectionWedge u v x) (nonzero : x ≠ 0) {y : ℂ}
    (close : InnerProductGeometry.angle y (Complex.orthonormalBasisOneI.repr.symm x) < B.margin) :
    0 < ((Complex.orthonormalBasisOneI.repr.trans B.place) y).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans B.place) y).im := by
  apply B.quadrant_of_angle_close inside nonzero
  let L := Complex.orthonormalBasisOneI.repr.trans B.place
  have frame := L.toLinearIsometry.angle_map
    (Complex.orthonormalBasisOneI.repr.symm x) y
  have initial : L (Complex.orthonormalBasisOneI.repr.symm x) = B.place x := by
    change B.place (Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm x)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  change InnerProductGeometry.angle (L (Complex.orthonormalBasisOneI.repr.symm x))
    (L y) = _ at frame
  rw [initial, InnerProductGeometry.angle_comm
    (Complex.orthonormalBasisOneI.repr.symm x) y] at frame
  exact frame.le.trans_lt close

end AcuteWedgeFrame
end Unfoldings
