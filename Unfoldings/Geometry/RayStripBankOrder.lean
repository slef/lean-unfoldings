module

public import Unfoldings.Geometry.RayHeightSegments

/-! A positively oriented quadrant ray pair retains the names of both strip banks. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im) (qx : 0 < q.re) (qy : 0 < q.im)

theorem rayStrip_lower_point_eq_last {h : ℝ} (nonnegative : 0 ≤ h)
    (cross : 0 ≤ (starRingEnd ℂ p * q).im) :
    (rayStrip p q px py qx qy).lower.point h = (MonotoneHeightGraph.ray q qx qy).point h := by
  have slope : q.re / (q.re + q.im) ≤ p.re / (p.re + p.im) := by
    apply (div_le_div_iff₀ (add_pos qx qy) (add_pos px py)).mpr
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at cross
    nlinarith
  have equal : (rayStrip p q px py qx qy).lower.coordinate h =
      (MonotoneHeightGraph.ray q qx qy).coordinate h := by
    change min ((MonotoneHeightGraph.ray p px py).coordinate h)
      ((MonotoneHeightGraph.ray q qx qy).coordinate h) = _
    simp only [MonotoneHeightGraph.ray_coordinate]
    exact min_eq_right (mul_le_mul_of_nonneg_right slope nonnegative)
  apply Complex.ext
  · exact equal
  · change h - (rayStrip p q px py qx qy).lower.coordinate h =
      h - (MonotoneHeightGraph.ray q qx qy).coordinate h
    rw [equal]

theorem rayStrip_upper_point_eq_first {h : ℝ} (nonnegative : 0 ≤ h)
    (cross : 0 ≤ (starRingEnd ℂ p * q).im) :
    (rayStrip p q px py qx qy).upper.point h = (MonotoneHeightGraph.ray p px py).point h := by
  have slope : q.re / (q.re + q.im) ≤ p.re / (p.re + p.im) := by
    apply (div_le_div_iff₀ (add_pos qx qy) (add_pos px py)).mpr
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at cross
    nlinarith
  have equal : (rayStrip p q px py qx qy).upper.coordinate h =
      (MonotoneHeightGraph.ray p px py).coordinate h := by
    change max ((MonotoneHeightGraph.ray p px py).coordinate h)
      ((MonotoneHeightGraph.ray q qx qy).coordinate h) = _
    simp only [MonotoneHeightGraph.ray_coordinate]
    exact max_eq_left (mul_le_mul_of_nonneg_right slope nonnegative)
  apply Complex.ext
  · exact equal
  · change h - (rayStrip p q px py qx qy).upper.coordinate h =
      h - (MonotoneHeightGraph.ray p px py).coordinate h
    rw [equal]

end Unfoldings.MonotoneStrip
