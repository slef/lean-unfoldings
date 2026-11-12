module

public import Unfoldings.Geometry.RayStrip

/-! Distinct positively directed rays enclose positive width at every positive height. -/

@[expose] public section

namespace Unfoldings

namespace MonotoneStrip

theorem rayStrip_width_pos (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im)
    (different : (starRingEnd ℂ p * q).im ≠ 0) {h : ℝ} (positive : 0 < h) :
    (rayStrip p q px py qx qy).lower.coordinate h <
      (rayStrip p q px py qx qy).upper.coordinate h := by
  change min ((MonotoneHeightGraph.ray p px py).coordinate h)
      ((MonotoneHeightGraph.ray q qx qy).coordinate h) <
    max ((MonotoneHeightGraph.ray p px py).coordinate h)
      ((MonotoneHeightGraph.ray q qx qy).coordinate h)
  simp only [MonotoneHeightGraph.ray_coordinate]
  apply lt_of_le_of_ne min_le_max
  intro equal
  have products : p.re / (p.re + p.im) * h = q.re / (q.re + q.im) * h :=
    le_antisymm ((le_max_left _ _).trans (equal.symm.trans_le (min_le_right _ _)))
      ((le_max_right _ _).trans (equal.symm.trans_le (min_le_left _ _)))
  have slopes := mul_right_cancel₀ positive.ne' products
  have ratios := (div_eq_div_iff (add_pos px py).ne' (add_pos qx qy).ne').mp slopes
  apply different
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

end MonotoneStrip

end Unfoldings
