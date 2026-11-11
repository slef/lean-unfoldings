module

public import Unfoldings.Geometry.RayStrip
public import Unfoldings.Geometry.RecoverableStripPinches

/-! Between two source rays, every reopening pinch is the source itself. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

theorem rayStrip_coordinate_homogeneous (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) {h : ℝ} (nonnegative : 0 ≤ h) :
    (rayStrip p q px py qx qy).lower.coordinate h =
      (rayStrip p q px py qx qy).lower.coordinate 1 * h ∧
    (rayStrip p q px py qx qy).upper.coordinate h =
      (rayStrip p q px py qx qy).upper.coordinate 1 * h := by
  constructor
  · simpa only [rayStrip, MonotoneHeightGraph.min, MonotoneHeightGraph.ray_coordinate,
      mul_one] using
      (min_mul_of_nonneg (p.re / (p.re + p.im)) (q.re / (q.re + q.im)) nonnegative).symm
  · simpa only [rayStrip, MonotoneHeightGraph.max, MonotoneHeightGraph.ray_coordinate,
      mul_one] using
      (max_mul_of_nonneg (p.re / (p.re + p.im)) (q.re / (q.re + q.im)) nonnegative).symm

theorem rayStrip_recoverablePinchesIn (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) (b : ℝ) :
    (rayStrip p q px py qx qy).RecoverablePinchesIn {0} 0 b := by
  intro h slab same k later width
  let a := p.re / (p.re + p.im)
  let c := q.re / (q.re + q.im)
  have coordinate (h : ℝ) :
      (rayStrip p q px py qx qy).lower.coordinate h = Min.min (a * h) (c * h) ∧
      (rayStrip p q px py qx qy).upper.coordinate h = Max.max (a * h) (c * h) := by
    constructor <;> simp only [rayStrip, MonotoneHeightGraph.min, MonotoneHeightGraph.max,
      MonotoneHeightGraph.ray_coordinate] <;> rfl
  by_cases zero : h = 0
  · subst h
    have source := rayStrip_source p q px py qx qy
    apply Complex.ext
    · exact source.1
    · change 0 - (rayStrip p q px py qx qy).lower.coordinate 0 = 0
      rw [source.1, sub_self]
  · rw [(coordinate h).1, (coordinate h).2] at same
    have equal : a * h = c * h := le_antisymm
      ((le_max_left _ _).trans (same.symm.trans_le (min_le_right _ _)))
      ((le_max_right _ _).trans (same.symm.trans_le (min_le_left _ _)))
    have slopes : a = c := mul_right_cancel₀ zero equal
    rw [(coordinate k).1, (coordinate k).2, slopes, min_self, max_self] at width
    exact (lt_irrefl _ width).elim

end Unfoldings.MonotoneStrip
