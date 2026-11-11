module

public import Unfoldings.Geometry.MonotoneStripInsertion
public import Unfoldings.Geometry.DirectionWedgeOperations

/-! Represent a source-centered wedge by monotone ray boundaries. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace MonotoneHeightGraph

def ray (p : ℂ) (horizontal : 0 < p.re) (vertical : 0 < p.im) : MonotoneHeightGraph :=
  affine 0 0 (p.re / (p.re + p.im))
    (div_nonneg horizontal.le (add_pos horizontal vertical).le)
    ((div_le_one (add_pos horizontal vertical)).mpr (by linarith))

theorem ray_coordinate (p : ℂ) (horizontal : 0 < p.re) (vertical : 0 < p.im) (h : ℝ) :
    (ray p horizontal vertical).coordinate h = p.re / (p.re + p.im) * h := by
  change 0 + p.re / (p.re + p.im) * (h - 0) = _
  ring

end MonotoneHeightGraph

namespace MonotoneStrip

/-- On nonnegative heights these are the two original rays. The min/max continuation
on negative heights is only to give the height graphs their required total domain. -/
def rayStrip (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) : MonotoneStrip :=
  let P := MonotoneHeightGraph.ray p px py
  let Q := MonotoneHeightGraph.ray q qx qy
  ⟨P.min Q, P.max Q, fun _ => min_le_max⟩

theorem rayStrip_source (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) :
    (rayStrip p q px py qx qy).lower.coordinate 0 = 0 ∧
      (rayStrip p q px py qx qy).upper.coordinate 0 = 0 := by
  simp [rayStrip, MonotoneHeightGraph.min, MonotoneHeightGraph.max,
    MonotoneHeightGraph.ray, MonotoneHeightGraph.affine]

theorem rayStrip_of_cone (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) {z : ℂ} (inside : InDirectionWedge p q z) :
    z ∈ (rayStrip p q px py qx qy).carrier := by
  obtain ⟨r, s, rnonnegative, snonnegative, representation⟩ := inside
  let a := p.re / (p.re + p.im)
  let b := q.re / (q.re + q.im)
  have pheight : 0 < p.re + p.im := add_pos px py
  have qheight : 0 < q.re + q.im := add_pos qx qy
  have a_eq : a * (p.re + p.im) = p.re := div_mul_cancel₀ _ pheight.ne'
  have b_eq : b * (q.re + q.im) = q.re := div_mul_cancel₀ _ qheight.ne'
  have real : z.re = r * p.re + s * q.re := by
    rw [representation, Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul,
      smul_eq_mul]
  have imaginary : z.im = r * p.im + s * q.im := by
    rw [representation, Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul,
      smul_eq_mul]
  have nonnegative : 0 ≤ z.re + z.im := by rw [real, imaginary]; positivity
  change Min.min ((MonotoneHeightGraph.ray p px py).coordinate (z.re + z.im))
    ((MonotoneHeightGraph.ray q qx qy).coordinate (z.re + z.im)) ≤ z.re ∧
      z.re ≤ Max.max ((MonotoneHeightGraph.ray p px py).coordinate (z.re + z.im))
        ((MonotoneHeightGraph.ray q qx qy).coordinate (z.re + z.im))
  simp only [MonotoneHeightGraph.ray_coordinate]
  change Min.min (a * (z.re + z.im)) (b * (z.re + z.im)) ≤ z.re ∧
    z.re ≤ Max.max (a * (z.re + z.im)) (b * (z.re + z.im))
  have lower_bound (c : ℝ) (first : c * (p.re + p.im) ≤ p.re)
      (last : c * (q.re + q.im) ≤ q.re) : c * (z.re + z.im) ≤ z.re := by
    calc
      _ = r * (c * (p.re + p.im)) + s * (c * (q.re + q.im)) := by
        rw [real, imaginary]
        ring
      _ ≤ r * p.re + s * q.re := add_le_add
        (mul_le_mul_of_nonneg_left first rnonnegative)
        (mul_le_mul_of_nonneg_left last snonnegative)
      _ = z.re := real.symm
  have upper_bound (c : ℝ) (first : p.re ≤ c * (p.re + p.im))
      (last : q.re ≤ c * (q.re + q.im)) : z.re ≤ c * (z.re + z.im) := by
    calc
      _ = r * p.re + s * q.re := real
      _ ≤ r * (c * (p.re + p.im)) + s * (c * (q.re + q.im)) := add_le_add
        (mul_le_mul_of_nonneg_left first rnonnegative)
        (mul_le_mul_of_nonneg_left last snonnegative)
      _ = c * (z.re + z.im) := by rw [real, imaginary]; ring
  rcases le_total a b with ordered | ordered
  · have qbound := mul_le_mul_of_nonneg_right ordered qheight.le
    have pbound := mul_le_mul_of_nonneg_right ordered pheight.le
    rw [min_eq_left (mul_le_mul_of_nonneg_right ordered nonnegative),
      max_eq_right (mul_le_mul_of_nonneg_right ordered nonnegative)]
    exact ⟨lower_bound a a_eq.le (qbound.trans_eq b_eq),
      upper_bound b (a_eq.symm.trans_le pbound) b_eq.ge⟩
  · have qbound := mul_le_mul_of_nonneg_right ordered qheight.le
    have pbound := mul_le_mul_of_nonneg_right ordered pheight.le
    rw [min_eq_right (mul_le_mul_of_nonneg_right ordered nonnegative),
      max_eq_left (mul_le_mul_of_nonneg_right ordered nonnegative)]
    exact ⟨lower_bound b (pbound.trans_eq a_eq) b_eq.le,
      upper_bound a a_eq.ge (b_eq.symm.trans_le qbound)⟩

end MonotoneStrip
end Unfoldings
