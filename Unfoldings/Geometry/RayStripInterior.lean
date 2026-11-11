module

public import Unfoldings.Geometry.RayStrip
public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Unfoldings.Geometry.CyclicRays

/-! A forward strict strip between positive rays is the genuine open cone between those rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

private theorem strict_cone_of_slope_bounds (p q z : ℂ)
    (px : 0 < p.re) (py : 0 < p.im) (qx : 0 < q.re) (qy : 0 < q.im)
    (ordered : p.re / (p.re + p.im) < q.re / (q.re + q.im))
    (lower : p.re / (p.re + p.im) * (z.re + z.im) < z.re)
    (upper : z.re < q.re / (q.re + q.im) * (z.re + z.im)) :
    z ∈ strictRayCone p q := by
  let D := p.re * q.im - p.im * q.re
  have ph := add_pos px py
  have qh := add_pos qx qy
  have negative : D < 0 := by
    have cross := (div_lt_div_iff₀ ph qh).mp ordered
    dsimp only [D]
    nlinarith
  have lower' : p.re * (z.re + z.im) / (p.re + p.im) < z.re := by
    simpa only [div_mul_eq_mul_div] using lower
  have upper' : z.re < q.re * (z.re + z.im) / (q.re + q.im) := by
    simpa only [div_mul_eq_mul_div] using upper
  have pbound := (div_lt_iff₀ ph).mp lower'
  have qbound := (lt_div_iff₀ qh).mp upper'
  let r := (z.re * q.im - z.im * q.re) / D
  let s := (p.re * z.im - p.im * z.re) / D
  have rpositive : 0 < r := div_pos_of_neg_of_neg (by nlinarith) negative
  have spositive : 0 < s := div_pos_of_neg_of_neg (by nlinarith) negative
  refine ⟨r, rpositive, s, spositive, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    dsimp only [r, s]
    field_simp [negative.ne]
    dsimp only [D]
    ring
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    dsimp only [r, s]
    field_simp [negative.ne]
    dsimp only [D]
    ring

theorem rayStrip_strict_subset_cone (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) {z : ℂ}
    (forward : 0 ≤ z.re + z.im) (inside : z ∈ (rayStrip p q px py qx qy).strictCarrier) :
    z ∈ strictRayCone p q := by
  change Min.min ((MonotoneHeightGraph.ray p px py).coordinate (z.re + z.im))
    ((MonotoneHeightGraph.ray q qx qy).coordinate (z.re + z.im)) < z.re ∧
      z.re < Max.max ((MonotoneHeightGraph.ray p px py).coordinate (z.re + z.im))
        ((MonotoneHeightGraph.ray q qx qy).coordinate (z.re + z.im)) at inside
  simp only [MonotoneHeightGraph.ray_coordinate] at inside
  rcases lt_trichotomy (p.re / (p.re + p.im)) (q.re / (q.re + q.im)) with ordered | same | ordered
  · have bound := mul_le_mul_of_nonneg_right ordered.le forward
    rw [min_eq_left bound, max_eq_right bound] at inside
    exact strict_cone_of_slope_bounds p q z px py qx qy ordered inside.1 inside.2
  · rw [same, min_self, max_self] at inside
    exact (inside.1.trans inside.2).false.elim
  · have bound := mul_le_mul_of_nonneg_right ordered.le forward
    rw [min_eq_right bound, max_eq_left bound] at inside
    obtain ⟨r, hr, s, hs, equal⟩ :=
      strict_cone_of_slope_bounds q p z qx qy px py ordered inside.1 inside.2
    exact ⟨s, hs, r, hr, by rw [equal, add_comm]⟩

end Unfoldings.MonotoneStrip
