module

public import Unfoldings.Geometry.MonotoneHeightGraph
public import Mathlib.Analysis.Convex.Combination

/-! Splice monotone height graphs and represent genuine monotone segments exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneHeightGraph

variable (G H : MonotoneHeightGraph)

/-- Join two coordinate-monotone graphs at a common point of a specified height. -/
def splice (height : ℝ) (joined : G.coordinate height = H.coordinate height) :
    MonotoneHeightGraph where
  coordinate h := if h ≤ height then G.coordinate h else H.coordinate h
  coordinate_mono := by
    intro a b ordered
    change (if a ≤ height then G.coordinate a else H.coordinate a) ≤
      if b ≤ height then G.coordinate b else H.coordinate b
    by_cases first : a ≤ height
    · rw [ite_eq_left first]
      by_cases last : b ≤ height
      · rw [ite_eq_left last]
        exact G.coordinate_mono ordered
      · rw [ite_eq_right last]
        exact (G.coordinate_mono first).trans
          (joined ▸ H.coordinate_mono (le_of_not_ge last))
    · rw [ite_eq_right first, ite_eq_right (fun last => first (ordered.trans last))]
      exact H.coordinate_mono ordered
  complement_mono := by
    intro a b ordered
    change a - (if a ≤ height then G.coordinate a else H.coordinate a) ≤
      b - (if b ≤ height then G.coordinate b else H.coordinate b)
    by_cases first : a ≤ height
    · rw [ite_eq_left first]
      by_cases last : b ≤ height
      · rw [ite_eq_left last]
        exact G.complement_mono ordered
      · rw [ite_eq_right last]
        have before : a - G.coordinate a ≤ height - G.coordinate height :=
          G.complement_mono first
        have after : height - H.coordinate height ≤ b - H.coordinate b :=
          H.complement_mono (le_of_not_ge last)
        rw [joined] at before
        exact before.trans after
    · rw [ite_eq_right first, ite_eq_right (fun last => first (ordered.trans last))]
      exact H.complement_mono ordered

theorem splice_coordinate_left (height : ℝ) (joined : G.coordinate height = H.coordinate height)
    {h : ℝ} (before : h ≤ height) :
    (G.splice H height joined).coordinate h = G.coordinate h := ite_eq_left before

theorem splice_coordinate_right (height : ℝ) (joined : G.coordinate height = H.coordinate height)
    {h : ℝ} (after : height ≤ h) :
    (G.splice H height joined).coordinate h = H.coordinate h := by
  by_cases same : h = height
  · subst h
    exact (ite_eq_left le_rfl).trans joined
  · exact ite_eq_right (fun before => same (le_antisymm before after))

/-- An affine graph with slope in the closed unit interval has both coordinates increasing. -/
def affine (height x slope : ℝ) (nonnegative : 0 ≤ slope) (small : slope ≤ 1) :
    MonotoneHeightGraph where
  coordinate h := x + slope * (h - height)
  coordinate_mono := by
    intro a b ordered
    have bound := mul_le_mul_of_nonneg_left ordered nonnegative
    dsimp only
    nlinarith
  complement_mono := by
    intro a b ordered
    have bound := mul_nonneg (sub_nonneg.mpr small) (sub_nonneg.mpr ordered)
    dsimp only
    nlinarith

theorem point_eq_of_coordinate (G : MonotoneHeightGraph) (z : ℂ)
    (equal : G.coordinate (z.re + z.im) = z.re) : G.point (z.re + z.im) = z := by
  apply Complex.ext
  · exact equal
  · change z.re + z.im - _ = z.im
    rw [equal]
    ring

/-- Exact affine graph through an actual segment with positive diagonal height increment. -/
def through (p q : ℂ) (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im)
    (genuine : 0 < q.re + q.im - (p.re + p.im)) : MonotoneHeightGraph :=
  affine (p.re + p.im) p.re ((q.re - p.re) / (q.re + q.im - (p.re + p.im)))
    (div_nonneg (sub_nonneg.mpr horizontal) genuine.le)
    ((div_le_one genuine).mpr (by linarith))

theorem through_lineMap (p q : ℂ) (horizontal : p.re ≤ q.re) (vertical : p.im ≤ q.im)
    (genuine : 0 < q.re + q.im - (p.re + p.im)) (t : ℝ) :
    let z := AffineMap.lineMap p q t
    (through p q horizontal vertical genuine).point (z.re + z.im) = z := by
  apply point_eq_of_coordinate
  dsimp only [through, affine, AffineMap.lineMap_apply_module']
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.sub_re, Complex.sub_im, smul_eq_mul]
  field_simp [genuine.ne']
  ring

end Unfoldings.MonotoneHeightGraph
