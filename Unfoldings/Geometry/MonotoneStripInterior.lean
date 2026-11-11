module

public import Unfoldings.Geometry.MonotoneStripPaths

/-! Strictly internal monotone connectors for inserting a leaf into an existing strip. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace MonotoneHeightGraph

def average (G H : MonotoneHeightGraph) : MonotoneHeightGraph where
  coordinate h := (G.coordinate h + H.coordinate h) / 2
  coordinate_mono := by
    intro a b ordered
    exact div_le_div_of_nonneg_right
      (add_le_add (G.coordinate_mono ordered) (H.coordinate_mono ordered)) (by positivity)
  complement_mono := by
    intro a b ordered
    have first := G.complement_mono ordered
    have last := H.complement_mono ordered
    dsimp only at first last ⊢
    linarith

end MonotoneHeightGraph

namespace MonotoneStrip

variable (S : MonotoneStrip)

/-- Average the leftmost and rightmost feasible monotone connectors to the target.
Unlike clamping a single connector, this keeps positive-height points strictly inside. -/
def interiorConnector (p : ℂ) : MonotoneHeightGraph :=
  (S.lower.max (MonotoneHeightGraph.horizontal p.im)).average
    (S.upper.min (MonotoneHeightGraph.constant p.re))

theorem interiorConnector_source {p : ℂ}
    (lower_source : S.lower.coordinate 0 = 0) (upper_source : S.upper.coordinate 0 = 0)
    (horizontal : 0 ≤ p.re) (vertical : 0 ≤ p.im) :
    (S.interiorConnector p).coordinate 0 = 0 := by
  change (Max.max (S.lower.coordinate 0) (0 - p.im) +
    Min.min (S.upper.coordinate 0) p.re) / 2 = 0
  rw [lower_source, upper_source, max_eq_left (by linarith), min_eq_left horizontal]
  norm_num

theorem interiorConnector_target {p : ℂ} (member : p ∈ S.carrier) :
    (S.interiorConnector p).coordinate (p.re + p.im) = p.re := by
  change (Max.max (S.lower.coordinate (p.re + p.im)) (p.re + p.im - p.im) +
    Min.min (S.upper.coordinate (p.re + p.im)) p.re) / 2 = p.re
  rw [add_sub_cancel_right, max_eq_right member.1, min_eq_right member.2]
  ring

theorem interiorConnector_bounds {p : ℂ} (member : p ∈ S.carrier) {h : ℝ}
    (before : h ≤ p.re + p.im) :
    S.lower.coordinate h ≤ (S.interiorConnector p).coordinate h ∧
      (S.interiorConnector p).coordinate h ≤ S.upper.coordinate h := by
  have low : S.lower.coordinate h ≤ p.re := (S.lower.coordinate_mono before).trans member.1
  have high : h - p.im ≤ S.upper.coordinate h := by
    have bound : h - S.upper.coordinate h ≤
        p.re + p.im - S.upper.coordinate (p.re + p.im) := S.upper.complement_mono before
    linarith [member.2]
  have left_low := le_max_left (S.lower.coordinate h) (h - p.im)
  have left_high := max_le (S.ordered h) high
  have right_low := le_min (S.ordered h) low
  have right_high := min_le_left (S.upper.coordinate h) p.re
  change S.lower.coordinate h ≤
    (Max.max (S.lower.coordinate h) (h - p.im) + Min.min (S.upper.coordinate h) p.re) / 2 ∧ _
  constructor
  · linarith
  · change (Max.max (S.lower.coordinate h) (h - p.im) +
      Min.min (S.upper.coordinate h) p.re) / 2 ≤ S.upper.coordinate h
    linarith

/-- No displacement from the target is needed: the average is strict everywhere the strip
has positive width, provided the target is strictly between its existing boundaries. -/
theorem interiorConnector_strict {p : ℂ}
    (lower_target : S.lower.coordinate (p.re + p.im) < p.re)
    (upper_target : p.re < S.upper.coordinate (p.re + p.im)) {h : ℝ}
    (before : h ≤ p.re + p.im) (width : S.lower.coordinate h < S.upper.coordinate h) :
    S.lower.coordinate h < (S.interiorConnector p).coordinate h ∧
      (S.interiorConnector p).coordinate h < S.upper.coordinate h := by
  have low : S.lower.coordinate h < p.re :=
    (S.lower.coordinate_mono before).trans_lt lower_target
  have high : h - p.im < S.upper.coordinate h := by
    have bound : h - S.upper.coordinate h ≤
        p.re + p.im - S.upper.coordinate (p.re + p.im) := S.upper.complement_mono before
    linarith
  have left_low := le_max_left (S.lower.coordinate h) (h - p.im)
  have left_high := max_lt width high
  have right_low := lt_min width low
  have right_high := min_le_left (S.upper.coordinate h) p.re
  change S.lower.coordinate h <
    (Max.max (S.lower.coordinate h) (h - p.im) + Min.min (S.upper.coordinate h) p.re) / 2 ∧ _
  constructor
  · linarith
  · change (Max.max (S.lower.coordinate h) (h - p.im) +
      Min.min (S.upper.coordinate h) p.re) / 2 < S.upper.coordinate h
    linarith

end MonotoneStrip
end Unfoldings
