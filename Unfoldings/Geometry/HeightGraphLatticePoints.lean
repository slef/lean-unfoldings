module

public import Unfoldings.Geometry.MonotoneHeightGraph

/-! A point of a height-graph envelope is on one of its actual defining graphs. -/

@[expose] public section

namespace Unfoldings.MonotoneHeightGraph

variable (G H : MonotoneHeightGraph)

theorem min_point_eq_or (h : ℝ) :
    (G.min H).point h = G.point h ∨ (G.min H).point h = H.point h := by
  rcases le_total (G.coordinate h) (H.coordinate h) with ordered | ordered
  · left
    apply Complex.ext <;> simp only [point, min, min_eq_left ordered]
  · right
    apply Complex.ext <;> simp only [point, min, min_eq_right ordered]

theorem max_point_eq_or (h : ℝ) :
    (G.max H).point h = G.point h ∨ (G.max H).point h = H.point h := by
  rcases le_total (G.coordinate h) (H.coordinate h) with ordered | ordered
  · right
    apply Complex.ext <;> simp only [point, max, max_eq_right ordered]
  · left
    apply Complex.ext <;> simp only [point, max, max_eq_left ordered]

end Unfoldings.MonotoneHeightGraph
