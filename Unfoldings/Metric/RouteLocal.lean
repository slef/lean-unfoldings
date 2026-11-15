module

public import Unfoldings.Metric.Route

/-! A radial budget keeps a short route inside the region where a map controls individual steps. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.Route

variable {X Y : Type*} [PseudoEMetricSpace Y]

/-- A nonnegative radial height controls all vertices of a sufficiently short route. -/
theorem map_edist_le_length_of_radial_budget (cost : X → X → ℝ≥0∞)
    (height : X → ℝ≥0∞) (progress : ∀ a b, height b ≤ height a + cost a b)
    (f : X → Y) (r : ℝ≥0∞)
    (local_step : ∀ a b, height a < r → height b < r → edist (f a) (f b) ≤ cost a b)
    {a b : X} (route : Route X a b) (budget : height a + route.length cost < r) :
    edist (f a) (f b) ≤ route.length cost := by
  induction route with
  | nil a => simp [length]
  | cons a b tail ih =>
    have tail_budget : height b + tail.length cost < r :=
      (add_le_add (progress a b) le_rfl).trans_lt
        (by simpa only [length, add_assoc] using budget)
    have first_inside : height a < r := (le_add_of_nonneg_right bot_le).trans_lt budget
    have next_inside : height b < r := (le_add_of_nonneg_right bot_le).trans_lt tail_budget
    exact (edist_triangle (f a) (f b) _).trans
      (add_le_add (local_step a b first_inside next_inside) (ih tail_budget))

/-- Only local step control is needed when the target distance fits in the radial budget. -/
theorem map_edist_le_distance_of_radial_budget (cost : X → X → ℝ≥0∞)
    (height : X → ℝ≥0∞) (progress : ∀ a b, height b ≤ height a + cost a b)
    (f : X → Y) (r : ℝ≥0∞)
    (local_step : ∀ a b, height a < r → height b < r → edist (f a) (f b) ≤ cost a b)
    (a b : X) (budget : height a + edist (f a) (f b) < r) :
    edist (f a) (f b) ≤ distance cost a b := by
  by_contra smaller
  obtain ⟨route, short⟩ := iInf_lt_iff.mp (lt_of_not_ge smaller)
  have fits : height a + route.length cost < r :=
    (add_le_add le_rfl short.le).trans_lt budget
  exact (not_lt_of_ge
    (map_edist_le_length_of_radial_budget cost height progress f r local_step route fits)) short

end Unfoldings.Route
