module

public import Unfoldings.Metric.Quotient

/-!
# Localizing route estimates

A map on tagged cell points need only be nonexpanding on steps near a fixed
metric center. Short routes remain in that neighborhood. Comparing with such
routes gives a local distance bound without assuming a global development.
-/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

universe u v

variable {ι : Type u} (E : ι → Type v) [∀ i, PseudoEMetricSpace (E i)]
  {Y : Type*} [PseudoEMetricSpace Y]

theorem map_edist_le_length_of_short_route (glue : Total E → Total E → Prop)
    (f : Total E → Y) (center : Realization E glue) (r : ℝ≥0∞)
    (local_step : ∀ a b, edist center (point E glue a) < r →
      edist center (point E glue b) < r → edist (f a) (f b) ≤ stepCost E glue a b)
    {a b : Total E} (route : Route (Total E) a b)
    (short : edist center (point E glue a) + route.length (stepCost E glue) < r) :
    edist (f a) (f b) ≤ route.length (stepCost E glue) := by
  induction route with
  | nil a => simp [Route.length]
  | cons a b tail ih =>
    have step : edist (point E glue a) (point E glue b) ≤ stepCost E glue a b :=
      Route.distance_le_cost _ _ _
    have next : edist center (point E glue b) ≤
        edist center (point E glue a) + stepCost E glue a b :=
      (edist_triangle center (point E glue a) (point E glue b)).trans (add_le_add le_rfl step)
    have tail_short : edist center (point E glue b) + tail.length (stepCost E glue) < r :=
      (add_le_add next le_rfl).trans_lt (by simpa only [Route.length, add_assoc] using short)
    have first_inside : edist center (point E glue a) < r :=
      (le_add_of_nonneg_right bot_le).trans_lt short
    have next_inside : edist center (point E glue b) < r :=
      (le_add_of_nonneg_right bot_le).trans_lt tail_short
    exact (edist_triangle (f a) (f b) _).trans
      (add_le_add (local_step a b first_inside next_inside) (ih tail_short))

/-- A local step estimate bounds metric distance when the endpoints fit in the radius budget. -/
theorem map_edist_le_edist_of_budget (glue : Total E → Total E → Prop)
    (f : Total E → Y) (center : Realization E glue) (r : ℝ≥0∞)
    (local_step : ∀ a b, edist center (point E glue a) < r →
      edist center (point E glue b) < r → edist (f a) (f b) ≤ stepCost E glue a b)
    (a b : Total E) (budget : edist center (point E glue a) + edist (f a) (f b) < r) :
    edist (f a) (f b) ≤ edist (point E glue a) (point E glue b) := by
  by_contra smaller
  have less : Route.distance (stepCost E glue) a b < edist (f a) (f b) := lt_of_not_ge smaller
  obtain ⟨route, short⟩ := iInf_lt_iff.mp less
  have fits : edist center (point E glue a) + route.length (stepCost E glue) < r :=
    (add_le_add le_rfl short.le).trans_lt budget
  exact (not_lt_of_ge
    (map_edist_le_length_of_short_route E glue f center r local_step route fits)) short

end Unfoldings.MetricGluing
