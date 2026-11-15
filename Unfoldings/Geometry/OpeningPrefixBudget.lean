module

public import Unfoldings.Geometry.PolygonalRayOpening
public import Mathlib.Data.List.TakeDrop

/-! Every partial actual opening stays within the original cumulative budget. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

@[simp] theorem openingBudget_append (first last : List (Opening n)) :
    openingBudget (first ++ last) = openingBudget first + openingBudget last := by
  simp only [openingBudget, List.map_append, List.sum_append]

@[simp] theorem openingBudget_singleton (event : Opening n) :
    openingBudget [event] = |event.angle| := by simp [openingBudget]

theorem openingBudget_take_le (events : List (Opening n)) (k : ℕ) :
    openingBudget (events.take k) ≤ openingBudget events := by
  have equal : openingBudget events =
      openingBudget (events.take k) + openingBudget (events.drop k) := by
    rw [← openingBudget_append, List.take_append_drop]
  rw [equal]
  exact le_add_of_nonneg_right (openingBudget_nonneg _)

/-- The last angle may stop anywhere during the actual positive opening. -/
theorem openingBudget_take_partial_le (events : List (Opening n)) (k : Fin events.length)
    (θ : ℝ) (bounds : θ ∈ Set.Icc 0 events[k].angle) :
    openingBudget (events.take k.val ++ [⟨events[k].hinge, θ⟩]) ≤ openingBudget events := by
  have equal : events.take (k.val + 1) = events.take k.val ++ [events[k]] :=
    (List.take_concat_get' events k.val k.isLt).symm
  calc
    _ = openingBudget (events.take k.val) + |θ| := by simp
    _ ≤ openingBudget (events.take k.val) + |events[k].angle| := by
      rw [abs_of_nonneg bounds.1, abs_of_nonneg (bounds.1.trans bounds.2)]
      exact add_le_add_right bounds.2 _
    _ = openingBudget (events.take (k.val + 1)) := by
      rw [equal, openingBudget_append, openingBudget_singleton]
    _ ≤ openingBudget events := openingBudget_take_le events _

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

@[simp] theorem openings_append (first last : List (PolygonalChain.Opening n)) :
    R.openings (first ++ last) = (R.openings first).openings last := by
  exact List.foldl_append

/-- Prefix-and-partial-event data are the actual current hinge-fixed bank. -/
theorem openings_append_singleton (events : List (PolygonalChain.Opening n))
    (event : PolygonalChain.Opening n) :
    R.openings (events ++ [event]) = (R.openings events).rotateSuffix event.hinge event.angle := by
  rw [R.openings_append]
  rfl

end Unfoldings.PolygonalRay
