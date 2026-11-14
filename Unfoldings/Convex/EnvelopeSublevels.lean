module

public import Unfoldings.Convex.SlopeEnvelope

/-! Strict sublevel control along segments, allowing one endpoint on the boundary level. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem openSegment_height_lt {level : ℝ} {x y z : Plane}
    (first : E.height x < level) (last : E.height y ≤ level)
    (member : z ∈ openSegment ℝ x y) : E.height z < level := by
  obtain ⟨a, b, ha, hb, total, rfl⟩ := member
  have upper := E.convex_height.2 (Set.mem_univ x) (Set.mem_univ y) ha.le hb.le total
  have strict := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left first ha)
    (mul_le_mul_of_nonneg_left last hb.le)
  simp only [smul_eq_mul] at upper
  calc
    E.height (a • x + b • y) ≤ a * E.height x + b * E.height y := upper
    _ < a * level + b * level := strict
    _ = level := by rw [← add_mul, total, one_mul]

theorem mem_interior_sublevel {level : ℝ} {x : Plane} (strict : E.height x < level) :
    x ∈ interior {x | E.height x ≤ level} := by
  have open_set : IsOpen {x : Plane | E.height x < level} :=
    isOpen_lt E.continuous_height continuous_const
  have inclusion : {x : Plane | E.height x < level} ⊆ {x : Plane | E.height x ≤ level} := by
    intro y hy
    change E.height y < level at hy
    change E.height y ≤ level
    exact hy.le
  apply interior_mono inclusion
  rw [open_set.interior_eq]
  exact strict

end Unfoldings.SlopeEnvelope
