module

public import Mathlib.Data.Set.Function

/-! Pointwise identifications transport entire carriers without unfolding concrete maps. -/

@[expose] public section

namespace Unfoldings

/-- A pointwise map identification preserves the exact whole carrier. -/
theorem image_range_eq_of_pointwise {A X Y : Type*} (f : X → Y) (g : A → X) (h : A → Y)
    (same : ∀ a, f (g a) = h a) : f '' Set.range g = Set.range h := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (same a).symm⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨g a, ⟨a, rfl⟩, same a⟩

end Unfoldings
