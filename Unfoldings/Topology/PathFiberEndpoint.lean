module

public import Mathlib.Topology.Path
public import Unfoldings.Topology.ImageRange

/-! Unique fibers identify a lifted path's actual endpoint without changing its carrier. -/

@[expose] public section

namespace Unfoldings

/-- A unique endpoint fiber fixes the lift's endpoint while retaining every original point. -/
theorem exists_path_to_of_unique_fiber {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) {a b : Y} (original : Path a b) {x y : X} (lifted : Path x y)
    (same : ∀ u, f (lifted u) = original u) (j : X) (endpoint : f j = b)
    (unique : ∀ z, f z = f j → z = j) :
    ∃ P : Path x j, (∀ u, f (P u) = original u) ∧ f '' Set.range P = Set.range original := by
  have at_end : y = j := unique y
    ((congrArg f lifted.target).symm.trans ((same 1).trans (original.target.trans endpoint.symm)))
  let P := lifted.cast rfl at_end.symm
  refine ⟨P, same, ?_⟩
  exact image_range_eq_of_pointwise f P original same

/-- Join two paths at an equality of their actual endpoint copies, preserving both carriers. -/
theorem exists_path_joining_copy {X : Type*} [TopologicalSpace X] {a b c d : X}
    (first : Path a b) (last : Path c d) (joined : c = b) :
    ∃ P : Path a d, Set.range P = Set.range first ∪ Set.range last := by
  refine ⟨(first.cast rfl joined).trans last, ?_⟩
  rw [Path.trans_range]
  rfl

end Unfoldings
