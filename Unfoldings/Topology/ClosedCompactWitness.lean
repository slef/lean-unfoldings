module

public import Mathlib.Topology.Maps.Proper.Basic

/-! Existential conditions with finitely many compact witness families are closed. -/

@[expose] public section

namespace Unfoldings

/-- Projection preserves closedness when the witness parameter space is compact.
The discrete label only needs to be finite; it requires no chosen topology. -/
theorem isClosed_exists_finite_compact
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [Finite ι]
    (R : ι → X → Y → Prop)
    (closed : ∀ i, IsClosed {p : X × Y | R i p.1 p.2}) :
    IsClosed {x | ∃ i y, R i x y} := by
  have each (i : ι) : IsClosed {x | ∃ y, R i x y} := by
    convert isClosedMap_fst_of_compactSpace _ (closed i) using 1
    ext x
    simp
  have union_closed := isClosed_iUnion_of_finite each
  convert union_closed using 1
  ext x
  simp

end Unfoldings
