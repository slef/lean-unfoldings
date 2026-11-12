module

public import Unfoldings.Geometry.MonotoneStripSubdivision
public import Mathlib.Data.List.Chain

/-! The actual ordered subdivision cells form one continuous chain of physical walls. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

theorem cells_head_lower : P.cells.head?.map MonotoneStrip.lower = some S.lower := by
  induction P with
  | leaf S => rfl
  | split G bounds left right first _ =>
    simp only [cells, List.head?_append, Option.map_or, first, Option.some_or]
    rfl

theorem cells_last_upper : P.cells.getLast?.map MonotoneStrip.upper = some S.upper := by
  induction P with
  | leaf S => rfl
  | split G bounds left right _ last =>
    simp only [cells, List.getLast?_append, Option.map_or, last, Option.some_or]
    rfl

theorem cells_ne_nil : P.cells ≠ [] := by
  intro empty
  have first := P.cells_head_lower
  simp only [empty, List.head?_nil, Option.map_none, reduceCtorEq] at first

/-- Repeated or zero-width cells are retained, with their actual shared wall. -/
theorem cells_chain : P.cells.IsChain (fun A B => A.upper = B.lower) := by
  induction P with
  | leaf S => exact List.isChain_singleton _
  | split G bounds left right first last =>
    apply List.isChain_append.mpr
    refine ⟨first, last, ?_⟩
    intro A at_end B at_start
    have upper := left.cells_last_upper
    have lower := right.cells_head_lower
    rw [Option.mem_def.mp at_end] at upper
    rw [Option.mem_def.mp at_start] at lower
    exact (Option.some.inj upper).trans (Option.some.inj lower).symm

theorem adjacent_cell_walls (j : ℕ) (next : j + 1 < P.cells.length) :
    (P.cells[j]'(by omega)).upper = P.cells[j + 1].lower :=
  List.isChain_iff_getElem.mp P.cells_chain j next

end Unfoldings.MonotoneStrip.Subdivision
