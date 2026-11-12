module

public import Unfoldings.Geometry.SubdivisionNonemptyEndpoints

/-! Either extreme physical cell retains its actual enclosing bank contact. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

variable {S : MonotoneStrip} (P : Subdivision S)

theorem nonemptyCells_head_contact {cutoff : ℝ} (positive : 0 < cutoff)
    (first : {T : MonotoneStrip // T ∈ P.cells})
    (at_start : (P.nonemptyCells cutoff).head? = some first) :
    Set.EqOn S.lower.point first.val.lower.point (Set.Icc 0 cutoff) := by
  have nonempty : P.nonemptyCells cutoff ≠ [] := by
    intro empty
    simp only [empty, List.head?_nil, reduceCtorEq] at at_start
  exact (P.nonemptyCells_endpoint_contacts positive first
    ((P.nonemptyCells cutoff).getLast nonempty) at_start
    (List.getLast?_eq_some_getLast nonempty)).1

theorem nonemptyCells_last_contact {cutoff : ℝ} (positive : 0 < cutoff)
    (last : {T : MonotoneStrip // T ∈ P.cells})
    (at_end : (P.nonemptyCells cutoff).getLast? = some last) :
    Set.EqOn last.val.upper.point S.upper.point (Set.Icc 0 cutoff) := by
  have nonempty : P.nonemptyCells cutoff ≠ [] := by
    intro empty
    simp only [empty, List.getLast?_nil, reduceCtorEq] at at_end
  exact (P.nonemptyCells_endpoint_contacts positive ((P.nonemptyCells cutoff).head nonempty)
    last (List.head?_eq_some_head nonempty) at_end).2

end Unfoldings.MonotoneStrip.Subdivision
