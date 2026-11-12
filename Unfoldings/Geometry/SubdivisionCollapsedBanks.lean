module

public import Unfoldings.Geometry.MonotoneStripSubdivision

/-! A finite subdivision cannot have every cell collapsed where its enclosing strip has width. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip.Subdivision

theorem banks_eq_of_all_cells_collapsed {S : MonotoneStrip} (P : S.Subdivision) (h : ℝ)
    (collapsed : ∀ T ∈ P.cells, T.lower.coordinate h = T.upper.coordinate h) :
    S.lower.coordinate h = S.upper.coordinate h := by
  induction P with
  | leaf S => exact collapsed S (List.mem_singleton_self _)
  | split G bounds left right first last =>
    exact (first (fun T member => collapsed T (List.mem_append_left _ member))).trans
      (last (fun T member => collapsed T (List.mem_append_right _ member)))

end Unfoldings.MonotoneStrip.Subdivision
