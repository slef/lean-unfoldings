module

public import Unfoldings.Geometry.Edge
public import Mathlib.Tactic.FinCases

/-! A genuine fine edge belongs to only one side of a fixed original triangle. -/

@[expose] public section

namespace Unfoldings.Triangle

/-- Distinct original sides cannot both contain the same entire genuine fine edge. -/
theorem edge_eq_of_common_subedge (T U : Triangle) (e f g : Fin 3)
    (first : U.edge g ⊆ T.edge e) (last : U.edge g ⊆ T.edge f) : e = f := by
  by_contra different
  have adjacent : f = next e ∨ e = next f := by
    fin_cases e <;> fin_cases f <;> simp_all [next]
  rcases adjacent with rfl | rfl
  · have left := T.eq_vertex_of_mem_edge_of_mem_next e
      (first (left_mem_segment ℝ _ _)) (last (left_mem_segment ℝ _ _))
    have right := T.eq_vertex_of_mem_edge_of_mem_next e
      (first (right_mem_segment ℝ _ _)) (last (right_mem_segment ℝ _ _))
    exact U.edge_endpoints_ne g (left.trans right.symm)
  · have left := T.eq_vertex_of_mem_edge_of_mem_next f
      (last (left_mem_segment ℝ _ _)) (first (left_mem_segment ℝ _ _))
    have right := T.eq_vertex_of_mem_edge_of_mem_next f
      (last (right_mem_segment ℝ _ _)) (first (right_mem_segment ℝ _ _))
    exact U.edge_endpoints_ne g (left.trans right.symm)

end Unfoldings.Triangle
