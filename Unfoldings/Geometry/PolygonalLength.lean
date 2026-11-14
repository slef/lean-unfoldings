module

public import Unfoldings.Geometry.PolygonalChain
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact edge sums and projected lengths of finite polygonal chains. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E]
  {n : ℕ} (P : PolygonalChain E n)

def projectedLength : ℝ := ∑ i, ‖P.edge i‖

theorem sum_edge : ∑ i, P.edge i = P.vertex (Fin.last n) - P.vertex 0 := by
  simp only [edge, Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [add_comm _ (P.vertex 0), ← Fin.sum_univ_succ P.vertex,
    Fin.sum_univ_castSucc P.vertex]
  exact add_comm _ _

theorem chord_le_projectedLength : ‖P.vertex (Fin.last n) - P.vertex 0‖ ≤ P.projectedLength := by
  rw [← P.sum_edge]
  exact norm_sum_le _ _

theorem projectedLength_nonneg : 0 ≤ P.projectedLength :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Local progress telescopes over the entire chain, with no constraint on predecessor choices. -/
theorem potential_progress (height : E → ℝ) {c : ℝ}
    (step : ∀ i, c * ‖P.edge i‖ ≤ height (P.vertex i.succ) - height (P.vertex i.castSucc)) :
    c * P.projectedLength ≤ height (P.vertex (Fin.last n)) - height (P.vertex 0) := by
  have total := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => step i)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at total
  have first := Fin.sum_univ_succ (fun i => height (P.vertex i))
  have last := Fin.sum_univ_castSucc (fun i => height (P.vertex i))
  dsimp [projectedLength]
  linarith

end Unfoldings.PolygonalChain
