module

public import Unfoldings.Geometry.PolygonalChain

/-! Radial distance comparisons across different closed edges of a polygonal chain. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- Ordered positions include the shared endpoint of consecutive edges. -/
def Before (i : Fin n) (t : unitInterval) (k : Fin n) (s : unitInterval) : Prop :=
  i < k ∨ (i = k ∧ t ≤ s)

theorem RadiallyMonotone.dist_vertices_le (radial : P.RadiallyMonotone)
    (j a b : Fin (n + 1)) (earlier : j ≤ a) (ordered : a ≤ b) :
    dist (P.vertex j) (P.vertex a) ≤ dist (P.vertex j) (P.vertex b) := by
  have monotone : Monotone (fun k : Fin (n + 1) => dist (P.vertex j) (P.vertex (max j k))) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    by_cases previous : j ≤ k.castSucc
    · rw [max_eq_right previous, max_eq_right (previous.trans (Fin.castSucc_le_succ k))]
      have bound := radial j k previous (show (0 : unitInterval) ≤ 1 from zero_le_one)
      simpa only [point_zero, point_one] using bound
    · rw [max_eq_left (le_of_not_ge previous)]
      simp only [dist_self]
      exact dist_nonneg
  simpa only [max_eq_right earlier, max_eq_right (earlier.trans ordered)] using monotone ordered

/-- Whole-edge monotonicity composes across all intervening vertices. -/
theorem RadiallyMonotone.dist_point_le (radial : P.RadiallyMonotone)
    (j : Fin (n + 1)) (i k : Fin n) (t s : unitInterval)
    (earlier : j.val ≤ i.val) (ordered : Before i t k s) :
    dist (P.vertex j) (P.point i t) ≤ dist (P.vertex j) (P.point k s) := by
  rcases ordered with different | ⟨rfl, parameters⟩
  · have previous : j.val ≤ k.val := earlier.trans (le_of_lt different)
    have first := radial j i earlier (show t ≤ (1 : unitInterval) from t.property.2)
    have last := radial j k previous (show (0 : unitInterval) ≤ s from s.property.1)
    have middle := RadiallyMonotone.dist_vertices_le P radial j i.succ k.castSucc
      (by change j.val ≤ i.val + 1; omega) (by change i.val + 1 ≤ k.val; omega)
    simp only [point_one, point_zero] at first last
    exact first.trans (middle.trans last)
  · exact radial j i earlier parameters

end Unfoldings.PolygonalChain
