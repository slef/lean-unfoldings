module

public import Unfoldings.Geometry.ChainLinear

/-!
# Ordering matched banks in common monotone coordinates

Increment inequalities are enough to compare entire banks at equal horizontal
coordinates. The proof does not infer global order merely from local opening.
-/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (L R : PolygonalChain E n)

theorem linear_point_le_of_increments (height : E →ₗ[ℝ] ℝ)
    (start : height (L.vertex 0) ≤ height (R.vertex 0))
    (increments : ∀ i, height (L.edge i) ≤ height (R.edge i))
    (i : Fin n) (t : unitInterval) : height (L.point i t) ≤ height (R.point i t) := by
  have monotone : Monotone (fun k => height (R.vertex k) - height (L.vertex k)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have bound := increments k
    simp only [edge, map_sub] at bound
    linarith
  have vertices (k : Fin (n + 1)) : height (L.vertex k) ≤ height (R.vertex k) := by
    have bound := monotone (show (0 : Fin (n + 1)) ≤ k from Nat.zero_le k.val)
    linarith
  rw [L.linear_point, R.linear_point]
  exact add_le_add (mul_le_mul_of_nonneg_left (vertices i.castSucc)
    (sub_nonneg.mpr t.property.2)) (mul_le_mul_of_nonneg_left (vertices i.succ) t.property.1)

/-- Matched up-left increments put the entire left bank above the right bank at equal abscissae. -/
theorem vertical_order_of_increments (horizontal vertical : E →ₗ[ℝ] ℝ)
    (start : L.vertex 0 = R.vertex 0)
    (horizontal_increments : ∀ i, horizontal (L.edge i) ≤ horizontal (R.edge i))
    (vertical_increments : ∀ i, vertical (R.edge i) ≤ vertical (L.edge i))
    (right_horizontal : ∀ i, 0 < horizontal (R.edge i))
    (right_vertical : ∀ i, 0 ≤ vertical (R.edge i))
    (i j : Fin n) (t s : unitInterval)
    (same_horizontal : horizontal (L.point i t) = horizontal (R.point j s)) :
    vertical (R.point j s) ≤ vertical (L.point i t) := by
  have point_x := linear_point_le_of_increments L R horizontal
    (by rw [start]) horizontal_increments i t
  have point_y := linear_point_le_of_increments R L vertical
    (by rw [start]) vertical_increments i t
  have monotone_y := (R.monotone_linear_vertices_iff vertical).mpr right_vertical
  by_cases before : Before j s i t
  · exact (R.linear_point_le vertical monotone_y j i s t before).trans point_y
  · have after : Before i t j s := by
      rcases lt_trichotomy i j with earlier | rfl | later
      · exact Or.inl earlier
      · exact Or.inr ⟨rfl, le_of_not_ge (fun parameters => before (Or.inr ⟨rfl, parameters⟩))⟩
      · exact (before (Or.inl later)).elim
    have monotone_x := (R.monotone_linear_vertices_iff horizontal).mpr
      (fun k => (right_horizontal k).le)
    have bound := R.linear_point_le horizontal monotone_x i j t s after
    have equal : horizontal (R.point i t) = horizontal (R.point j s) := by linarith
    have equal_points := R.point_eq_of_linear_eq horizontal right_horizontal i j t s after equal
    rw [← equal_points]
    exact point_y

end Unfoldings.PolygonalChain
