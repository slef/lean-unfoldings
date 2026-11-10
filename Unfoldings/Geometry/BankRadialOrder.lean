module

public import Unfoldings.Geometry.PairedChains

/-!
# Radial order from matched coordinate increments

Up-left increment dominance implies that any two bank points are either
left-to-right ordered or bottom-to-top ordered. In a common quadrant, equal
radii then force both coordinate orders. Finite endpoints cause no gap in this
argument: no extra chain point at a chosen abscissa is assumed to exist.
-/

@[expose] public section

namespace Unfoldings

/-- On a first-quadrant circle, the two weak coordinate orders determine the same angular order. -/
theorem quadrant_circle_order {lx ly rx ry : ℝ}
    (lxnonnegative : 0 ≤ lx) (lynonnegative : 0 ≤ ly)
    (rxnonnegative : 0 ≤ rx) (rynonnegative : 0 ≤ ry)
    (radius : lx ^ 2 + ly ^ 2 = rx ^ 2 + ry ^ 2)
    (alternative : lx ≤ rx ∨ ry ≤ ly) : lx ≤ rx ∧ ry ≤ ly := by
  rcases alternative with horizontal | vertical
  · have squares := mul_self_le_mul_self lxnonnegative horizontal
    exact ⟨horizontal, by nlinarith⟩
  · have squares := mul_self_le_mul_self rynonnegative vertical
    exact ⟨by nlinarith, vertical⟩

namespace PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

theorem before_total (i j : Fin n) (t s : unitInterval) : Before i t j s ∨ Before j s i t := by
  rcases lt_trichotomy i j with ordered | rfl | ordered
  · exact Or.inl (Or.inl ordered)
  · exact (le_total t s).imp (fun h => Or.inr ⟨rfl, h⟩) (fun h => Or.inr ⟨rfl, h⟩)
  · exact Or.inr (Or.inl ordered)

variable (P : PolygonalChain E n)

theorem linear_origin_le_point (height : E →ₗ[ℝ] ℝ)
    (increments : ∀ i, 0 ≤ height (P.edge i)) (i : Fin n) (t : unitInterval) :
    height (P.vertex 0) ≤ height (P.point i t) := by
  have monotone := (P.monotone_linear_vertices_iff height).mpr increments
  have first := monotone (show (0 : Fin (n + 1)) ≤ i.castSucc from Nat.zero_le _)
  have last := monotone (show (0 : Fin (n + 1)) ≤ i.succ from Nat.zero_le _)
  rw [P.linear_point]
  nlinarith [t.property.1, t.property.2]

variable (L R : PolygonalChain E n)

/-- Whole-edge order follows from matched increments and common monotone coordinates. -/
theorem left_or_above_of_increments (horizontal vertical : E →ₗ[ℝ] ℝ)
    (start : L.vertex 0 = R.vertex 0)
    (horizontal_increments : ∀ i, horizontal (L.edge i) ≤ horizontal (R.edge i))
    (vertical_increments : ∀ i, vertical (R.edge i) ≤ vertical (L.edge i))
    (right_horizontal : ∀ i, 0 ≤ horizontal (R.edge i))
    (right_vertical : ∀ i, 0 ≤ vertical (R.edge i))
    (i j : Fin n) (t s : unitInterval) :
    horizontal (L.point i t) ≤ horizontal (R.point j s) ∨
      vertical (R.point j s) ≤ vertical (L.point i t) := by
  rcases before_total i j t s with before | before
  · left
    exact (L.linear_point_le_of_increments R horizontal (by rw [start])
      horizontal_increments i t).trans
      (R.linear_point_le horizontal
        ((R.monotone_linear_vertices_iff horizontal).mpr right_horizontal) i j t s before)
  · right
    exact (R.linear_point_le vertical
      ((R.monotone_linear_vertices_iff vertical).mpr right_vertical) j i s t before).trans
        (R.linear_point_le_of_increments L vertical (by rw [start]) vertical_increments i t)

end PolygonalChain
end Unfoldings
