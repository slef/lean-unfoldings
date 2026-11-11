module

public import Unfoldings.Geometry.BankRadialOrder

/-! Whole-bank order using coordinate progress that permits oppositely directed branch jumps. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (L R : PolygonalChain E n)

/-- Only the right bank's horizontal coordinate and the left bank's vertical coordinate must
increase. Thus outward edges can be interleaved with up-left jumps on the left bank and
down-right jumps on the right bank; neither bank needs two increasing coordinates. -/
theorem left_or_above_of_matched_order (horizontal vertical : E →ₗ[ℝ] ℝ)
    (matched_horizontal : ∀ i t, horizontal (L.point i t) ≤ horizontal (R.point i t))
    (matched_vertical : ∀ i t, vertical (R.point i t) ≤ vertical (L.point i t))
    (right_horizontal : ∀ i, 0 ≤ horizontal (R.edge i))
    (left_vertical : ∀ i, 0 ≤ vertical (L.edge i))
    (i j : Fin n) (t s : unitInterval) :
    horizontal (L.point i t) ≤ horizontal (R.point j s) ∨
      vertical (R.point j s) ≤ vertical (L.point i t) := by
  rcases before_total i j t s with before | before
  · exact Or.inl ((matched_horizontal i t).trans
      (R.linear_point_le horizontal ((R.monotone_linear_vertices_iff horizontal).mpr
        right_horizontal) i j t s before))
  · exact Or.inr ((matched_vertical j s).trans
      (L.linear_point_le vertical ((L.monotone_linear_vertices_iff vertical).mpr
        left_vertical) j i s t before))

/-- An unmatched contact already gives a matched contact if the two controlling coordinates
are injective on the corresponding bank images. The formulation allows collapsed flat jumps. -/
theorem matched_contact_of_contact (horizontal vertical : E →ₗ[ℝ] ℝ)
    (matched_horizontal : ∀ i t, horizontal (L.point i t) ≤ horizontal (R.point i t))
    (matched_vertical : ∀ i t, vertical (R.point i t) ≤ vertical (L.point i t))
    (right_horizontal : ∀ i, 0 ≤ horizontal (R.edge i))
    (left_vertical : ∀ i, 0 ≤ vertical (L.edge i))
    (right_injective : ∀ i j t s, horizontal (R.point i t) = horizontal (R.point j s) →
      R.point i t = R.point j s)
    (left_injective : ∀ i j t s, vertical (L.point i t) = vertical (L.point j s) →
      L.point i t = L.point j s)
    (i j : Fin n) (t s : unitInterval) (same : L.point i t = R.point j s) :
    L.point i t = R.point i t ∨ L.point j s = R.point j s := by
  rcases before_total i j t s with before | before
  · have bound := R.linear_point_le horizontal
      ((R.monotone_linear_vertices_iff horizontal).mpr right_horizontal) i j t s before
    have equal : horizontal (R.point i t) = horizontal (R.point j s) := by
      have matched := matched_horizontal i t
      rw [same] at matched
      exact le_antisymm bound matched
    exact Or.inl (same.trans (right_injective i j t s equal).symm)
  · have bound := L.linear_point_le vertical
      ((L.monotone_linear_vertices_iff vertical).mpr left_vertical) j i s t before
    have equal : vertical (L.point j s) = vertical (L.point i t) := by
      have matched := matched_vertical j s
      rw [← same] at matched
      exact le_antisymm bound matched
    exact Or.inr ((left_injective j i s t equal).trans same)

end Unfoldings.PolygonalChain
