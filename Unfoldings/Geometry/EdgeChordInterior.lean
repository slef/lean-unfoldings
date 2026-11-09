module

public import Unfoldings.Geometry.Barycentric

/-! Chords joining interiors of different triangle edges enter the face interior. -/

@[expose] public section

namespace Unfoldings.Triangle

theorem openSegment_subset_interior_of_distinct_edges (T : Triangle)
    {e f : Fin 3} (different : e ≠ f) (x : T.Edge e) (y : T.Edge f)
    (regular_x : ¬ T.IsVertex x) (regular_y : ¬ T.IsVertex y) :
    openSegment ℝ x.val y.val ⊆ interior T.carrier := by
  have positive_x := T.coord_edge_positive e x regular_x
  have positive_y := T.coord_edge_positive f y regular_y
  have nonnegative_x : ∀ i, 0 ≤ T.coord i x := by
    have member := T.edge_subset e x.property
    rwa [T.carrier_eq_nonneg_coord] at member
  have nonnegative_y : ∀ i, 0 ≤ T.coord i y := by
    have member := T.edge_subset f y.property
    rwa [T.carrier_eq_nonneg_coord] at member
  intro z hz
  obtain ⟨t, ht, rfl⟩ := (openSegment_eq_image_lineMap ℝ x.val y.val).le hz
  rw [T.interior_eq_pos_coord]
  intro i
  have one_positive : 0 < T.coord i x ∨ 0 < T.coord i y := by
    fin_cases e <;> fin_cases f <;> fin_cases i <;> simp_all [next]
  rw [(T.coord i).apply_lineMap, AffineMap.lineMap_apply_ring]
  rcases one_positive with hx | hy
  · nlinarith [nonnegative_y i, mul_pos (sub_pos.mpr ht.2) hx,
      mul_nonneg ht.1.le (nonnegative_y i)]
  · nlinarith [nonnegative_x i, mul_pos ht.1 hy,
      mul_nonneg (sub_nonneg.mpr ht.2.le) (nonnegative_x i)]

end Unfoldings.Triangle
