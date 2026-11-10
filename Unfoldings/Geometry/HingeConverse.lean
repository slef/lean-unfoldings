module

public import Unfoldings.Geometry.TriangleMotion

/-! A joined pair has disjoint interiors exactly when it opens to opposite sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f)

/-- Disjoint interiors along a whole common edge force strict opposite-side opening. -/
theorem opposite_of_disjoint (joined : ∀ x : T.Edge e, (identify x).val = x.val)
    (disjoint : Disjoint (interior T.carrier) (interior U.carrier)) :
    orient (T.vertex e) (T.vertex (next e)) (T.opposite e) *
      orient (T.vertex e) (T.vertex (next e)) (U.opposite f) < 0 := by
  let h := U.coord (next (next f))
  have vanishes (x : T.Edge e) : h x.val = 0 := by
    rw [← joined x]
    exact U.coord_edge_eq_zero f (identify x)
  have formula (x : Plane) : h x = h (T.opposite e) * T.coord (next (next e)) x :=
    T.affine_height_eq_coord e h (vanishes ⟨_, left_mem_segment ℝ _ _⟩)
      (vanishes ⟨_, right_mem_segment ℝ _ _⟩) x
  have one : h (U.opposite f) = 1 := by simp [h, opposite]
  have nonzero : h (T.opposite e) ≠ 0 := by
    intro zero
    have contradiction := formula (U.opposite f)
    rw [one, zero, zero_mul] at contradiction
    norm_num at contradiction
  have negative : h (T.opposite e) < 0 := by
    by_contra not_negative
    have positive := lt_of_le_of_ne (le_of_not_gt not_negative) nonzero.symm
    obtain ⟨x, regular⟩ := T.exists_edge_nonvertex e
    have regular' : ¬ U.IsVertex (identify x) := fun vertex =>
      regular ((T.edge_isometry_isVertex_iff U e f identify x).mp vertex)
    have endpoints := U.coord_edge_positive f (identify x) regular'
    have open_set : IsOpen {p : Plane | 0 < U.coord f p ∧ 0 < U.coord (next f) p} :=
      (isOpen_lt continuous_const (U.continuous_coord f)).inter
        (isOpen_lt continuous_const (U.continuous_coord (next f)))
    have member : x.val ∈ {p : Plane | 0 < U.coord f p ∧ 0 < U.coord (next f) p} := by
      rw [← joined x]
      exact endpoints
    obtain ⟨r, rpos, ball⟩ := Metric.isOpen_iff.mp open_set x.val member
    have closure : x.val ∈ closure (interior T.carrier) := by
      rw [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
      exact subset_closure (T.edge_subset e x.property)
    obtain ⟨p, pin, near⟩ := Metric.mem_closure_iff.mp closure r rpos
    have close : p ∈ Metric.ball x.val r := by
      simpa only [Metric.mem_ball, dist_comm] using near
    have endpoint_positive : 0 < U.coord f p ∧ 0 < U.coord (next f) p := ball close
    have third_positive : 0 < h p := by
      rw [formula]
      exact mul_pos positive (T.interior_eq_pos_coord.le pin _)
    have other : p ∈ interior U.carrier := by
      rw [U.interior_eq_pos_coord]
      intro i
      rcases corner_cases f i with rfl | rfl | rfl
      · exact endpoint_positive.1
      · exact endpoint_positive.2
      · exact third_positive
    exact Set.disjoint_left.mp disjoint pin other
  have right_negative : T.coord (next (next e)) (U.opposite f) < 0 := by
    have product := formula (U.opposite f)
    rw [one] at product
    rcases mul_pos_iff.mp (show 0 < h (T.opposite e) *
        T.coord (next (next e)) (U.opposite f) by rw [← product]; exact zero_lt_one) with hp | hn
    · exact (not_lt_of_ge negative.le hp.1).elim
    · exact hn.2
  rw [T.orient_eq_coord_mul e (U.opposite f), ← mul_assoc]
  exact mul_neg_of_pos_of_neg (mul_self_pos.mpr (T.orient_edge_ne_zero e)) right_negative

/-- The same criterion in arbitrary rigidly placed coordinates. -/
theorem placed_opposite_of_disjoint (L R : Plane ≃ᵃⁱ[ℝ] Plane)
    (joined : ∀ x : T.Edge e, L x.val = R (identify x).val)
    (disjoint : Disjoint (interior (L '' T.carrier)) (interior (R '' U.carrier))) :
    orient (L (T.vertex e)) (L (T.vertex (next e))) (L (T.opposite e)) *
      orient (L (T.vertex e)) (L (T.vertex (next e))) (R (U.opposite f)) < 0 := by
  let pair := ((T.moveEdge L e).symm.trans identify).trans (U.moveEdge R f)
  apply (T.move L).opposite_of_disjoint (U.move R) e f pair
  · intro x
    change R (identify ((T.moveEdge L e).symm x)).val = x.val
    rw [← joined]
    exact congrArg Subtype.val ((T.moveEdge L e).apply_symm_apply x)
  · simpa only [move_carrier] using disjoint

end Unfoldings.Triangle
