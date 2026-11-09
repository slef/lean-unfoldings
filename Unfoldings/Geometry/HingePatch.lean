module

public import Unfoldings.Geometry.Placement
public import Unfoldings.Geometry.EdgeSides

/-! The two sides of an outward hinge fill a planar neighborhood of an edge-interior point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.HingePlacement

variable {T U : Triangle} {e f : Fin 3} {identify : T.Edge e ≃ᵢ U.Edge f}
  (H : HingePlacement T U e f identify)

theorem inverse_joined (x : T.Edge e) : H.place.symm x.val = (identify x).val := by
  apply H.place.injective
  exact (H.place.apply_symm_apply x.val).trans (H.joined x).symm

/-- The right supporting coordinate transported into the common unfolded plane. -/
def rightCoord : Plane →ᵃ[ℝ] ℝ :=
  (U.coord (Triangle.next (Triangle.next f))).comp H.place.symm.toAffineEquiv.toAffineMap

@[simp] theorem rightCoord_apply (x : Plane) :
    H.rightCoord x = U.coord (Triangle.next (Triangle.next f)) (H.place.symm x) := rfl

theorem rightCoord_edge (x : T.Edge e) : H.rightCoord x.val = 0 := by
  rw [rightCoord_apply, H.inverse_joined]
  exact U.coord_edge_eq_zero f (identify x)

theorem rightCoord_eq (x : Plane) :
    H.rightCoord x = H.rightCoord (T.opposite e) * T.coord (Triangle.next (Triangle.next e)) x :=
  T.affine_height_eq_coord e H.rightCoord
    (H.rightCoord_edge ⟨_, left_mem_segment ℝ _ _⟩)
    (H.rightCoord_edge ⟨_, right_mem_segment ℝ _ _⟩) x

/-- Strict opening makes the two supporting half-plane coordinates point in opposite directions. -/
theorem rightCoord_opposite_neg : H.rightCoord (T.opposite e) < 0 := by
  let q := H.place (U.opposite f)
  have left_negative : T.coord (Triangle.next (Triangle.next e)) q < 0 := by
    have opening := H.opposite
    have formula := T.orient_eq_coord_mul e q
    rw [formula, ← mul_assoc] at opening
    by_contra nonnegative
    exact (not_lt_of_ge (mul_nonneg (mul_self_nonneg _)
      (le_of_not_gt nonnegative))) opening
  have right_one : H.rightCoord q = 1 := by
    change U.coord (Triangle.next (Triangle.next f)) (H.place.symm (H.place (U.opposite f))) = 1
    rw [H.place.symm_apply_apply]
    simp [Triangle.opposite]
  have product : 0 < H.rightCoord (T.opposite e) * T.coord (Triangle.next (Triangle.next e)) q := by
    rw [← H.rightCoord_eq, right_one]
    exact zero_lt_one
  rcases mul_pos_iff.mp product with positive | negative
  · exact ((not_lt_of_ge left_negative.le) positive.2).elim
  · exact negative.1

theorem rightCoord_nonneg_of_mem_image {x : Plane} (inside : x ∈ H.place '' U.carrier) :
    0 ≤ H.rightCoord x := by
  obtain ⟨y, hy, rfl⟩ := inside
  rw [rightCoord_apply, H.place.symm_apply_apply]
  exact (U.carrier_eq_nonneg_coord.le hy) _

/-- The closed developed triangles intersect in exactly their declared common edge. -/
theorem inter_eq_edge : T.carrier ∩ H.place '' U.carrier = T.edge e := by
  ext x
  constructor
  · rintro ⟨left, right⟩
    have nonnegative := (T.carrier_eq_nonneg_coord.le left) (Triangle.next (Triangle.next e))
    have other := H.rightCoord_nonneg_of_mem_image right
    rw [H.rightCoord_eq] at other
    have nonpositive : T.coord (Triangle.next (Triangle.next e)) x ≤ 0 := by
      by_contra positive
      exact (not_lt_of_ge other)
        (mul_neg_of_neg_of_pos H.rightCoord_opposite_neg (lt_of_not_ge positive))
    exact (T.mem_edge_iff e x).mpr ⟨left, le_antisymm nonpositive nonnegative⟩
  · intro edge
    refine ⟨T.edge_subset e edge, ?_⟩
    exact ⟨(identify ⟨x, edge⟩).val, U.edge_subset f (identify ⟨x, edge⟩).property,
      H.joined ⟨x, edge⟩⟩

theorem image_edge_eq : H.place '' U.edge f = T.edge e := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have back := identify.apply_symm_apply (⟨y, hy⟩ : U.Edge f)
    have mapped := congrArg (fun p : U.Edge f => H.place p.val) back
    have equal : H.place y = (identify.symm ⟨y, hy⟩).val :=
      mapped.symm.trans (H.joined (identify.symm ⟨y, hy⟩))
    rw [equal]
    exact (identify.symm ⟨y, hy⟩).property
  · intro hz
    exact ⟨(identify ⟨z, hz⟩).val, (identify ⟨z, hz⟩).property, H.joined ⟨z, hz⟩⟩

theorem mem_edge_of_mem_right_of_coord_zero {z : Plane} (inside : z ∈ H.place '' U.carrier)
    (zero : T.coord (Triangle.next (Triangle.next e)) z = 0) : z ∈ T.edge e := by
  obtain ⟨y, hy, equal⟩ := inside
  have other_zero : H.rightCoord z = 0 := by rw [H.rightCoord_eq, zero, mul_zero]
  rw [← equal, rightCoord_apply, H.place.symm_apply_apply] at other_zero
  have edge : y ∈ U.edge f := (U.mem_edge_iff f y).mpr ⟨hy, other_zero⟩
  exact H.image_edge_eq.le ⟨y, edge, equal⟩

/-- A chord joining the two faces inside a covered ball crosses their actual common edge. -/
theorem exists_edge_on_chord {center p q : Plane} {r : ℝ}
    (cover : Metric.ball center r ⊆ T.carrier ∪ H.place '' U.carrier)
    (left : p ∈ T.carrier) (right : q ∈ H.place '' U.carrier)
    (near_left : p ∈ Metric.ball center r) (near_right : q ∈ Metric.ball center r) :
    ∃ z : T.Edge e, z.val ∈ segment ℝ p q := by
  have nonnegative := (T.carrier_eq_nonneg_coord.le left) (Triangle.next (Triangle.next e))
  have other := H.rightCoord_nonneg_of_mem_image right
  rw [H.rightCoord_eq] at other
  have nonpositive : T.coord (Triangle.next (Triangle.next e)) q ≤ 0 := by
    by_contra positive
    exact (not_lt_of_ge other)
      (mul_neg_of_neg_of_pos H.rightCoord_opposite_neg (lt_of_not_ge positive))
  obtain ⟨z, between, zero⟩ := exists_mem_segment_zero
    (T.coord (Triangle.next (Triangle.next e))) p q nonnegative nonpositive
  have near : z ∈ Metric.ball center r :=
    (convex_ball center r).segment_subset near_left near_right between
  have edge : z ∈ T.edge e := by
    rcases cover near with left | right
    · exact (T.mem_edge_iff e z).mpr ⟨left, zero⟩
    · exact H.mem_edge_of_mem_right_of_coord_zero right zero
  exact ⟨⟨z, edge⟩, between⟩

/-- Around an edge-interior point, the two developed faces contain a whole Euclidean ball. -/
theorem exists_ball_cover (x : T.Edge e) (regular : ¬ T.IsVertex x) :
    ∃ r > 0, Metric.ball x.val r ⊆ T.carrier ∪ H.place '' U.carrier := by
  obtain ⟨l, lpos, left_halfplane⟩ := T.exists_ball_halfplane_edge e x regular
  have regular' : ¬ U.IsVertex (identify x) := fun h =>
    regular ((T.edge_isometry_isVertex_iff U e f identify x).mp h)
  obtain ⟨r, rpos, right_halfplane⟩ := U.exists_ball_halfplane_edge f (identify x) regular'
  refine ⟨min l r, lt_min lpos rpos, ?_⟩
  intro p hp
  have near_left := Metric.ball_subset_ball (min_le_left l r) hp
  have near_right : H.place.symm p ∈ Metric.ball (identify x).val r := by
    apply Metric.mem_ball.mpr
    rw [← H.inverse_joined x, H.place.symm.isometry.dist_eq]
    exact (Metric.mem_ball.mp hp).trans_le (min_le_right l r)
  by_cases side : 0 ≤ T.coord (Triangle.next (Triangle.next e)) p
  · exact Or.inl ((left_halfplane p near_left).mpr side)
  · apply Or.inr
    have other_side : 0 ≤ H.rightCoord p := by
      rw [H.rightCoord_eq]
      exact mul_nonneg_of_nonpos_of_nonpos H.rightCoord_opposite_neg.le (le_of_not_ge side)
    exact ⟨H.place.symm p, (right_halfplane _ near_right).mpr other_side,
      H.place.apply_symm_apply p⟩

end Unfoldings.HingePlacement
