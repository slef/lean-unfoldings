module

public import Unfoldings.Geometry.SharedEdgeOpening

/-! At most two triangles with pairwise disjoint interiors can share one whole edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

theorem edge_injective (T : Triangle) : Function.Injective T.edge := by
  intro e f same
  by_contra different
  obtain ⟨x, regular⟩ := T.exists_edge_nonvertex e
  exact regular (T.isVertex_of_mem_edges different x.property (same ▸ x.property))

/-- Opposite-side opening is independent of which triangle supplies the common edge coordinates. -/
theorem opposite_product_of_shared_edge (T U V : Triangle) (e f g : Fin 3)
    (first : T.edge e = U.edge f) (last : T.edge e = V.edge g)
    (separated : Disjoint (interior U.carrier) (interior V.carrier)) :
    orient (T.vertex e) (T.vertex (next e)) (U.opposite f) *
      orient (T.vertex e) (T.vertex (next e)) (V.opposite g) < 0 := by
  let height := orientMap (T.vertex e) (T.vertex (next e))
  have eval_height (x : Plane) : height x = orient (T.vertex e) (T.vertex (next e)) x :=
    orientMap_apply _ _ _
  have at_left : height (U.vertex f) = 0 := by
    rw [eval_height]
    apply orient_eq_zero_of_mem_segment
    change U.vertex f ∈ T.edge e
    rw [first]
    exact left_mem_segment ℝ _ _
  have at_right : height (U.vertex (next f)) = 0 := by
    rw [eval_height]
    apply orient_eq_zero_of_mem_segment
    change U.vertex (next f) ∈ T.edge e
    rw [first]
    exact right_mem_segment ℝ _ _
  have formula := U.affine_height_eq_coord f height at_left at_right (V.opposite g)
  have opposite := U.opposite_of_shared_edge V f g (first.symm.trans last) separated
  rw [U.orient_eq_coord_mul f (V.opposite g)] at opposite
  have coordinate_negative : U.coord (next (next f)) (V.opposite g) < 0 := by
    have positive := sq_pos_of_ne_zero (U.orient_edge_ne_zero f)
    nlinarith
  have height_ne : height (U.opposite f) ≠ 0 := by
    intro zero
    have all_zero : height = 0 := by
      apply U.affine_ext
      intro i
      rcases corner_cases f i with rfl | rfl | rfl
      · exact at_left
      · exact at_right
      · exact zero
    have nonzero := T.orient_edge_ne_zero e
    have evaluation := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A (T.opposite e)) all_zero
    exact nonzero (by simpa only [eval_height, AffineMap.coe_zero, Pi.zero_apply] using evaluation)
  rw [← eval_height (U.opposite f), ← eval_height (V.opposite g)]
  rw [formula]
  have positive := sq_pos_of_ne_zero height_ne
  have rewrite : height (U.opposite f) *
      (height (U.opposite f) * U.coord (next (next f)) (V.opposite g)) =
      height (U.opposite f) ^ 2 * U.coord (next (next f)) (V.opposite g) := by ring
  rw [rewrite]
  exact mul_neg_of_pos_of_neg positive coordinate_negative

/-- Three pairwise disjoint interiors cannot all share the same nondegenerate edge carrier. -/
theorem not_three_shared_edges (T U V : Triangle) (e f g : Fin 3)
    (first : T.edge e = U.edge f) (last : T.edge e = V.edge g)
    (TU : Disjoint (interior T.carrier) (interior U.carrier))
    (TV : Disjoint (interior T.carrier) (interior V.carrier))
    (UV : Disjoint (interior U.carrier) (interior V.carrier)) : False := by
  have ab := T.opposite_of_shared_edge U e f first TU
  have ac := T.opposite_of_shared_edge V e g last TV
  have bc := T.opposite_product_of_shared_edge U V e f g first last UV
  rcases mul_neg_iff.mp ab with ⟨a_pos, b_neg⟩ | ⟨a_neg, b_pos⟩
  · have c_neg : orient (T.vertex e) (T.vertex (next e)) (V.opposite g) < 0 := by
      rcases mul_neg_iff.mp ac with ⟨_, negative⟩ | ⟨negative, _⟩
      · exact negative
      · linarith
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos b_neg.le c_neg.le)) bc
  · have c_pos : 0 < orient (T.vertex e) (T.vertex (next e)) (V.opposite g) := by
      rcases mul_neg_iff.mp ac with ⟨positive, _⟩ | ⟨_, positive⟩
      · linarith
      · exact positive
    exact (not_lt_of_ge (mul_nonneg b_pos.le c_pos.le)) bc

end Unfoldings.Triangle
