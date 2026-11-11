module

public import Unfoldings.Cap.RoofFlat
public import Unfoldings.Geometry.ConvexSegmentExit

/-! A nonflat cap has strictly positive roof height at every interior source point. -/

@[expose] public section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- One positive height makes all interior heights positive, including the chosen forest source. -/
theorem roofHeight_pos_of_mem_interior {q p : Plane}
    (_member : q ∈ K.footprint) (positive : 0 < K.roofHeight q)
    (inside : p ∈ interior K.footprint) : 0 < K.roofHeight p := by
  by_contra not_positive
  have zero : K.roofHeight p = 0 := le_antisymm (not_lt.mp not_positive)
    (K.roofHeight_nonneg_of_mem (interior_subset inside))
  obtain ⟨f, active⟩ := K.exists_roofHeight_eq_supportHeight p
  have plane_zero : K.supportHeight f p = 0 := active.symm.trans zero
  have plane_positive : 0 < K.supportHeight f q :=
    positive.trans_le (K.roofHeight_le_supportHeight q f)
  obtain ⟨t, after, member⟩ := exists_lineMap_beyond_one_mem (q := q) inside
  have nonnegative : 0 ≤ K.supportHeight f (AffineMap.lineMap q p t) :=
    (K.roofHeight_nonneg_of_mem member).trans (K.roofHeight_le_supportHeight _ f)
  rw [(K.supportHeight f).apply_lineMap, AffineMap.lineMap_apply_ring,
    plane_zero, mul_zero, add_zero] at nonnegative
  exact (not_lt_of_ge nonnegative) (mul_neg_of_neg_of_pos (sub_neg.mpr after) plane_positive)

/-- The flat alternative or every interior point is available as a positive roof source. -/
theorem flat_or_positive_interior_roof :
    K.TiltBound 0 ∨ ∀ p ∈ interior K.footprint, 0 < K.roofHeight p := by
  rcases K.flat_or_positive_roof with flat | ⟨q, member, positive⟩
  · exact Or.inl flat
  · exact Or.inr (fun _ inside => K.roofHeight_pos_of_mem_interior member positive inside)

end Unfoldings.ConvexCap
