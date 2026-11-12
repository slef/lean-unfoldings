module

public import Unfoldings.Geometry.WedgeRotationFrame
public import Unfoldings.Geometry.AffineOrientation

/-! Positively ordered acute-wedge frames preserve the actual side of every directed edge. -/

@[expose] public section

namespace Unfoldings.AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem exists_positive_side_scale (positive : 0 < orient 0 u v) :
    ∃ scale > 0, ∀ a b c : Plane,
      (starRingEnd ℂ (B.place (b - a)) * B.place (c - a)).im = scale * orient a b c := by
  let A := B.place.trans Complex.orthonormalBasisOneI.repr
  let scale := orientationScale A.toAffineIsometryEquiv.toAffineMap
  have at_banks : 0 ≤ orient 0 (A u) (A v) := by
    have area := orient_complex_repr_zero (B.place u) (B.place v)
    change orient 0 (A u) (A v) = _ at area
    rw [area]
    exact B.banks_cross_nonneg
  have transport := orient_affine_linear A.toAffineIsometryEquiv.toAffineMap u v
  change orient 0 (A u) (A v) = scale * orient 0 u v at transport
  have nonzero : scale ≠ 0 := orientationScale_ne_zero A.toAffineIsometryEquiv
  have scale_nonnegative : 0 ≤ scale :=
    (mul_nonneg_iff_of_pos_right positive).mp (transport ▸ at_banks)
  have scale_positive : 0 < scale := lt_of_le_of_ne scale_nonnegative nonzero.symm
  refine ⟨scale, scale_positive, fun a b c => ?_⟩
  have area := orient_complex_repr (B.place a) (B.place b) (B.place c)
  have mapped := orient_affineMap A.toAffineIsometryEquiv.toAffineMap a b c
  change orient (A a) (A b) (A c) = scale * orient a b c at mapped
  rw [← B.place.map_sub, ← B.place.map_sub] at area
  change orient (A a) (A b) (A c) = _ at area
  exact area.symm.trans mapped

theorem orient_nonneg_iff (positive : 0 < orient 0 u v) (a b c : Plane) :
    0 ≤ (starRingEnd ℂ (B.place (b - a)) * B.place (c - a)).im ↔ 0 ≤ orient a b c := by
  obtain ⟨scale, scale_positive, bound⟩ := B.exists_positive_side_scale positive
  rw [bound]
  exact mul_nonneg_iff_of_pos_left scale_positive

theorem orient_nonpos_iff (positive : 0 < orient 0 u v) (a b c : Plane) :
    (starRingEnd ℂ (B.place (b - a)) * B.place (c - a)).im ≤ 0 ↔ orient a b c ≤ 0 := by
  obtain ⟨scale, scale_positive, bound⟩ := B.exists_positive_side_scale positive
  rw [bound]
  constructor
  · intro nonpositive
    by_contra reversed
    exact not_lt_of_ge nonpositive (mul_pos scale_positive (lt_of_not_ge reversed))
  · intro nonpositive
    exact mul_nonpos_of_nonneg_of_nonpos scale_positive.le nonpositive

theorem centered_cross_eq (q a b : Plane) (z : ℂ) :
    (starRingEnd ℂ (B.place (b - q) - B.place (a - q)) * (z - B.place (a - q))).im =
      (starRingEnd ℂ (B.place (b - a)) * B.place (q + B.place.symm z - a)).im := by
  have first : B.place (b - q) - B.place (a - q) = B.place (b - a) := by
    rw [← B.place.map_sub]
    congr 1
    abel
  have last : z - B.place (a - q) = B.place (q + B.place.symm z - a) := by
    simp only [B.place.map_sub, B.place.map_add, B.place.apply_symm_apply]
    abel
  rw [first, last]

theorem centered_orient_nonneg_iff (positive : 0 < orient 0 u v)
    (q a b : Plane) (z : ℂ) :
    0 ≤ (starRingEnd ℂ (B.place (b - q) - B.place (a - q)) * (z - B.place (a - q))).im ↔
      0 ≤ orient a b (q + B.place.symm z) := by
  rw [B.centered_cross_eq]
  exact B.orient_nonneg_iff positive a b _

theorem centered_orient_nonpos_iff (positive : 0 < orient 0 u v)
    (q a b : Plane) (z : ℂ) :
    (starRingEnd ℂ (B.place (b - q) - B.place (a - q)) * (z - B.place (a - q))).im ≤ 0 ↔
      orient a b (q + B.place.symm z) ≤ 0 := by
  rw [B.centered_cross_eq]
  exact B.orient_nonpos_iff positive a b _

end Unfoldings.AcuteWedgeFrame
