module

public import Unfoldings.Geometry.DirectionFrame
public import Unfoldings.Geometry.AffineOrientation
public import Unfoldings.Geometry.PlanarConjugation

/-! Positively oriented orthogonal coordinates for a prescribed actual section direction. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Correct the initial direction frame by reflection if its determinant is negative. -/
def positiveDirectionFrame (direction : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  if 0 < orientationScale (directionFrame direction).toAffineIsometryEquiv.toAffineMap then
    directionFrame direction else (directionFrame direction).trans planeConjugation

/-- The single corrected frame preserves every positive original signed area. -/
theorem positiveDirectionFrame_positive (direction a b : Plane) (positive : 0 < orient 0 a b) :
    0 < orient 0 (positiveDirectionFrame direction a) (positiveDirectionFrame direction b) := by
  have transport := orient_affine_linear
    (directionFrame direction).toAffineIsometryEquiv.toAffineMap a b
  change orient 0 (directionFrame direction a) (directionFrame direction b) =
    orientationScale (directionFrame direction).toAffineIsometryEquiv.toAffineMap *
      orient 0 a b at transport
  by_cases first : 0 < orientationScale (directionFrame direction).toAffineIsometryEquiv.toAffineMap
  · simp only [positiveDirectionFrame, ite_eq_left first]
    rw [transport]
    exact mul_pos first positive
  · have negative := lt_of_le_of_ne (le_of_not_gt first)
      (orientationScale_ne_zero (directionFrame direction).toAffineIsometryEquiv)
    simp only [positiveDirectionFrame, ite_eq_right first, LinearIsometryEquiv.trans_apply,
      orient_planeConjugation]
    rw [transport]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos negative positive)

/-- Correcting orientation leaves the prescribed vector on the positive horizontal axis. -/
theorem positiveDirectionFrame_apply (direction : Plane) :
    positiveDirectionFrame direction direction = EuclideanSpace.single 0 ‖direction‖ := by
  unfold positiveDirectionFrame
  split_ifs
  · exact directionFrame_apply direction
  · change planeConjugation (directionFrame direction direction) = _
    rw [directionFrame_apply, planeConjugation_apply]
    ext i
    fin_cases i <;> simp [EuclideanSpace.single]

@[simp] theorem positiveDirectionFrame_horizontal (direction : Plane) :
    positiveDirectionFrame direction direction 0 = ‖direction‖ := by
  rw [positiveDirectionFrame_apply]
  simp [EuclideanSpace.single]

@[simp] theorem positiveDirectionFrame_vertical (direction : Plane) :
    positiveDirectionFrame direction direction 1 = 0 := by
  rw [positiveDirectionFrame_apply]
  simp [EuclideanSpace.single]

/-- A positive original transverse determinant means the framed edge points downward. -/
theorem positiveDirectionFrame_transverse_sign {direction edge : Plane} (nonzero : direction ≠ 0) :
    0 < orient 0 edge direction ↔ positiveDirectionFrame direction edge 1 < 0 := by
  let F := positiveDirectionFrame direction
  have frame_scale : 0 < orientationScale F.toAffineIsometryEquiv.toAffineMap := by
    have original : 0 < orient 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) := by
      norm_num [orient, EuclideanSpace.single]
    exact positiveDirectionFrame_positive direction _ _ original
  have transport := orient_affine_linear F.toAffineIsometryEquiv.toAffineMap edge direction
  change orient 0 (F edge) (F direction) =
    orientationScale F.toAffineIsometryEquiv.toAffineMap * orient 0 edge direction at transport
  have cross : orient 0 (F edge) (F direction) = -(F edge 1) * ‖direction‖ := by
    change orient 0 (F edge) (positiveDirectionFrame direction direction) = _
    simp only [orient, PiLp.zero_apply, sub_zero, positiveDirectionFrame_horizontal,
      positiveDirectionFrame_vertical, mul_zero, zero_sub]
    ring
  have norm_positive := norm_pos_iff.mpr nonzero
  constructor
  · intro positive
    have mapped : 0 < orient 0 (F edge) (F direction) := by
      rw [transport]
      exact mul_pos frame_scale positive
    rw [cross] at mapped
    nlinarith
  · intro negative
    have mapped : 0 < orient 0 (F edge) (F direction) := by
      rw [cross]
      exact mul_pos (neg_pos.mpr negative) norm_positive
    rw [transport] at mapped
    exact (mul_pos_iff_of_pos_left frame_scale).mp mapped

/-- Zero transverse coordinate is exactly membership in the complete section line. -/
theorem exists_lineMap_of_positiveFrame_vertical_zero {p q x : Plane} (different : p ≠ q)
    (zero : positiveDirectionFrame (q - p) (x - p) 1 = 0) :
    ∃ t : ℝ, x = AffineMap.lineMap p q t := by
  let F := positiveDirectionFrame (q - p)
  let t := F (x - p) 0 / ‖q - p‖
  have nonzero : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr different.symm)
  have framed : F (x - p) = t • F (q - p) := by
    rw [positiveDirectionFrame_apply]
    ext i
    fin_cases i
    · change F (x - p) 0 = t * (EuclideanSpace.single (0 : Fin 2) ‖q - p‖) 0
      simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
      exact (div_mul_cancel₀ _ nonzero).symm
    · change F (x - p) 1 = t * (EuclideanSpace.single (0 : Fin 2) ‖q - p‖) 1
      simpa [EuclideanSpace.single] using zero
  have original : x - p = t • (q - p) := F.injective (by rw [map_smul]; exact framed)
  exact ⟨t, by rw [AffineMap.lineMap_apply_module', ← original, sub_add_cancel]⟩

end Unfoldings
