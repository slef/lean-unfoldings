module

public import Unfoldings.Cone.ConsecutiveSectorMetric

/-! The remainder after retaining an untouched original side of a completed corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Join the original remaining side to the inserted full-turn defect sector. -/
abbrev CompletedCornerRemainder (original untouched : ℝ) :=
  ConsecutiveSectorGluing (original - untouched) (2 * Real.pi - original)

/-- The actual joined metric remainder has width `2 * pi - untouched`. The construction
keeps the original remaining sector and the inserted sector as separate whole metric pieces. -/
def completedCornerRemainderIsometryEquiv (original untouched : ℝ)
    (positive : 0 < untouched) (before : untouched < original) (small : original ≤ 2 * Real.pi) :
    CompletedCornerRemainder original untouched ≃ᵢ
      PolygonalPoint (closedAngularSector (2 * Real.pi - untouched)) :=
  (consecutiveSectorNonnegIsometryEquiv (original - untouched) (2 * Real.pi - original)
    (sub_pos.mpr before) (sub_nonneg.mpr small) (by linarith)).trans
      (PolygonalPoint.congrIsometryEquiv (congrArg closedAngularSector (by ring)))

/-- Both original pieces retain their physical coordinates in the new remainder. -/
@[simp] theorem completedCornerRemainderIsometryEquiv_point (original untouched : ℝ)
    (positive : 0 < untouched) (before : untouched < original) (small : original ≤ 2 * Real.pi)
    (x : MetricGluing.Total (fun i =>
      PolygonalPoint (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original) i))) :
    (completedCornerRemainderIsometryEquiv original untouched positive before small
      (MetricGluing.point _ (MetricGluing.polygonalCoincident
        (consecutiveSectorRegion (original - untouched) (2 * Real.pi - original))) x)).val =
          x.2.val := by
  simp only [completedCornerRemainderIsometryEquiv, IsometryEquiv.trans_apply,
    PolygonalPoint.congrIsometryEquiv_val, consecutiveSectorNonnegIsometryEquiv_point]

/-- Rotating the new remainder back to the original untouched-side frame gives exactly
the actual complement of that original side in the completed plane. -/
theorem completedCornerRemainder_region (original untouched : ℝ)
    (before : untouched ≤ original) (small : original ≤ 2 * Real.pi) :
    rotation (Circle.exp untouched) ''
      (closedAngularSector (original - untouched) ∪
        rotation (Circle.exp (original - untouched)) ''
          closedAngularSector (2 * Real.pi - original)) = complementarySector untouched := by
  rw [closedAngularSector_union_consecutive _ _ (sub_nonneg.mpr before) (sub_nonneg.mpr small)]
  have total : original - untouched + (2 * Real.pi - original) = 2 * Real.pi - untouched := by ring
  rw [total]
  rfl

/-- The real angle added on this side is exactly the original full-turn defect. -/
theorem completedCornerRemainder_angle_increment (original untouched : ℝ) :
    (2 * Real.pi - untouched) - (original - untouched) = 2 * Real.pi - original := by ring

end Unfoldings
