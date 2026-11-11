module

public import Unfoldings.Geometry.AngleMonotoneCoordinates
public import Unfoldings.Geometry.LevelCrossings

/-! Acute angle-monotone chains have uniformly bounded signed crossings of every planar ray. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

/-- Translation and rotation permit any ray origin and direction, without a crossing-count input. -/
theorem AngleMonotone.abs_sum_rayCrossings_le_one {width : ℝ}
    (monotone : P.AngleMonotone width) (small : width < Real.pi / 2)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (cut level : ℝ) :
    |∑ i : Fin n, horizontalRayCrossing (fun j => (P.inFrame L center).vertex j 0)
      (fun j => (P.inFrame L center).vertex j 1) cut level i| ≤ 1 := by
  rcases ((monotone.inFrame P L center).coordinate_monotone _ small) with
    rightward | leftward | upward | downward
  · exact abs_sum_horizontalRayCrossing_of_monotone_x _ _ rightward cut level
  · exact abs_sum_horizontalRayCrossing_of_antitone_x _ _ leftward cut level
  · exact abs_sum_horizontalRayCrossing_of_monotone_y _ _ upward cut level
  · exact abs_sum_horizontalRayCrossing_of_antitone_y _ _ downward cut level

end Unfoldings.PolygonalChain
