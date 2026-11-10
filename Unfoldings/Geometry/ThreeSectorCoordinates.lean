module

public import Unfoldings.Geometry.ThreeSectorRays

/-! Each source-centered sector supplies one fixed monotone ambient coordinate. -/

@[expose] public section

namespace Unfoldings

theorem closedThreeSector_upper_y {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {v : Plane} (inside : v ∈ closedThreeSector t 0) : 0 ≤ v 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := inDirectionWedge_of_closedThreeSector nonnegative small 0 inside
  change 0 ≤ a * (1 + t) + b * (1 - t)
  exact add_nonneg (mul_nonneg ha (by linarith)) (mul_nonneg hb (by linarith))

theorem closedThreeSector_middle_x {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {v : Plane} (inside : v ∈ closedThreeSector t 1) : v 0 ≤ 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := inDirectionWedge_of_closedThreeSector nonnegative small 1 inside
  change a * (-1) + b * (-1) ≤ 0
  linarith

theorem closedThreeSector_lower_y {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    {v : Plane} (inside : v ∈ closedThreeSector t 2) : v 1 ≤ 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := inDirectionWedge_of_closedThreeSector nonnegative small 2 inside
  change a * (t - 1) + b * (-1 - t) ≤ 0
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (by linarith))
    (mul_nonpos_of_nonneg_of_nonpos hb (by linarith))

end Unfoldings
