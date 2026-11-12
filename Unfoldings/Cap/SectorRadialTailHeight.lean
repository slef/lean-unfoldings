module

public import Unfoldings.Cap.GeometricTailCutoff
public import Unfoldings.Cap.GeometricSectorPositions
public import Unfoldings.Geometry.RadialTailHeightMembership

/-! Every radial component tip lies beyond a controlled interior sweep height. -/

@[expose] public section

namespace Unfoldings

theorem sector_radial_tail_tip_height_beyond {t cutoff : ℝ} (positive : 0 < t) (small : t < 1)
    {region : Set Plane} {source seed x : Plane} (T : RadialClipTail region source seed)
    (cutoff_positive : 0 < cutoff)
    (deep : Metric.closedBall source cutoff ⊆ interior region)
    (i : FiveSector) (member : x ∈ T.carrier)
    (inside : x - source ∈ closedFiveSector t i) :
    cutoff < ((fiveSectorFrame t positive small i).place (T.tip - source)).re +
      ((fiveSectorFrame t positive small i).place (T.tip - source)).im := by
  have far : cutoff < ‖T.tip - source‖ := by
    by_contra before
    apply T.boundary.2
    apply deep
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_not_gt before
  have nonzero : T.tip - source ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at far
    exact (cutoff_positive.trans far).false
  have cone := T.position_inDirectionWedge_of_mem member inside T.tip_mem
  have quadrant := (fiveSectorFrame t positive small i).quadrant_self cone nonzero
  have bound := complex_norm_le_diagonal_of_nonneg quadrant.1.le quadrant.2.le
  rw [LinearIsometryEquiv.norm_map] at bound
  exact far.trans_le bound

end Unfoldings
