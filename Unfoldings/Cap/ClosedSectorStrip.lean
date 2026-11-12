module

public import Unfoldings.Cap.SectorPositionMargins

/-! The full closed sector strip, including both banks, stays within its sweep-height ball. -/

@[expose] public section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_forward_norm_bound {z : ℂ} (member : z ∈ B.enclosingStrip.carrier)
    (forward : 0 ≤ z.re + z.im) : ‖z‖ ≤ z.re + z.im := by
  obtain ⟨μ, positive, bound⟩ := B.exists_enclosingStrip_coordinate_margin
  have coordinates := bound z member forward
  have first : 0 ≤ z.re := (mul_nonneg positive.le forward).trans coordinates.1
  have last : 0 ≤ z.im := (mul_nonneg positive.le forward).trans coordinates.2
  have norm := Complex.norm_le_abs_re_add_abs_im z
  rwa [abs_of_nonneg first, abs_of_nonneg last] at norm

end AcuteWedgeFrame

theorem closed_sector_strip_slab_mem_closedBall {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : FiveSector) (q : Plane) {cutoff : ℝ} {z : ℂ}
    (member : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier)
    (slab : z.re + z.im ∈ Set.Icc 0 cutoff) :
    q + (fiveSectorFrame t positive small i).place.symm z ∈ Metric.closedBall q cutoff := by
  let frame := (fiveSectorFrame t positive small i).place
  have bound := (fiveSectorFrame t positive small i).enclosingStrip_forward_norm_bound
    member slab.1
  rw [Metric.mem_closedBall, dist_eq_norm]
  have vector : q + frame.symm z - q = frame.symm z := by abel
  rw [vector, frame.symm.norm_map]
  exact bound.trans slab.2

end Unfoldings
