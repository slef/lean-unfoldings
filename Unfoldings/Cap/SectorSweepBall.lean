module

public import Unfoldings.Cap.SectorWaterfallDensity

/-! A physical source ball is strictly inside every sector sweep when the cutoff is larger. -/

@[expose] public section

namespace Unfoldings

variable {t : ℝ} (positive : 0 < t) (small : t < 1) (source : Plane)

theorem closedBall_subset_sectorSweepInterior {radius cutoff : ℝ} (room : 2 * radius < cutoff) :
    Metric.closedBall source radius ⊆ sectorSweepInterior positive small source cutoff := by
  intro p member i
  let z := (fiveSectorFrame t positive small i).place (p - source)
  have norm_bound : ‖z‖ ≤ radius := by
    rw [show ‖z‖ = ‖p - source‖ from (fiveSectorFrame t positive small i).place.norm_map _]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using member
  have real := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have imaginary := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  change z.re + z.im < cutoff
  linarith

end Unfoldings
