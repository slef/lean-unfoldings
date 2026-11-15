module

public import Unfoldings.Geometry.TwoBankOppositeSide
public import Unfoldings.Geometry.LocalConeRegularClosed
public import Mathlib.Analysis.Complex.ReImTopology

/-! Actual strict interior sides of both polygonal gap banks away from their common source. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The first bank's positive side is the genuine geometric interior, including at its bends. -/
theorem eventually_mem_interior_twoBankGap_iff_first_side (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ z in 𝓝 (R.radialPoint first_outward first_nonzero r),
      z ∈ interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
        positive_phase) ↔ 0 < ((R.bankFrame first_outward first_nonzero).symm z).im := by
  let H := (R.bankFrame first_outward first_nonzero).symm
  have near : ∀ᶠ z in 𝓝 (R.radialPoint first_outward first_nonzero r),
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z ∈ H ⁻¹' {w : ℂ | 0 ≤ w.im} :=
    R.eventually_mem_twoBankGap_iff_first_side Q first_outward first_nonzero last_outward
      last_nonzero positive_phase r positive
  have inside := eventually_mem_interior_iff_of_local_eq near
  rwa [← H.preimage_interior, Complex.interior_setOfPred_le_im] at inside

/-- The second bank's negative side is the actual geometric interior, with opposite orientation. -/
theorem eventually_mem_interior_twoBankGap_iff_second_side (common : Q.start = R.start)
    (r : ℝ≥0) (positive : 0 < r) :
    ∀ᶠ z in 𝓝 (Q.radialPoint last_outward last_nonzero r),
      z ∈ interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
        positive_phase) ↔ ((Q.bankFrame last_outward last_nonzero).symm z).im < 0 := by
  let H := (Q.bankFrame last_outward last_nonzero).symm
  have near : ∀ᶠ z in 𝓝 (Q.radialPoint last_outward last_nonzero r),
      z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
        z ∈ H ⁻¹' {w : ℂ | w.im ≤ 0} :=
    R.eventually_mem_twoBankGap_iff_opposite_side Q first_outward first_nonzero last_outward
      last_nonzero positive_phase common r positive
  have inside := eventually_mem_interior_iff_of_local_eq near
  rwa [← H.preimage_interior, Complex.interior_setOfPred_im_le] at inside

end Unfoldings.PolygonalRay
