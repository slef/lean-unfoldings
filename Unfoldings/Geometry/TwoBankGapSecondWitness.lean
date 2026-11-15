module

public import Unfoldings.Geometry.TwoBankGapInteriorApproach
public import Unfoldings.Geometry.ClockwiseConeApproach

/-! Opposite source-circle normals select the occupied side of actual polygonal gap corners. -/

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

/-- An original source-circle normal in the candidate cone gives actual geometric orientation
samples arbitrarily near the second bank point, including at its internal bends. -/
theorem frequently_second_bank_interior_sector (common : Q.start = R.start)
    (r : ℝ≥0) (positive : 0 < r) (cone : Set ℂ)
    (radial : ∀ (v : ℂ) (t : ℝ), 0 < t → (t • v ∈ cone ↔ v ∈ cone))
    (normal : -(Complex.I * (Q.radialPoint last_outward last_nonzero r - Q.start)) ∈
      interior cone) :
    ∃ᶠ z in 𝓝 (Q.radialPoint last_outward last_nonzero r),
      z ∈ interior (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
        positive_phase) ∧ z - Q.radialPoint last_outward last_nonzero r ∈ interior cone := by
  let p := Q.radialPoint last_outward last_nonzero r
  have into_gap := R.eventually_rotate_second_bank_mem_gap_interior Q first_outward first_nonzero
    last_outward last_nonzero positive_phase common r positive
  have into_cone := eventually_clockwise_sub_mem_interior_cone Q.start p radial normal
  have derivative := hasDerivAt_sourceRotation_neg_angle Q.start p
  have zero : sourceRotation Q.start (-(0 : ℝ)) p = p := by
    simp [sourceRotation_apply, complexRotation_apply]
  have tends := derivative.continuousAt.tendsto
  rw [zero] at tends
  have tends_right := tends.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  by_contra no_samples
  rw [not_frequently] at no_samples
  obtain ⟨θ, geometric, outside⟩ :=
    ((into_gap.and into_cone).and (tends_right.eventually no_samples)).exists
  exact outside geometric

end Unfoldings.PolygonalRay
