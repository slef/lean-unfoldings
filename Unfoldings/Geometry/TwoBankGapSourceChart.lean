module

public import Unfoldings.Geometry.TwoBankGapSourceSector
public import Unfoldings.Metric.PolygonalConvexChart

/-! The actual source corner of a Jordan gap has its original geometric sector metric. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The entire source ball, up to the first possible bend, has the exact original sector metric.
The chart preserves physical coordinates; a tangent-angle or flatness premise is not assumed. -/
theorem exists_twoBankGap_source_sector_isometry (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0)
    (first_segment : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (last_segment : segment ℝ Q.start (Q.start + e) ⊆ Q.carrier) :
    ∃ A : Metric.eball
      (R.twoBankSourcePoint Q first_outward first_nonzero last_outward last_nonzero positive_phase)
        (ENNReal.ofReal (min ‖d‖ ‖e‖)) ≃ᵢ
      Metric.ball
        (⟨R.start, source_mem_initialGapSector R.start d e⟩ : initialGapSector R.start d e)
        (min ‖d‖ ‖e‖),
      ∀ y, (A y).val.val = y.val.val := by
  exact PolygonalPoint.exists_local_convex_ball_isometry
    (R.twoBankSourcePoint Q first_outward first_nonzero last_outward last_nonzero positive_phase)
    ⟨R.start, source_mem_initialGapSector R.start d e⟩ rfl
    (lt_min (norm_pos_iff.mpr first) (norm_pos_iff.mpr last))
    (convex_initialGapSector R.start d e)
    (R.mem_twoBankGap_iff_initialGapSector Q first_outward first_nonzero last_outward last_nonzero
      positive_phase d e first last first_segment last_segment)

end Unfoldings.PolygonalRay
