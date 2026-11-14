module

public import Unfoldings.Geometry.PolygonalRotationGap
public import Unfoldings.Cone.SectorClosed

/-! Every point of an actual bank-rotation gap lies on one intermediate rotated bank. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- Closed intermediate angles cover the entire gap, including its source and infinite end. -/
theorem mem_rotationGap_iff_sweep (angle : ℝ) (positive : 0 < angle) (small : angle < Real.pi)
    (z : ℂ) : z ∈ R.rotationGap outward nonzero angle ↔
      ∃ θ ∈ Set.Icc 0 angle, z ∈ R.rotatedCarrier θ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, θ, heading, equal⟩ := (mem_planarSector_iff_polar angle positive small w).mp hw
    refine ⟨θ, heading, R.radialPoint outward nonzero r, R.radialPoint_mem outward nonzero r, ?_⟩
    rw [equal, mul_comm, R.bankFrame_rotated_ray outward nonzero]
  · rintro ⟨θ, heading, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := Set.mem_range.mp ((R.range_radialPoint outward nonzero).symm ▸ hx)
    refine ⟨polarRay θ * (r : ℂ), ?_, R.bankFrame_rotated_ray outward nonzero r θ⟩
    simpa only [mul_comm] using polar_mem_planarSector angle r θ positive small r.coe_nonneg heading

end Unfoldings.PolygonalRay
