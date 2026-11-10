module

public import Unfoldings.Cone.AngularHomeomorph
public import Unfoldings.Cone.AngularOverlap

/-! A multiply covered development still has the topology of a half-plane. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples

def fiveRightAngles : AngularFan 4 where
  angle _ := Real.pi / 2
  positive _ := half_pos Real.pi_pos
  small _ := by linarith [Real.pi_pos]

theorem fiveRightAngles_totalAngle : fiveRightAngles.totalAngle = 5 * Real.pi / 2 := by
  simp [AngularFan.totalAngle, fiveRightAngles]
  ring

theorem fiveRightAngles_overlaps : ¬ fiveRightAngles.Nonoverlapping := by
  rw [fiveRightAngles.nonoverlapping_iff_totalAngle_le, fiveRightAngles_totalAngle]
  linarith [Real.pi_pos]

/-- The topology theorem applies even though the actual developed face interiors overlap. -/
def fiveRightAngles_halfPlane : fiveRightAngles.Surface ≃ₜ PlanarTopology.closedHalfPlane :=
  fiveRightAngles.halfPlaneHomeomorph

end Unfoldings.Examples
