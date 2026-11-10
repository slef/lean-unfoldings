module

public import Unfoldings.Cap.NormalImage

/-!
# Gnomonic coordinates recover the actual supporting normals

The normalized lift of a planar slope is a unit upward normal. The two maps
are inverse on unit upward normals, identifying the cap's planar normal image
with its actual spherical normal image.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- The horizontal plane at height one. -/
def northLift (p : Plane) : Space := WithLp.toLp 2 ![p 0, p 1, 1]

@[simp] theorem northLift_horizontal (p : Plane) : horizontal (northLift p) = p := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem northLift_height (p : Plane) : northLift p 2 = 1 := rfl

theorem northLift_ne_zero (p : Plane) : northLift p ≠ 0 := by
  intro equal
  have height := congrArg (fun v : Space => v 2) equal
  norm_num only [northLift_height, PiLp.zero_apply] at height

def gnomonicNormal (p : Plane) : Space := NormedSpace.normalize (northLift p)

theorem gnomonicNormal_unit (p : Plane) : ‖gnomonicNormal p‖ = 1 :=
  NormedSpace.norm_normalize (northLift_ne_zero p)

theorem gnomonicNormal_upward (p : Plane) : 0 < gnomonicNormal p 2 := by
  change 0 < (‖northLift p‖⁻¹ • northLift p) 2
  change 0 < ‖northLift p‖⁻¹ * 1
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero p))) zero_lt_one

theorem northLift_slope (normal : Space) (upward : 0 < normal 2) :
    northLift ((normal 2)⁻¹ • horizontal normal) = (normal 2)⁻¹ • normal := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · change 1 = (normal 2)⁻¹ * normal 2
    exact (inv_mul_cancel₀ upward.ne').symm

/-- The inverse gnomonic map recovers every actual unit upward normal. -/
theorem gnomonicNormal_slope (normal : Space) (unit : ‖normal‖ = 1) (upward : 0 < normal 2) :
    gnomonicNormal ((normal 2)⁻¹ • horizontal normal) = normal := by
  rw [gnomonicNormal, northLift_slope normal upward,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr upward),
    NormedSpace.normalize_eq_self_of_norm_eq_one unit]

/-- Slope coordinates recover every point of the planar normal image. -/
theorem slope_gnomonicNormal (p : Plane) :
    (gnomonicNormal p 2)⁻¹ • horizontal (gnomonicNormal p) = p := by
  have positive := norm_pos_iff.mpr (northLift_ne_zero p)
  have height : gnomonicNormal p 2 = ‖northLift p‖⁻¹ := by
    change ‖northLift p‖⁻¹ * 1 = ‖northLift p‖⁻¹
    exact mul_one _
  have projected : horizontal (gnomonicNormal p) = ‖northLift p‖⁻¹ • p := by
    change horizontal (‖northLift p‖⁻¹ • northLift p) = _
    rw [map_smul, northLift_horizontal]
  rw [height, projected, smul_smul, inv_mul_cancel₀ (inv_ne_zero positive.ne'), one_smul]

theorem gnomonicNormal_injective : Function.Injective gnomonicNormal := by
  intro p q equal
  have slopes := congrArg (fun n : Space => (n 2)⁻¹ • horizontal n) equal
  simpa only [slope_gnomonicNormal] using slopes

end Unfoldings.Cap

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem gnomonicNormal_normalSlope (f : Face) : Cap.gnomonicNormal (K.normalSlope f) = K.normal f :=
  Cap.gnomonicNormal_slope (K.normal f) (K.normal_unit f) (K.normal_upward f)

end Unfoldings.ConvexCap
