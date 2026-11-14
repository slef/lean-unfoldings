module

public import Unfoldings.Geometry.ComplexRotation
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! A continuous choice of rotation on positive concentric circles extends across the center. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- The value at radius zero is immaterial, so no angular limit at the center is required. -/
def radialTwist (coefficient : ℝ≥0 → ℂ) (z : ℂ) : ℂ := coefficient ‖z‖₊ * z

@[simp] theorem radialTwist_zero (coefficient : ℝ≥0 → ℂ) : radialTwist coefficient 0 = 0 := by
  simp [radialTwist]

variable (coefficient : ℝ≥0 → ℂ)
  (unit : ∀ r, 0 < r → ‖coefficient r‖ = 1)
  (regular : ContinuousOn coefficient (Set.Ioi 0))

include unit in
@[simp] theorem norm_radialTwist (z : ℂ) : ‖radialTwist coefficient z‖ = ‖z‖ := by
  by_cases zero : z = 0
  · simp [zero]
  · rw [radialTwist, norm_mul, unit ‖z‖₊ (nnnorm_pos.mpr zero), one_mul]

include unit in
@[simp] theorem nnnorm_radialTwist (z : ℂ) : ‖radialTwist coefficient z‖₊ = ‖z‖₊ :=
  NNReal.eq (norm_radialTwist coefficient unit z)

include unit regular in
theorem continuous_radialTwist : Continuous (radialTwist coefficient) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases zero : z = 0
  · subst z
    apply Metric.continuousAt_iff.mpr
    intro ε positive
    refine ⟨ε, positive, ?_⟩
    intro w close
    simpa only [radialTwist_zero, dist_zero_right, norm_radialTwist coefficient unit] using close
  · exact ((regular.continuousAt (isOpen_Ioi.mem_nhds (nnnorm_pos.mpr zero))).comp
      continuous_nnnorm.continuousAt).mul continuous_id.continuousAt

include unit in
private theorem conjugate_coefficient_mul (r : ℝ≥0) (positive : 0 < r) :
    star (coefficient r) * coefficient r = 1 := by
  change (starRingEnd ℂ) (coefficient r) * coefficient r = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, unit r positive]
  norm_num

/-- Independent rotations of concentric circles give a genuine homeomorphism of the whole plane. -/
def radialTwistHomeomorph : ℂ ≃ₜ ℂ where
  toFun := radialTwist coefficient
  invFun := radialTwist (fun r => star (coefficient r))
  left_inv z := by
    by_cases zero : z = 0
    · simp [zero]
    · change star (coefficient ‖radialTwist coefficient z‖₊) * (coefficient ‖z‖₊ * z) = z
      rw [nnnorm_radialTwist coefficient unit, ← mul_assoc,
        conjugate_coefficient_mul coefficient unit ‖z‖₊ (nnnorm_pos.mpr zero), one_mul]
  right_inv z := by
    by_cases zero : z = 0
    · simp [zero]
    · have conjugate_unit (r : ℝ≥0) (positive : 0 < r) : ‖star (coefficient r)‖ = 1 := by
        simpa only [norm_star] using unit r positive
      change coefficient ‖radialTwist (fun r => star (coefficient r)) z‖₊ *
        (star (coefficient ‖z‖₊) * z) = z
      rw [nnnorm_radialTwist _ conjugate_unit, ← mul_assoc,
        mul_comm (coefficient ‖z‖₊),
        conjugate_coefficient_mul coefficient unit ‖z‖₊ (nnnorm_pos.mpr zero), one_mul]
  continuous_toFun := continuous_radialTwist coefficient unit regular
  continuous_invFun := continuous_radialTwist _
    (fun r positive => by simpa only [norm_star] using unit r positive)
    (continuous_star.comp_continuousOn regular)

@[simp] theorem radialTwistHomeomorph_apply (z : ℂ) :
    radialTwistHomeomorph coefficient unit regular z = coefficient ‖z‖₊ * z := rfl

end Unfoldings
