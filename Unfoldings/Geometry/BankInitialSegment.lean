module

public import Unfoldings.Geometry.PolygonalRayFrame
public import Mathlib.Tactic.FieldSimp

/-! Exact initial straight-bank coordinates from actual source segments. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- The actual first straight piece fixes the normalized radial bank coefficient exactly. -/
theorem radialCoefficient_eq_of_initial_segment (d : ℂ) (genuine : d ≠ 0)
    (included : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (r : ℝ≥0) (positive : 0 < r) (before : (r : ℝ) ≤ ‖d‖) :
    R.radialCoefficient outward nonzero r = d / (‖d‖ : ℂ) := by
  let t : ℝ := (r : ℝ) / ‖d‖
  have norm_positive : 0 < ‖d‖ := norm_pos_iff.mpr genuine
  have bounds : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg r.coe_nonneg norm_positive.le, (div_le_one norm_positive).mpr before⟩
  let p := R.start + t • d
  have on_bank : p ∈ R.carrier := by
    apply included
    have member := lineMap_mem_segment ℝ R.start (R.start + d) bounds
    have value : AffineMap.lineMap R.start (R.start + d) t = p := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left]
      exact add_comm _ _
    rwa [value] at member
  have radius : ‖p - R.start‖ = (r : ℝ) := by
    rw [show p - R.start = t • d by simp only [p, add_sub_cancel_left], norm_smul,
      Real.norm_of_nonneg bounds.1]
    exact div_mul_cancel₀ _ norm_positive.ne'
  have same : R.radialPoint outward nonzero r = p := by
    apply R.eq_of_radius_eq outward nonzero (R.radialPoint_mem outward nonzero r) on_bank
    rw [dist_eq_norm', dist_eq_norm', R.norm_radialPoint_sub_start, radius]
  rw [radialCoefficient, same]
  change (R.start + t • d - R.start) / (r : ℂ) = d / (‖d‖ : ℂ)
  rw [add_sub_cancel_left, Complex.real_smul]
  dsimp [t]
  push_cast
  have radius_nonzero : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr positive.ne')
  have norm_nonzero : (‖d‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr norm_positive.ne'
  field_simp

/-- The original bank frame is an actual rigid rotation on its whole initial ball. -/
theorem bankFrame_eq_of_initial_segment (d : ℂ) (genuine : d ≠ 0)
    (included : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (z : ℂ) (before : ‖z‖ ≤ ‖d‖) :
    R.bankFrame outward nonzero z = R.start + (d / (‖d‖ : ℂ)) * z := by
  by_cases zero : z = 0
  · subst z
    simp only [R.bankFrame_apply, nnnorm_zero, mul_zero]
  · rw [R.bankFrame_apply,
      R.radialCoefficient_eq_of_initial_segment outward nonzero d genuine included ‖z‖₊
        (nnnorm_pos.mpr zero) before]

/-- The full frame preserves source-centered distances, including at bank corners. -/
theorem norm_bankFrame_sub_start (z : ℂ) :
    ‖R.bankFrame outward nonzero z - R.start‖ = ‖z‖ := by
  rw [bankFrame_apply, add_sub_cancel_left]
  exact norm_radialTwist (R.radialCoefficient outward nonzero)
    (R.radialCoefficient_unit outward nonzero) z

/-- The inverse frame has the exact physical source-centered radius. -/
theorem norm_bankFrame_symm (z : ℂ) :
    ‖(R.bankFrame outward nonzero).symm z‖ = ‖z - R.start‖ := by
  have same := R.norm_bankFrame_sub_start outward nonzero ((R.bankFrame outward nonzero).symm z)
  rw [Homeomorph.apply_symm_apply] at same
  exact same.symm

end Unfoldings.PolygonalRay
