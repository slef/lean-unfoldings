module

public import Unfoldings.Cone.Sector
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Normed.Module.Normalize

/-! Actual angles of vectors with positive horizontal component are real arctangent differences. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def slopeRay (s : ℝ) : ℂ := ⟨1, s⟩

theorem slopeRay_ne_zero (s : ℝ) : slopeRay s ≠ 0 := by
  intro equal
  have first := congrArg Complex.re equal
  change (1 : ℝ) = 0 at first
  norm_num at first

theorem norm_slopeRay (s : ℝ) : ‖slopeRay s‖ = Real.sqrt (1 + s ^ 2) := by
  simp only [slopeRay, Complex.norm_def, Complex.normSq_mk, one_mul, sq]

theorem arg_slopeRay (s : ℝ) : (slopeRay s).arg = Real.arctan s := by
  rw [Complex.arg_of_re_nonneg (by change (0 : ℝ) ≤ 1; norm_num), norm_slopeRay,
    Real.arctan_eq_arcsin]
  rfl

theorem normalize_slopeRay (s : ℝ) : NormedSpace.normalize (slopeRay s) =
    polarRay (Real.arctan s) := by
  have polar := (Complex.norm_mul_exp_arg_mul_I (slopeRay s)).symm
  change slopeRay s = (‖slopeRay s‖ : ℂ) * polarRay (slopeRay s).arg at polar
  rw [arg_slopeRay] at polar
  have nonzero := norm_ne_zero_iff.mpr (slopeRay_ne_zero s)
  calc
    _ = ((‖slopeRay s‖⁻¹ : ℝ) : ℂ) *
        ((‖slopeRay s‖ : ℂ) * polarRay (Real.arctan s)) := by
      change ((‖slopeRay s‖⁻¹ : ℝ) : ℂ) * slopeRay s = _
      exact congrArg (((‖slopeRay s‖⁻¹ : ℝ) : ℂ) * ·) polar
    _ = _ := by
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ nonzero,
        Complex.ofReal_one, one_mul]

/-- The difference lies strictly between minus pi and pi, so this is a genuine angular distance. -/
theorem angle_slopeRay (s t : ℝ) :
    InnerProductGeometry.angle (slopeRay s) (slopeRay t) =
      |Real.arctan t - Real.arctan s| := by
  rw [← InnerProductGeometry.angle_normalize_left, ← InnerProductGeometry.angle_normalize_right,
    normalize_slopeRay, normalize_slopeRay]
  have sbounds := Real.arctan_mem_Ioo s
  have tbounds := Real.arctan_mem_Ioo t
  by_cases ordered : Real.arctan s ≤ Real.arctan t
  · rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
    exact angle_polarRay _ _ (sub_nonneg.mpr ordered) (by linarith [sbounds.1, tbounds.2])
  · rw [InnerProductGeometry.angle_comm, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge ordered))]
    have angle := angle_polarRay (Real.arctan t) (Real.arctan s)
      (by linarith : 0 ≤ Real.arctan s - Real.arctan t)
      (by linarith [tbounds.1, sbounds.2] : Real.arctan s - Real.arctan t ≤ Real.pi)
    exact angle.trans (by ring)

end Unfoldings
