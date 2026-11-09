module

public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.LinearAlgebra.Span.Basic

/-! A nonzero line has exactly its two opposite unit directions. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_norm_smul_eq_or_eq_neg_of_mem_span {d e : E}
    (d_nonzero : d ≠ 0) (e_nonzero : e ≠ 0) (parallel : d ∈ Submodule.span ℝ {e}) :
    ‖e‖⁻¹ • e = ‖d‖⁻¹ • d ∨ ‖e‖⁻¹ • e = -(‖d‖⁻¹ • d) := by
  obtain ⟨t, equal⟩ := Submodule.mem_span_singleton.mp parallel
  have t_nonzero : t ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at equal
    exact d_nonzero equal.symm
  rcases lt_or_gt_of_ne t_nonzero with negative | positive
  · have ray : SameRay ℝ e (-d) := by
      rw [← equal, ← neg_smul]
      exact SameRay.sameRay_nonneg_smul_right e (neg_nonneg.mpr negative.le)
    right
    simpa only [norm_neg, smul_neg] using
      (sameRay_iff_inv_norm_smul_eq_of_ne e_nonzero (neg_ne_zero.mpr d_nonzero)).mp ray
  · have ray : SameRay ℝ e d := by
      rw [← equal]
      exact SameRay.sameRay_nonneg_smul_right e positive.le
    exact Or.inl ((sameRay_iff_inv_norm_smul_eq_of_ne e_nonzero d_nonzero).mp ray)

end Unfoldings
