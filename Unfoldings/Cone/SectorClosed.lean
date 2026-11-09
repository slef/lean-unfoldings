module

public import Unfoldings.Cone.SectorCoordinates

/-!
# Closed polar coordinates for sectors and the whole plane

Closed sector carriers include the apex and both banks. Nonnegative radii
and closed heading intervals describe exactly these sets. Every complex
point also has such a heading between zero and a full turn.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings

theorem polar_mem_planarSector (α r θ : ℝ) (positive : 0 < α)
    (small : α < Real.pi) (radius : 0 ≤ r) (heading : θ ∈ Set.Icc 0 α) :
    (r : ℂ) * polarRay θ ∈ planarSector α := by
  obtain ⟨c, hc, d, hd, combination⟩ := polarRay_mem_positive_span 0 α θ
    (by simpa only [sub_zero] using positive) (by simpa only [sub_zero] using small) heading
  refine ⟨r * c, mul_nonneg radius hc, r * d, mul_nonneg radius hd, ?_⟩
  rw [combination, polarRay_zero]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem mem_planarSector_iff_polar (α : ℝ) (positive : 0 < α) (small : α < Real.pi) (z : ℂ) :
    z ∈ planarSector α ↔
      ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc 0 α, z = (r : ℂ) * polarRay θ := by
  constructor
  · intro inside
    by_cases zero : z = 0
    · exact ⟨0, 0, ⟨le_rfl, positive.le⟩, by simp [zero]⟩
    · obtain ⟨r, radius, θ, heading, equal⟩ :=
        exists_polar_of_mem_planarSector α positive small z inside zero
      exact ⟨⟨r, radius.le⟩, θ, heading, equal⟩
  · rintro ⟨r, θ, heading, rfl⟩
    exact polar_mem_planarSector α r θ positive small r.coe_nonneg heading

theorem exists_polar_nonnegative_heading (z : ℂ) :
    ∃ r : ℝ≥0, ∃ θ ∈ Set.Icc 0 (2 * Real.pi), z = (r : ℂ) * polarRay θ := by
  have representation : z = (‖z‖₊ : ℂ) * polarRay z.arg :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  by_cases positive : 0 ≤ z.arg
  · exact ⟨‖z‖₊, z.arg, ⟨positive, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩,
      representation⟩
  · refine ⟨‖z‖₊, z.arg + 2 * Real.pi, ?_, ?_⟩
    · constructor <;> linarith [Complex.neg_pi_lt_arg z, lt_of_not_ge positive, Real.pi_pos]
    · have periodic : polarRay (z.arg + 2 * Real.pi) = polarRay z.arg :=
        congrArg (fun w : Circle => (w : ℂ)) (Circle.exp_add_two_pi z.arg)
      rw [periodic]
      exact representation

end Unfoldings
