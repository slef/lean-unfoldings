module

public import Unfoldings.Geometry.AnnularRadialMargin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! A positive routing width gives the stronger radial margin uniformly at all fine vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The two-history-angle condition supplies a genuine positive radial margin. -/
theorem fine_annular_radial_margin_pos {ρ β : ℝ}
    (small : 2 * annularHistoryAngle ρ β < Real.pi / 2) :
    0 < Real.cos (2 * annularHistoryAngle ρ β) :=
  Real.cos_pos_of_mem_Ioo ⟨by
    have nonnegative := Real.arccos_nonneg (ρ * Real.cos β)
    change -(Real.pi / 2) < 2 * Real.arccos (ρ * Real.cos β)
    linarith [Real.pi_pos], small⟩

/-- A sufficiently round slope annulus admits a positive width before choosing a mesh. -/
theorem exists_positive_fine_annular_width {ρ : ℝ} (round : Real.arccos ρ < Real.pi / 4) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ β ∈ Set.Icc (0 : ℝ) δ, 2 * annularHistoryAngle ρ β < Real.pi / 2 := by
  have at_zero : 2 * annularHistoryAngle ρ 0 < Real.pi / 2 := by
    simp only [annularHistoryAngle, Real.cos_zero, mul_one]
    linarith
  have continuous : ContinuousAt (fun β => 2 * annularHistoryAngle ρ β) 0 := by
    unfold annularHistoryAngle
    fun_prop
  have nearby : ∀ᶠ β in nhds (0 : ℝ), 2 * annularHistoryAngle ρ β < Real.pi / 2 :=
    continuous.eventually (gt_mem_nhds at_zero)
  obtain ⟨r, rpositive, bound⟩ := Metric.eventually_nhds_iff.mp nearby
  let δ := min (r / 2) (Real.pi / 4)
  have positive : 0 < δ := lt_min (by positivity) (by positivity)
  have small : δ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨δ, ⟨positive, small⟩, fun β beta => bound ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg beta.1]
  exact beta.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))

end Unfoldings
