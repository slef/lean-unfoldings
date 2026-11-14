module

public import Unfoldings.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.Linarith

/-! The annular ratio conditions give the paper's explicit positive radial margin. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def annularHistoryAngle (ρ β : ℝ) : ℝ := Real.arccos (ρ * Real.cos β)

def annularRadialMargin (ρ β ζ : ℝ) : ℝ :=
  min (Real.cos (β + annularHistoryAngle ρ β)) (Real.cos (annularHistoryAngle ρ β + ζ))

theorem annular_history_angle_sector {ρ β : ℝ} (rhopos : 0 < ρ) (rho_le : ρ ≤ 1)
    (beta : 0 ≤ β) (acute : β < Real.pi / 2) (ratio : Real.tan β < ρ) :
    β + annularHistoryAngle ρ β < Real.pi / 2 := by
  have cospos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], acute⟩
  have strict : Real.sin β < ρ * Real.cos β := by
    rw [Real.tan_eq_sin_div_cos] at ratio
    exact (div_lt_iff₀ cospos).mp ratio
  have upper : ρ * Real.cos β ≤ 1 :=
    (mul_le_of_le_one_right rhopos.le (Real.cos_le_one β)).trans rho_le
  have comparison := Real.arccos_lt_arccos (Real.neg_one_le_sin β) strict upper
  rw [← Real.cos_pi_div_two_sub β,
    Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])] at comparison
  exact (by dsimp [annularHistoryAngle]; linarith)

theorem annular_radial_margin_pos {ρ β ζ : ℝ} (rhopos : 0 < ρ) (rho_le : ρ ≤ 1)
    (beta : 0 ≤ β) (acute : β < Real.pi / 2) (ratio : Real.tan β < ρ)
    (zeta : 0 ≤ ζ) (exterior : annularHistoryAngle ρ β + ζ < Real.pi / 2) :
    0 < annularRadialMargin ρ β ζ := by
  have sector := annular_history_angle_sector rhopos rho_le beta acute ratio
  have angle : 0 ≤ annularHistoryAngle ρ β := Real.arccos_nonneg _
  exact lt_min
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], sector⟩)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], exterior⟩)

end Unfoldings
