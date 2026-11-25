module

public import Unfoldings.Geometry.PolarHeadingInterval
import Mathlib.Tactic.Linarith

/-! Shift the two permitted stem intervals according to the signed side headings. -/

@[expose] public section

namespace Unfoldings.FewestNets

open Real

private theorem hull_width_le {lo hi t A : ℝ} (span : hi - lo ≤ A)
    (before : hi - t ≤ A) (after : t - lo ≤ A) (nonneg : 0 ≤ A) :
    max hi t - min lo t ≤ A := by
  rcases le_total hi t with h | h <;> rcases le_total lo t with l | l
  · rwa [max_eq_right h, min_eq_left l]
  · rw [max_eq_right h, min_eq_right l, sub_self]
    exact nonneg
  · rwa [max_eq_left h, min_eq_left l]
  · rwa [max_eq_left h, min_eq_right l]

/-- Choose the actual paper's asymmetric heading windows. The west stem
window is expressed in reflected coordinates. Both intervals have width
`π / 2 - 2 * δ` and keep the radial margin `σ` with either permissible exit. -/
theorem exists_threeExit_windows {δ σ e w : ℝ}
    (positive : 0 < σ) (sigma_le : σ ≤ δ) (small : δ ≤ π / 8)
    (east : |e| < 2 * δ) (west : |w| < 2 * δ)
    (east_margin : σ < δ + e / 2) (west_margin : σ < δ - w / 2)
    (cross_margin : σ < 2 * δ + e - w) :
    let β := π / 2 - 2 * δ
    let A := π / 2 - σ
    ∃ L M : ℝ,
      0 < L ∧ L + β < π / 2 ∧ 0 < M ∧ M + β < π / 2 ∧
      w < L ∧ -e < M ∧
      max (L + β) e - min L e ≤ A ∧
      max (M + β) (-w) - min M (-w) ≤ A ∧
      π / 2 - L ≤ A ∧ π / 2 - M ≤ A := by
  dsimp only
  obtain ⟨e_lo, e_hi⟩ := abs_lt.mp east
  obtain ⟨w_lo, w_hi⟩ := abs_lt.mp west
  have e_open : max σ w < min (2 * δ) (e + 2 * δ - σ) := by
    apply lt_min <;> apply max_lt <;>
      linarith only [positive, sigma_le, east_margin, w_hi, cross_margin]
  have w_open : max σ (-e) < min (2 * δ) (2 * δ - w - σ) := by
    apply lt_min <;> apply max_lt <;>
      linarith only [positive, sigma_le, west_margin, e_lo, cross_margin]
  obtain ⟨L, Llo, Lhi⟩ := exists_between e_open
  obtain ⟨M, Mlo, Mhi⟩ := exists_between w_open
  have Lσ := (le_max_left σ w).trans_lt Llo
  have Lw := (le_max_right σ w).trans_lt Llo
  have Lδ := Lhi.trans_le (min_le_left (2 * δ) (e + 2 * δ - σ))
  have Le := Lhi.trans_le (min_le_right (2 * δ) (e + 2 * δ - σ))
  have Mσ := (le_max_left σ (-e)).trans_lt Mlo
  have Me := (le_max_right σ (-e)).trans_lt Mlo
  have Mδ := Mhi.trans_le (min_le_left (2 * δ) (2 * δ - w - σ))
  have Mw := Mhi.trans_le (min_le_right (2 * δ) (2 * δ - w - σ))
  have span : 0 ≤ π / 2 - σ := by linarith only [sigma_le, small, pi_pos]
  refine ⟨L, M, positive.trans Lσ, by linarith only [Lδ], positive.trans Mσ,
    by linarith only [Mδ], Lw, Me, ?_, ?_, ?_, ?_⟩
  · apply hull_width_le _ _ _ span
    · linarith only [sigma_le, positive]
    · linarith only [Le]
    · linarith only [e_hi, positive, Lσ, sigma_le, small, pi_pos]
  · apply hull_width_le _ _ _ span
    · linarith only [sigma_le, positive]
    · linarith only [Mw]
    · linarith only [w_lo, positive, Mσ, sigma_le, small, pi_pos]
  · linarith only [Lσ]
  · linarith only [Mσ]

end Unfoldings.FewestNets
