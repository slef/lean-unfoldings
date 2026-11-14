module

public import Unfoldings.Convex.CommonPotential
public import Unfoldings.Geometry.AnnularRadialMargin

/-! The annular radial margin applies to any whole incoming path with common-potential progress. -/

@[expose] public section

namespace Unfoldings.SlopeEnvelope

variable (E : SlopeEnvelope)

theorem annular_history_radial_margin {a b β ζ length : ℝ}
    (positive : 0 < a) (bpos : 0 < b) (ratio : a ≤ b) (beta : 0 ≤ β) (acute : β < Real.pi / 2)
    (bounded : ∀ p ∈ E.slopes, ‖p‖ ≤ b)
    (sector : Real.tan β < a / b) (zeta : 0 ≤ ζ)
    (exterior : annularHistoryAngle (a / b) β + ζ < Real.pi / 2)
    {x y p edge : Plane} (active : E.Active x p) (pne : p ≠ 0) (different : x ≠ y)
    (edge_ne : edge ≠ 0)
    (progress : (a * Real.cos β) * length ≤ E.height x - E.height y)
    (chord : ‖x - y‖ ≤ length)
    (close : InnerProductGeometry.angle p edge ≤ β ∨ InnerProductGeometry.angle p edge ≤ ζ) :
    annularRadialMargin (a / b) β ζ * (‖x - y‖ * ‖edge‖) ≤ inner ℝ (x - y) edge := by
  have nonnegative : 0 ≤ a * Real.cos β :=
    mul_nonneg positive.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], acute.le⟩)
  have coefficient : a * Real.cos β ≤ b :=
    (mul_le_of_le_one_right positive.le (Real.cos_le_one β)).trans ratio
  have expression : (a * Real.cos β) / b = (a / b) * Real.cos β := by ring
  have sector_bound := annular_history_angle_sector (div_pos positive bpos)
    ((div_le_one bpos).mpr ratio) beta acute sector
  have finish (δ : ℝ) (delta : 0 ≤ δ)
      (small : annularHistoryAngle (a / b) β + δ < Real.pi / 2)
      (angle : InnerProductGeometry.angle p edge ≤ δ)
      (margin : annularRadialMargin (a / b) β ζ ≤
        Real.cos (annularHistoryAngle (a / b) β + δ)) :
      annularRadialMargin (a / b) β ζ * (‖x - y‖ * ‖edge‖) ≤ inner ℝ (x - y) edge := by
    have bound := E.history_radial_margin bpos nonnegative coefficient bounded active pne different
      edge_ne progress chord angle delta (by
        rw [expression]
        change annularHistoryAngle (a / b) β + δ ≤ Real.pi
        linarith [Real.pi_pos])
    rw [expression] at bound
    exact (mul_le_mul_of_nonneg_right margin
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans bound
  rcases close with close | close
  · apply finish β beta (by linarith) close
    exact (min_le_left _ _).trans_eq (by rw [add_comm])
  · exact finish ζ zeta exterior close (min_le_right _ _)

end Unfoldings.SlopeEnvelope
