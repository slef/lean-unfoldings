module

public import Unfoldings.Geometry.AffineConeBounds
public import Unfoldings.Geometry.RobustQuadrant
public import Mathlib.Tactic.FinCases

/-! A numerical angular neighborhood of the identity implies all four affine axis tests. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def affineTestAxis : Fin 4 → ℂ := ![1 + Complex.I, 1 - Complex.I,
  1 + Complex.I, -1 + Complex.I]

def affineTestRay : Fin 4 → ℂ := ![1, 1, Complex.I, Complex.I]

theorem affine_test_inner_pos (j : Fin 4) :
    0 < inner ℝ (affineTestAxis j) (affineTestRay j) := by
  fin_cases j <;> norm_num [affineTestAxis, affineTestRay, Complex.inner]

theorem affineAxisMargins_eq_inner (A : ℂ →ᵃ[ℝ] ℂ) (j : Fin 4) :
    affineAxisMargins A j = inner ℝ (affineTestAxis j) (A.linear (affineTestRay j)) := by
  fin_cases j <;> simp [affineAxisMargins, affineTestAxis, affineTestRay, Complex.inner,
    sub_eq_add_neg, add_comm]

/-- One positive numerical tolerance works for every affine map and every orthogonal coordinate
frame. No metric scale or face count enters this angular threshold. -/
theorem exists_affine_axis_angle_threshold :
    ∃ δ > 0, ∀ A : ℂ →ᵃ[ℝ] ℂ,
      InnerProductGeometry.angle (1 : ℂ) (A.linear 1) < δ →
      InnerProductGeometry.angle Complex.I (A.linear Complex.I) < δ →
      ∀ j, 0 < affineAxisMargins A j := by
  let slack (j : Fin 4) := Real.pi / 2 -
    InnerProductGeometry.angle (affineTestAxis j) (affineTestRay j)
  have positive (j : Fin 4) : 0 < slack j := by
    apply sub_pos.mpr
    by_contra wide
    exact (not_le_of_gt (affine_test_inner_pos j))
      (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr (le_of_not_gt wide))
  obtain ⟨j, minimal⟩ := Finite.exists_min slack
  refine ⟨slack j, positive j, fun A first last k => ?_⟩
  rw [affineAxisMargins_eq_inner]
  have close : InnerProductGeometry.angle (affineTestRay k)
      (A.linear (affineTestRay k)) < slack j := by
    fin_cases k
    · exact first
    · exact first
    · exact last
    · exact last
  have bound := minimal k
  change slack j ≤ Real.pi / 2 -
    InnerProductGeometry.angle (affineTestAxis k) (affineTestRay k) at bound
  exact inner_pos_of_angle_close le_rfl close (by linarith)

end Unfoldings
