module

public import Unfoldings.Cap.OpenedBanks
public import Unfoldings.Geometry.BankRadialOrder

/-!
# Equal-radius order of opened banks in a common quadrant

This proves the circle comparison needed in the strict acute-wedge case,
including finite endpoints and contacts. It does not claim the paper's broader
radial-monotonicity theorem for chains outside a common quadrant.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap.QuadrantBanks

variable {n : ℕ} {L R : PolygonalChain ℂ n} (B : QuadrantBanks L R)

include B

theorem left_horizontal (i : Fin n) : 0 < (L.edge i).re := by
  rw [B.left_edge]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, polarRay_re]
  exact mul_pos (B.positive_length i)
    (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [(B.left_bounds i).1, Real.pi_pos], (B.left_bounds i).2⟩)

theorem left_vertical (i : Fin n) : 0 ≤ (L.edge i).im :=
  (B.right_vertical i).trans (B.vertical_increments i)

/-- At equal radii, the left point is above and to the left of the right point. -/
theorem radial_order (i j : Fin n) (t s : unitInterval)
    (same_radius : dist (L.vertex 0) (L.point i t) = dist (R.vertex 0) (R.point j s)) :
    (L.point i t - L.vertex 0).re ≤ (R.point j s - R.vertex 0).re ∧
      (R.point j s - R.vertex 0).im ≤ (L.point i t - L.vertex 0).im := by
  have lxn := L.linear_origin_le_point Complex.reCLM.toLinearMap
    (fun k => (B.left_horizontal k).le) i t
  have lyn := L.linear_origin_le_point Complex.imCLM.toLinearMap B.left_vertical i t
  have rxn := R.linear_origin_le_point Complex.reCLM.toLinearMap
    (fun k => (B.right_horizontal k).le) j s
  have ryn := R.linear_origin_le_point Complex.imCLM.toLinearMap B.right_vertical j s
  have alternative := L.left_or_above_of_increments R Complex.reCLM.toLinearMap
    Complex.imCLM.toLinearMap B.start B.horizontal_increments B.vertical_increments
    (fun k => (B.right_horizontal k).le) B.right_vertical i j t s
  let a := L.point i t - L.vertex 0
  let b := R.point j s - R.vertex 0
  have radius : a.re ^ 2 + a.im ^ 2 = b.re ^ 2 + b.im ^ 2 := by
    have identity (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have equal : ‖a‖ = ‖b‖ := by simpa only [dist_eq_norm'] using same_radius
    rw [← identity, ← identity, equal]
  have relative : a.re ≤ b.re ∨ b.im ≤ a.im := by
    rcases alternative with horizontal | vertical
    · left
      change (L.point i t).re - (L.vertex 0).re ≤ (R.point j s).re - (R.vertex 0).re
      rw [B.start]
      exact sub_le_sub_right horizontal _
    · right
      change (R.point j s).im - (R.vertex 0).im ≤ (L.point i t).im - (L.vertex 0).im
      rw [B.start]
      exact sub_le_sub_right vertical _
  exact quadrant_circle_order (sub_nonneg.mpr lxn) (sub_nonneg.mpr lyn)
    (sub_nonneg.mpr rxn) (sub_nonneg.mpr ryn) radius relative

end Unfoldings.Cap.QuadrantBanks
