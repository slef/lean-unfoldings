module

public import Unfoldings.Roof.NormalRibbonTransport

/-! Determining which side of the normal trace contains a vertex polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope

open Real

/-- If a vertex is strictly above or below a horizontal closing link, the
interior of its slope polygon lies strictly to the same side of the trace
whenever their first slope coordinates agree. -/
theorem active_interior_normal_trace_sign (E : SlopeEnvelope) {x y p q : Plane}
    {polygon : Set Plane} (trace : E.Active x p)
    (active : ∀ z ∈ polygon, E.Active y z) (inside : q ∈ interior polygon)
    (horizontal : p 0 = q 0) (off_link : x 1 ≠ y 1) :
    (0 < y 1 - x 1 ∧ 0 < q 1 - p 1) ∨ (y 1 - x 1 < 0 ∧ q 1 - p 1 < 0) := by
  obtain ⟨r, rp, ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
  let e : Plane := PiLp.single 2 (1 : Fin 2) (1 : ℝ)
  have unit : ‖e‖ = 1 := by
    dsimp only [e]
    rw [PiLp.norm_single, norm_one]
  have fiber (s : ℝ) (near : |s| < r) : q + s • e ∈ polygon := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, unit, mul_one, Real.norm_eq_abs]
    exact near
  have first (s : ℝ) : (q + s • e) 0 = q 0 := by
    simp [e]
  have last (s : ℝ) : (q + s • e) 1 = q 1 + s := by
    simp [e]
  have mid := half_pos rp
  rcases lt_or_gt_of_ne off_link with above | below
  · have near : |-(r / 2)| < r := by
      rw [abs_neg, abs_of_pos mid]
      linarith only [rp]
    have inequality := E.active_secondCoord_le trace (active _ (fiber _ near))
      ((first _).symm ▸ horizontal) above
    rw [last] at inequality
    exact Or.inl ⟨sub_pos.mpr above, by linarith only [inequality, mid]⟩
  · have near : |r / 2| < r := by
      rw [abs_of_pos mid]
      linarith only [rp]
    have inequality := E.active_secondCoord_le (active _ (fiber _ near)) trace
      ((first _).trans horizontal.symm) below
    rw [last] at inequality
    exact Or.inr ⟨sub_neg.mpr below, by linarith only [inequality, mid]⟩

/-- The signed vertex charge and winding have the same sign. The trace may be
at any physical position on the chosen horizontal line. -/
theorem vertex_charge_mul_winding_nonneg (E : SlopeEnvelope) {x y p q : Plane}
    {polygon : Set Plane} (trace_active : E.Active x p)
    (vertex_active : ∀ z ∈ polygon, E.Active y z) (inside : q ∈ interior polygon)
    {trace chord : ℝ → ℝ} (trace_first : p 0 = q 0) (trace_second : p 1 = trace (q 0))
    {a b weight : ℝ} (off_link : x 1 ≠ y 1)
    (sign : 0 ≤ (y 1 - x 1) * weight) :
    0 ≤ weight * normalRibbonWinding trace chord a b (Cap.planeCartesian q) := by
  rcases E.active_interior_normal_trace_sign trace_active vertex_active inside trace_first off_link
    with ⟨above, p_above⟩ | ⟨below, p_below⟩
  · have positive := nonneg_of_mul_nonneg_right sign above
    have wind : 0 ≤ normalRibbonWinding trace chord a b (Cap.planeCartesian q) := by
      apply normalRibbonWinding_nonneg_of_above
      simpa only [Cap.planeCartesian_apply, ← trace_second] using sub_pos.mp p_above
    exact mul_nonneg positive wind
  · have negative := nonpos_of_mul_nonneg_right sign below
    have wind : normalRibbonWinding trace chord a b (Cap.planeCartesian q) ≤ 0 := by
      apply normalRibbonWinding_nonpos_of_below
      simpa only [Cap.planeCartesian_apply, ← trace_second] using (sub_neg.mp p_below).le
    exact mul_nonneg_of_nonpos_of_nonpos negative wind

end Unfoldings.SlopeEnvelope
