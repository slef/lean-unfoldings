module

public import Unfoldings.Geometry.PolygonalLength
public import Unfoldings.Cone.Sector
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Real heading errors control the chord error of a chain after alignment at one heading. -/

@[expose] public section

namespace Unfoldings

theorem norm_polarRay_sub_one_le (θ : ℝ) : ‖polarRay θ - 1‖ ≤ |θ| := by
  simpa only [polarRay, Circle.coe_exp, mul_comm, Real.norm_eq_abs] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)

namespace PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error : Fin n → ℝ)
  (rotated : ∀ i, Q.edge i = polarRay (error i) * P.edge i)

include rotated in
theorem projectedLength_eq_of_rotated_edges : Q.projectedLength = P.projectedLength := by
  apply Finset.sum_congr rfl
  intro i _
  rw [rotated, norm_mul, norm_polarRay, one_mul]

include rotated in
/-- The anchor can be the outgoing tangent's error, beyond the subpath whose chord is estimated. -/
theorem heading_chord_error {anchor ε : ℝ} (bound : ∀ i, |error i - anchor| ≤ ε) :
    ‖polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0)‖ ≤ ε * P.projectedLength := by
  have sum_equal : polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0) =
        ∑ i, (polarRay (error i - anchor) - 1) * P.edge i := by
    rw [← Q.sum_edge, ← P.sum_edge, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [rotated, ← mul_assoc, ← polarRay_add]
    have phase : -anchor + error i = error i - anchor := by ring
    rw [phase]
    ring
  rw [sum_equal]
  calc
    _ ≤ ∑ i, ‖(polarRay (error i - anchor) - 1) * P.edge i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε * ‖P.edge i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_polarRay_sub_one_le _).trans (bound i))
        (norm_nonneg _)
    _ = ε * P.projectedLength := (Finset.mul_sum _ _ _).symm

end PolygonalChain
end Unfoldings
