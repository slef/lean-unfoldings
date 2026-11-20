module

public import Unfoldings.Geometry.HeadingSubhistoryMargin

/-! Uniform heading errors preserve radial monotonicity of every actual subchain. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error : Fin n → ℝ)
  (rotated : ∀ i, Q.edge i = polarRay (error i) * P.edge i)

include rotated in
/-- Every earlier anchor is controlled by the same constants, independently of mesh size. -/
theorem outward_of_heading_oscillation {ε D d : ℝ} (epsilon : 0 ≤ ε) (constant : 0 ≤ D)
    (small : D * ε < d) (oscillation : ∀ i j, |error i - error j| ≤ ε)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (P.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖P.vertex i.castSucc - P.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i)) : Q.Outward := by
  intro j i earlier
  have estimate := P.radial_margin_of_heading_oscillation Q error rotated epsilon constant
    small oscillation length_bound margin j i earlier
  have coefficient : 0 ≤ (d - D * ε) / (1 + D * ε) :=
    div_nonneg (sub_pos.mpr small).le (by nlinarith [mul_nonneg constant epsilon])
  exact (mul_nonneg coefficient (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate

end Unfoldings.PolygonalChain
