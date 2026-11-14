module

public import Unfoldings.Geometry.HeadingSpeedError
public import Unfoldings.Geometry.WeightedHeadingBudget

/-! Quantitative radial-block chord control allows long polar winding and variable lifted speeds. -/

@[expose] public section

namespace Unfoldings

/-- Speed distortion plus the length-weighted cost of successive polar blocks. -/
noncomputable def radialBlockError (S B C K δ : ℝ) : ℝ :=
  C * (S - 1) + S * B * C * (1 + C * K / δ)

theorem radialBlockError_nonneg {S B C K δ : ℝ} (speed : 1 ≤ S) (budget : 0 ≤ B)
    (constant : 0 ≤ C) (angular : 0 ≤ K) (width : 0 < δ) :
    0 ≤ radialBlockError S B C K δ := by
  unfold radialBlockError
  exact add_nonneg (mul_nonneg constant (sub_nonneg.mpr speed))
    (mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one speed) budget) constant)
      (by positivity))

namespace PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error stretch : Fin n → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)

include changed in
/-- The heading bound may grow with future polar variation; its weighted chord cost stays small. -/
theorem radialBlock_chord_error (variation radius : Fin n → ℝ) {anchor S B C K δ : ℝ}
    (speed : 1 ≤ S) (budget : 0 ≤ B) (constant : 0 ≤ C) (angular_constant : 0 ≤ K)
    (width : 0 < δ) (lower : ∀ i, 1 ≤ stretch i) (upper : ∀ i, stretch i ≤ S)
    (variation_nonnegative : ∀ i, 0 ≤ variation i)
    (progress : ∀ j, earlierLength (fun i => ‖P.edge i‖) j ≤ C * radius j)
    (angular : ∀ j, radius j * variation j ≤ K * ‖P.edge j‖)
    (heading : ∀ i, |error i - anchor| ≤ B * (1 + futureVariation variation i / δ))
    (length_bound : P.projectedLength ≤ C * ‖P.vertex (Fin.last n) - P.vertex 0‖) :
    ‖polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0)‖ ≤
        radialBlockError S B C K δ * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
  have weighted := weighted_heading_budget (fun i => ‖P.edge i‖) variation radius
    (fun i => |error i - anchor|) constant budget width (fun _ => norm_nonneg _)
    variation_nonnegative progress angular heading
  have weighted' : (∑ i, |error i - anchor| * ‖P.edge i‖) ≤
      B * (1 + C * K / δ) * P.projectedLength := by
    simpa only [projectedLength, mul_comm] using weighted
  have nonnegative_speed : 0 ≤ S := le_trans zero_le_one speed
  have heading_constant : 0 ≤ B * (1 + C * K / δ) := by positivity
  have coefficient : 0 ≤ (S - 1) + S * (B * (1 + C * K / δ)) :=
    add_nonneg (sub_nonneg.mpr speed) (mul_nonneg nonnegative_speed heading_constant)
  calc
    _ ≤ (S - 1) * P.projectedLength + S * ∑ i, |error i - anchor| * ‖P.edge i‖ :=
      P.heading_speed_chord_error Q error stretch changed lower upper
    _ ≤ (S - 1) * P.projectedLength + S *
        (B * (1 + C * K / δ) * P.projectedLength) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left weighted' nonnegative_speed)
    _ = ((S - 1) + S * (B * (1 + C * K / δ))) * P.projectedLength := by ring
    _ ≤ ((S - 1) + S * (B * (1 + C * K / δ))) *
        (C * ‖P.vertex (Fin.last n) - P.vertex 0‖) :=
      mul_le_mul_of_nonneg_left length_bound coefficient
    _ = _ := by unfold radialBlockError; ring

end PolygonalChain
end Unfoldings
