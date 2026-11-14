module

public import Unfoldings.Geometry.RadialBlockError
public import Unfoldings.Geometry.ChordRotationControl

/-! Explicit radial and length bounds from length-weighted polar-block comparisons. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error stretch variation radius : Fin n → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)
  {anchor S B C K δ : ℝ}
  (speed : 1 ≤ S) (budget : 0 ≤ B) (constant : 0 ≤ C) (angular_constant : 0 ≤ K)
  (width : 0 < δ) (lower : ∀ i, 1 ≤ stretch i) (upper : ∀ i, stretch i ≤ S)
  (variation_nonnegative : ∀ i, 0 ≤ variation i)
  (progress : ∀ j, earlierLength (fun i => ‖P.edge i‖) j ≤ C * radius j)
  (angular : ∀ j, radius j * variation j ≤ K * ‖P.edge j‖)
  (heading : ∀ i, |error i - anchor| ≤ B * (1 + futureVariation variation i / δ))
  (length_bound : P.projectedLength ≤ C * ‖P.vertex (Fin.last n) - P.vertex 0‖)

include changed speed budget constant angular_constant width lower upper variation_nonnegative
  progress angular heading length_bound

/-- The loss uses weighted block comparisons; no uniform global heading-error bound is assumed. -/
theorem radialBlock_radial_margin {d : ℝ} (small : radialBlockError S B C K δ < d) (v : ℂ)
    (margin : d * (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖v‖) ≤
      inner ℝ (P.vertex (Fin.last n) - P.vertex 0) v) :
    ((d - radialBlockError S B C K δ) / (1 + radialBlockError S B C K δ)) *
      (‖Q.vertex (Fin.last n) - Q.vertex 0‖ * ‖polarRay anchor * v‖) ≤
        inner ℝ (Q.vertex (Fin.last n) - Q.vertex 0) (polarRay anchor * v) := by
  exact radial_margin_of_aligned_chord_error anchor
    (radialBlockError_nonneg speed budget constant angular_constant width) small
    (P.radialBlock_chord_error Q error stretch changed variation radius speed budget constant
      angular_constant width lower upper variation_nonnegative
      progress angular heading length_bound)
    margin

theorem radialBlock_length_bound (small : radialBlockError S B C K δ < 1) :
    Q.projectedLength ≤ (S * C / (1 - radialBlockError S B C K δ)) *
      ‖Q.vertex (Fin.last n) - Q.vertex 0‖ := by
  have speed_nonnegative : 0 ≤ S := le_trans zero_le_one speed
  have lifted_length : Q.projectedLength ≤ (S * C) * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
    calc
      _ ≤ S * P.projectedLength := P.heading_speed_length_bound Q error stretch changed
        (fun i => le_trans zero_le_one (lower i)) upper
      _ ≤ S * (C * ‖P.vertex (Fin.last n) - P.vertex 0‖) :=
        mul_le_mul_of_nonneg_left length_bound speed_nonnegative
      _ = _ := by ring
  exact length_constant_of_aligned_chord_error anchor (mul_nonneg speed_nonnegative constant) small
    (P.radialBlock_chord_error Q error stretch changed variation radius speed budget constant
      angular_constant width lower upper variation_nonnegative
      progress angular heading length_bound)
    lifted_length

end Unfoldings.PolygonalChain
