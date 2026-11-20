module

public import Unfoldings.Geometry.LocalHeadingBudget
public import Unfoldings.Geometry.NextEdgeRadialBlocks

/-!
# Radial estimates from genuine local bank comparisons

Actual edge polar variations supply the angular weights. The finite window
argument derives the required heading budget, allowing arbitrarily long polar
winding; no global bound on the real heading discrepancy is an input.
-/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ (n + 1)) (source : ℂ)
  (error stretch : Fin (n + 1) → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)
  {S B C δ γ : ℝ} (speed : 1 ≤ S) (budget : 0 ≤ B) (constant : 0 ≤ C) (width : 0 < δ)
  (lower : ∀ i, 1 ≤ stretch i) (upper : ∀ i, stretch i ≤ S)
  (gamma_nonnegative : 0 ≤ γ) (gamma_small : γ ≤ 1)
  (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
    inner ℝ (P.vertex i.castSucc - source) (P.edge i))
  (prefix_bound : ∀ j : Fin (n + 1),
    (P.interval 0 j.val (initial_interval_fits j.castSucc)).projectedLength ≤
      C * ‖P.vertex j.castSucc - source‖)
  (window : ∀ i j, i ≤ j → interiorVariation (P.polarVariation source) i j < δ →
    |error i - error j| ≤ B)
  (length_bound : P.projectedLength ≤ C * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖)

include changed speed budget constant width lower upper gamma_nonnegative gamma_small margin
  prefix_bound window length_bound

/-- Local polar windows imply the actual aligned chord estimate used in bank opening. -/
theorem local_window_chord_error :
    ‖polarRay (-error (Fin.last n)) * (Q.vertex (Fin.last (n + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (n + 1)) - P.vertex 0)‖ ≤
        radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ *
          ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
  apply P.radialBlock_chord_error Q error stretch changed (P.polarVariation source)
    (fun i => ‖P.vertex i.castSucc - source‖) speed budget constant (Real.sqrt_nonneg _) width
    lower upper (P.polarVariation_nonnegative source)
  · intro j
    rw [P.earlierLength_eq_interval_length]
    exact prefix_bound j
  · intro j
    exact P.polarVariation_weighted_bound source gamma_nonnegative gamma_small j (margin j)
  · intro i
    exact abs_heading_sub_le_weighted_local_budget error (P.polarVariation source) budget width
      (P.polarVariation_nonnegative source) window (Fin.last n) i (Fin.le_last i)
  · exact length_bound

/-- Actual local window comparisons preserve radial progress with an explicit mesh-free loss. -/
theorem local_window_radial_margin {d : ℝ}
    (small : radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ < d) (v : ℂ)
    (endpoint_margin : d * (‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ * ‖v‖) ≤
      inner ℝ (P.vertex (Fin.last (n + 1)) - P.vertex 0) v) :
    ((d - radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ) /
      (1 + radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ)) *
      (‖Q.vertex (Fin.last (n + 1)) - Q.vertex 0‖ * ‖polarRay (error (Fin.last n)) * v‖) ≤
        inner ℝ (Q.vertex (Fin.last (n + 1)) - Q.vertex 0)
          (polarRay (error (Fin.last n)) * v) :=
  radial_margin_of_aligned_chord_error _
    (radialBlockError_nonneg speed budget constant (Real.sqrt_nonneg _) width) small
    (P.local_window_chord_error Q source error stretch changed speed budget constant width
      lower upper gamma_nonnegative gamma_small margin prefix_bound window length_bound)
    endpoint_margin

/-- The same local comparisons give the actual lifted bank's length-to-chord bound. -/
theorem local_window_length_bound
    (small : radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ < 1) :
    Q.projectedLength ≤
      (S * C / (1 - radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ)) *
        ‖Q.vertex (Fin.last (n + 1)) - Q.vertex 0‖ := by
  have speed_nonnegative : 0 ≤ S := zero_le_one.trans speed
  have lifted : Q.projectedLength ≤ (S * C) *
      ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
    calc
      _ ≤ S * P.projectedLength := P.heading_speed_length_bound Q error stretch changed
        (fun i => zero_le_one.trans (lower i)) upper
      _ ≤ S * (C * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖) :=
        mul_le_mul_of_nonneg_left length_bound speed_nonnegative
      _ = _ := by ring
  exact length_constant_of_aligned_chord_error _ (mul_nonneg speed_nonnegative constant) small
    (P.local_window_chord_error Q source error stretch changed speed budget constant width
      lower upper gamma_nonnegative gamma_small margin prefix_bound window length_bound) lifted

end Unfoldings.PolygonalChain
