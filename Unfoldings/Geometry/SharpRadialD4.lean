module

public import Unfoldings.Geometry.RadialBlockLimit

/-! The sharp limiting development estimate preserves radial and length margins. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ (n + 1)) (source : ℂ)
  (error stretch : Fin (n + 1) → ℝ)
  (changed : ∀ i, Q.edge i = (stretch i : ℂ) * polarRay (error i) * P.edge i)
  {S B C γ : ℝ} (speed : 1 ≤ S) (budget : 0 ≤ B) (constant : 0 ≤ C)
  (lower : ∀ i, 1 ≤ stretch i) (upper : ∀ i, stretch i ≤ S)
  (gamma_nonnegative : 0 ≤ γ) (gamma_small : γ ≤ 1)
  (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
    inner ℝ (P.vertex i.castSucc - source) (P.edge i))
  (prefix_bound : ∀ j : Fin (n + 1),
    (P.interval 0 j.val (initial_interval_fits j.castSucc)).projectedLength ≤
      C * ‖P.vertex j.castSucc - source‖)
  (window : ∀ i j, i ≤ j → interiorVariation (P.polarVariation source) i j < Real.pi →
    |error i - error j| ≤ B)

local notation "E" => radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) Real.pi

include changed speed budget constant lower upper gamma_nonnegative gamma_small margin prefix_bound
  window

/-- The endpoint chord has the exact radial margin and length-to-chord ratio
from windows strictly shorter than a half-turn. -/
theorem sharp_developed_chord_margins
    (length_bound : P.projectedLength ≤ C * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖)
    (small : E < γ) (v : ℂ)
    (endpoint_margin : γ * (‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ * ‖v‖) ≤
      inner ℝ (P.vertex (Fin.last (n + 1)) - P.vertex 0) v) :
    ((γ - E) / (1 + E)) *
      (‖Q.vertex (Fin.last (n + 1)) - Q.vertex 0‖ * ‖polarRay (error (Fin.last n)) * v‖) ≤
        inner ℝ (Q.vertex (Fin.last (n + 1)) - Q.vertex 0)
          (polarRay (error (Fin.last n)) * v) ∧
      Q.projectedLength ≤ (S * C / (1 - E)) *
        ‖Q.vertex (Fin.last (n + 1)) - Q.vertex 0‖ := by
  have chord := P.local_window_chord_error_at_pi Q source error stretch changed
    speed budget constant lower upper gamma_nonnegative gamma_small margin prefix_bound window
    length_bound
  have nonnegative := radialBlockError_nonneg speed budget constant (Real.sqrt_nonneg (1 - γ ^ 2)) Real.pi_pos
  refine ⟨radial_margin_of_aligned_chord_error _ nonnegative small chord endpoint_margin, ?_⟩
  have speed_nonnegative : 0 ≤ S := zero_le_one.trans speed
  have lifted : Q.projectedLength ≤ (S * C) *
      ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := calc
    _ ≤ S * P.projectedLength := P.heading_speed_length_bound Q error stretch changed
      (fun i => zero_le_one.trans (lower i)) upper
    _ ≤ S * (C * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖) :=
      mul_le_mul_of_nonneg_left length_bound speed_nonnegative
    _ = _ := by ring
  exact length_constant_of_aligned_chord_error _ (mul_nonneg speed_nonnegative constant)
    (small.trans_le gamma_small) chord lifted

/-- Align a prefix chord with the next developed edge and retain a positive
radial margin using the same limiting coefficient. -/
theorem sharp_next_edge_radial_margin
    (length_bound : (P.interval 0 n (initial_interval_fits (Fin.last n).castSucc)).projectedLength ≤
      C * ‖P.vertex (Fin.last n).castSucc - P.vertex 0‖)
    (small : E < γ)
    (endpoint_margin : γ * (‖P.vertex (Fin.last n).castSucc - P.vertex 0‖ *
      ‖P.edge (Fin.last n)‖) ≤
        inner ℝ (P.vertex (Fin.last n).castSucc - P.vertex 0) (P.edge (Fin.last n))) :
    ((γ - E) / (1 + E)) *
      (‖Q.vertex (Fin.last n).castSucc - Q.vertex 0‖ * ‖Q.edge (Fin.last n)‖) ≤
      inner ℝ (Q.vertex (Fin.last n).castSucc - Q.vertex 0) (Q.edge (Fin.last n)) := by
  have chord := P.next_edge_chord_error_at_pi Q source error stretch changed speed budget
    constant lower upper gamma_nonnegative gamma_small margin prefix_bound window length_bound
  have nonnegative := radialBlockError_nonneg speed budget constant (Real.sqrt_nonneg (1 - γ ^ 2)) Real.pi_pos
  have rotated := radial_margin_of_aligned_chord_error _ nonnegative small chord endpoint_margin
  have scale : 0 ≤ stretch (Fin.last n) := zero_le_one.trans (lower _)
  have next : Q.edge (Fin.last n) = stretch (Fin.last n) •
      (polarRay (error (Fin.last n)) * P.edge (Fin.last n)) := by
    rw [changed, Complex.real_smul, mul_assoc]
  rw [next, norm_smul, Real.norm_eq_abs, abs_of_nonneg scale, inner_smul_right]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left rotated scale

end Unfoldings.PolygonalChain
