module

public import Unfoldings.Geometry.LocalRadialBlocks
public import Unfoldings.Geometry.NextEdgeRadialBlocks
public import Mathlib.Topology.Order.OrderClosed

/-! Radial-block estimates at the limiting window width, using strict windows throughout. -/

@[expose] public section

namespace Unfoldings

open Filter Set
open scoped Topology

/-- A window width can approach its upper endpoint from below. The estimate
therefore uses the limiting width without making a topological claim about a
window of exactly that width. -/
theorem le_radialBlockError_mul_at_limit {S B C K W radius error : ℝ}
    (width : 0 < W)
    (estimate : ∀ δ ∈ Ioo 0 W, error ≤ radialBlockError S B C K δ * radius) :
    error ≤ radialBlockError S B C K W * radius := by
  have continuous : ContinuousAt (fun δ => radialBlockError S B C K δ * radius) W := by
    unfold radialBlockError
    fun_prop (disch := exact width.ne')
  apply ge_of_tendsto (continuous.continuousWithinAt (s := Iio W))
  filter_upwards [Ioo_mem_nhdsLT width] with δ hδ
  exact estimate δ hδ

namespace PolygonalChain

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

include changed speed budget constant lower upper gamma_nonnegative gamma_small margin prefix_bound
  window

/-- The complete aligned chord estimate uses the exact coefficient with
denominator π, given the local comparison for strict angular windows. -/
theorem local_window_chord_error_at_pi
    (length_bound : P.projectedLength ≤ C * ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖) :
    ‖polarRay (-error (Fin.last n)) * (Q.vertex (Fin.last (n + 1)) - Q.vertex 0) -
      (P.vertex (Fin.last (n + 1)) - P.vertex 0)‖ ≤
        radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) Real.pi *
          ‖P.vertex (Fin.last (n + 1)) - P.vertex 0‖ := by
  apply le_radialBlockError_mul_at_limit Real.pi_pos
  intro δ hδ
  exact P.local_window_chord_error Q source error stretch changed speed budget constant hδ.1
    lower upper gamma_nonnegative gamma_small margin prefix_bound
    (fun i j ordered h => window i j ordered (h.trans hδ.2)) length_bound

/-- The exact coefficient also applies to the chord aligned with a final outgoing edge. -/
theorem next_edge_chord_error_at_pi
    (length_bound : (P.interval 0 n (initial_interval_fits (Fin.last n).castSucc)).projectedLength ≤
      C * ‖P.vertex (Fin.last n).castSucc - P.vertex 0‖) :
    ‖polarRay (-error (Fin.last n)) * (Q.vertex (Fin.last n).castSucc - Q.vertex 0) -
      (P.vertex (Fin.last n).castSucc - P.vertex 0)‖ ≤
        radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) Real.pi *
          ‖P.vertex (Fin.last n).castSucc - P.vertex 0‖ := by
  apply le_radialBlockError_mul_at_limit Real.pi_pos
  intro δ hδ
  exact P.next_edge_chord_error Q source error stretch changed speed budget constant hδ.1
    lower upper gamma_nonnegative gamma_small margin prefix_bound
    (fun i j ordered h => window i j ordered (h.trans hδ.2)) length_bound

end PolygonalChain
end Unfoldings
