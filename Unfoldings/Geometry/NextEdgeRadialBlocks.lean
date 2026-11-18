module

public import Unfoldings.Geometry.EndpointHeadingBudget
public import Unfoldings.Geometry.ChainPolarVariation
public import Unfoldings.Geometry.RadialBlockBounds

/-! Weighted rolling estimates align each actual prefix with its next outgoing edge. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

/-- Every earlier vertex gives a valid initial interval, with an exportable arithmetic proof. -/
theorem initial_interval_fits {N : ℕ} (j : Fin (N + 1)) : 0 + j.val ≤ N := by omega

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
  (length_bound : (P.interval 0 n (initial_interval_fits (Fin.last n).castSucc)).projectedLength ≤
    C * ‖P.vertex (Fin.last n).castSucc - P.vertex 0‖)

include changed speed budget constant width lower upper gamma_nonnegative gamma_small margin
  prefix_bound window length_bound

/-- The outgoing edge fixes the frame but adds no length or angular weight to the prefix. -/
theorem next_edge_chord_error :
    ‖polarRay (-error (Fin.last n)) * (Q.vertex (Fin.last n).castSucc - Q.vertex 0) -
      (P.vertex (Fin.last n).castSucc - P.vertex 0)‖ ≤
        radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ *
          ‖P.vertex (Fin.last n).castSucc - P.vertex 0‖ := by
  let A : PolygonalChain ℂ n := ⟨fun j => P.vertex j.castSucc⟩
  let D : PolygonalChain ℂ n := ⟨fun j => Q.vertex j.castSucc⟩
  apply A.radialBlock_chord_error D
    (fun i => error i.castSucc) (fun i => stretch i.castSucc)
    (fun i => changed i.castSucc)
    (fun i => P.polarVariation source i.castSucc)
    (fun i => ‖P.vertex i.castSucc.castSucc - source‖)
    speed budget constant (Real.sqrt_nonneg (1 - γ ^ 2)) width
    (fun i => lower i.castSucc) (fun i => upper i.castSucc)
    (fun i => P.polarVariation_nonnegative source i.castSucc)
  · intro j
    rw [A.earlierLength_eq_interval_length]
    simpa only [A, interval, Nat.zero_add, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Fin.val_zero, Fin.mk_zero] using prefix_bound j.castSucc
  · intro j
    exact P.polarVariation_weighted_bound source gamma_nonnegative gamma_small j.castSucc
      (margin j.castSucc)
  · intro i
    exact abs_heading_sub_next_le_weighted_local_budget error (P.polarVariation source)
      budget width (P.polarVariation_nonnegative source) window i
  · simpa only [A, interval, Nat.zero_add, Fin.castSucc, Fin.castAdd, Fin.castLE,
      Fin.val_zero, Fin.mk_zero] using length_bound

/-- A physical prefix margin against its next tangent survives rolling with an explicit loss. -/
theorem next_edge_rotated_radial_margin {d : ℝ}
    (small : radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ < d)
    (endpoint_margin : d * (‖P.vertex (Fin.last n).castSucc - P.vertex 0‖ *
      ‖P.edge (Fin.last n)‖) ≤
        inner ℝ (P.vertex (Fin.last n).castSucc - P.vertex 0) (P.edge (Fin.last n))) :
    ((d - radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ) /
      (1 + radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ)) *
      (‖Q.vertex (Fin.last n).castSucc - Q.vertex 0‖ *
        ‖polarRay (error (Fin.last n)) * P.edge (Fin.last n)‖) ≤
      inner ℝ (Q.vertex (Fin.last n).castSucc - Q.vertex 0)
        (polarRay (error (Fin.last n)) * P.edge (Fin.last n)) :=
  radial_margin_of_aligned_chord_error _
    (radialBlockError_nonneg speed budget constant (Real.sqrt_nonneg _) width) small
    (P.next_edge_chord_error Q source error stretch changed speed budget constant width lower upper
      gamma_nonnegative gamma_small margin prefix_bound window length_bound) endpoint_margin

/-- Positive edge stretching preserves the margin against the actual lifted outgoing edge. -/
theorem next_edge_radial_margin {d : ℝ}
    (small : radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ < d)
    (endpoint_margin : d * (‖P.vertex (Fin.last n).castSucc - P.vertex 0‖ *
      ‖P.edge (Fin.last n)‖) ≤
        inner ℝ (P.vertex (Fin.last n).castSucc - P.vertex 0) (P.edge (Fin.last n))) :
    ((d - radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ) /
      (1 + radialBlockError S B C (Real.sqrt (1 - γ ^ 2)) δ)) *
      (‖Q.vertex (Fin.last n).castSucc - Q.vertex 0‖ * ‖Q.edge (Fin.last n)‖) ≤
      inner ℝ (Q.vertex (Fin.last n).castSucc - Q.vertex 0) (Q.edge (Fin.last n)) := by
  have estimate := P.next_edge_rotated_radial_margin Q source error stretch changed speed budget
    constant width lower upper gamma_nonnegative gamma_small margin prefix_bound window
    length_bound small endpoint_margin
  have nonnegative : 0 ≤ stretch (Fin.last n) := zero_le_one.trans (lower _)
  have next : Q.edge (Fin.last n) = stretch (Fin.last n) •
      (polarRay (error (Fin.last n)) * P.edge (Fin.last n)) := by
    rw [changed, Complex.real_smul, mul_assoc]
  rw [next, norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative, inner_smul_right]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left estimate nonnegative

end Unfoldings.PolygonalChain
