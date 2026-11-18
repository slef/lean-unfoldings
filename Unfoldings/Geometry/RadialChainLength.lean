module

public import Unfoldings.Geometry.RadialChainProgress
public import Unfoldings.Geometry.ChainInterval

/-! Radial margins derive all physical prefix and length-to-chord bounds directly. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (source : E) {γ : ℝ}

/-- Summing the actual radial gain bounds the entire polygonal length. -/
theorem radial_projectedLength_progress (small : γ ≤ 1)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) :
    γ * P.projectedLength ≤ ‖P.vertex (Fin.last n) - source‖ - ‖P.vertex 0 - source‖ :=
  P.potential_progress (fun p => ‖p - source‖) (P.radial_edge_norm_progress source small margin)

/-- Every positive radial chain has length-to-chord constant the reciprocal of its margin. -/
theorem radial_projectedLength_le_chord (positive : 0 < γ) (small : γ ≤ 1)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) :
    P.projectedLength ≤ γ⁻¹ * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
  have progress := P.radial_projectedLength_progress source small margin
  have bound : ‖P.vertex (Fin.last n) - source‖ - ‖P.vertex 0 - source‖ ≤
      ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
    have triangle := norm_sub_norm_le (P.vertex (Fin.last n) - source) (P.vertex 0 - source)
    have equal : P.vertex (Fin.last n) - source - (P.vertex 0 - source) =
        P.vertex (Fin.last n) - P.vertex 0 := by abel
    rwa [equal] at triangle
  calc
    _ = γ⁻¹ * (γ * P.projectedLength) := by
      rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (progress.trans bound) (inv_nonneg.mpr positive.le)

/-- Every actual consecutive subchain inherits the original pointwise radial margin. -/
theorem interval_radial_margin (first length : ℕ) (fits : first + length ≤ n)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) (j : Fin length) :
    γ * (‖(P.interval first length fits).vertex j.castSucc - source‖ *
      ‖(P.interval first length fits).edge j‖) ≤
      inner ℝ ((P.interval first length fits).vertex j.castSucc - source)
        ((P.interval first length fits).edge j) :=
  margin ⟨first + j.val, by have bound := j.isLt; omega⟩

/-- Initial prefixes require no supplied metric length certificate. -/
theorem radial_prefix_projectedLength (positive : 0 < γ) (small : γ ≤ 1)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) (j : Fin (n + 1)) :
    (P.interval 0 j.val (by omega)).projectedLength ≤ γ⁻¹ * ‖P.vertex j - source‖ := by
  let A := P.interval 0 j.val (by omega)
  have progress := A.radial_projectedLength_progress source small
    (P.interval_radial_margin source 0 j.val (by omega) margin)
  have endpoint : A.vertex (Fin.last j.val) = P.vertex j :=
    (P.interval_last 0 j.val (by omega)).trans
      (congrArg P.vertex (Fin.ext (Nat.zero_add j.val)))
  have upper : γ * A.projectedLength ≤ ‖P.vertex j - source‖ := by
    rw [endpoint] at progress
    exact progress.trans (sub_le_self _ (norm_nonneg _))
  calc
    _ = γ⁻¹ * (γ * A.projectedLength) := by
      rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left upper (inv_nonneg.mpr positive.le)

end Unfoldings.PolygonalChain
