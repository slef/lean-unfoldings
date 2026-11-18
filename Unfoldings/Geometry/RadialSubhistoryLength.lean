module

public import Unfoldings.Geometry.RadialChainLength
public import Unfoldings.Geometry.OpeningAllAnchors

/-! Uniform all-anchor radial margins derive the length hypotheses for opening traces. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) {γ : ℝ} (positive : 0 < γ) (small : γ ≤ 1)
  (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
    γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))

include positive small margin

/-- Each subhistory's true length is bounded by its own chord with the same reciprocal margin. -/
theorem subhistory_projectedLength_le_chord (j : Fin (n + 1)) (length : ℕ)
    (fits : j.val + length ≤ n) :
    (P.interval j.val length fits).projectedLength ≤
      γ⁻¹ * ‖(P.interval j.val length fits).vertex (Fin.last length) - P.vertex j‖ := by
  have local_margin (i : Fin length) : γ *
      (‖(P.interval j.val length fits).vertex i.castSucc - P.vertex j‖ *
        ‖(P.interval j.val length fits).edge i‖) ≤
      inner ℝ ((P.interval j.val length fits).vertex i.castSucc - P.vertex j)
        ((P.interval j.val length fits).edge i) := by
    exact margin j ⟨j.val + i.val, by omega⟩ (Nat.le_add_right _ _)
  have first : (P.interval j.val length fits).vertex 0 = P.vertex j :=
    congrArg P.vertex (Fin.ext (Nat.add_zero _))
  simpa only [first] using (P.interval j.val length fits).radial_projectedLength_le_chord
    (P.vertex j) positive small local_margin

/-- The finite-bank length input for a positive opening follows from the radial margin alone. -/
theorem subhistory_length_between (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    (P.interval j.val (i.val - j.val) (interval_between_fits j i earlier)).projectedLength ≤
      γ⁻¹ * ‖P.vertex i.castSucc - P.vertex j‖ := by
  have last : (P.interval j.val (i.val - j.val) (interval_between_fits j i earlier)).vertex
      (Fin.last (i.val - j.val)) = P.vertex i.castSucc := by
    apply congrArg P.vertex
    apply Fin.ext
    change j.val + (i.val - j.val) = i.val
    omega
  simpa only [last] using P.subhistory_projectedLength_le_chord positive small margin j
    (i.val - j.val) (interval_between_fits j i earlier)

/-- The terminal prefix length input has the same derived constant. -/
theorem subhistory_length_tail (j : Fin (n + 1)) :
    (P.interval j.val (n - j.val) (interval_tail_fits j)).projectedLength ≤
      γ⁻¹ * ‖P.vertex (Fin.last n) - P.vertex j‖ := by
  have last : (P.interval j.val (n - j.val) (interval_tail_fits j)).vertex
      (Fin.last (n - j.val)) = P.vertex (Fin.last n) := by
    apply congrArg P.vertex
    apply Fin.ext
    change j.val + (n - j.val) = n
    omega
  simpa only [last] using P.subhistory_projectedLength_le_chord positive small margin j
    (n - j.val) (interval_tail_fits j)

end Unfoldings.PolygonalChain
