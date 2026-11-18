module

public import Unfoldings.Geometry.PolygonalRaySuffix
public import Unfoldings.Geometry.RadialMarginSubdivision

/-! Continue the actual last edge beyond its far endpoint, retaining every original bank vertex. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E (n + 1))

/-- The true final endpoint stays a named vertex on the complete unbounded bank. -/
def terminalEdgeRay : PolygonalRay E (n + 1) where
  chain := P
  direction := P.edge (Fin.last n)

/-- Every finite bank point, including the true rim endpoint, retains its literal position. -/
theorem point_mem_terminalEdgeRay (i : Fin (n + 1)) (t : unitInterval) :
    P.point i t ∈ P.terminalEdgeRay.carrier := by
  apply Or.inl
  change P.point i t ∈ Set.range P.path
  rw [P.path_range]
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, t, rfl⟩)

/-- A quantitative margin at the last edge's start persists at its true far endpoint. -/
theorem terminalEdgeRay_tail_margin {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i)) (j : Fin (n + 2)) :
    γ * (‖P.vertex (Fin.last (n + 1)) - P.vertex j‖ * ‖P.terminalEdgeRay.direction‖) ≤
      inner ℝ (P.vertex (Fin.last (n + 1)) - P.vertex j) P.terminalEdgeRay.direction := by
  by_cases last : j = Fin.last (n + 1)
  · simp only [last, sub_self, norm_zero, zero_mul, mul_zero, inner_zero_left, le_refl]
  · have earlier : j.val ≤ n := by
      have bound := j.isLt
      have different : j.val ≠ n + 1 := fun same => last (Fin.ext same)
      omega
    have estimate := radial_margin_forward_piece nonnegative small
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
      (margin j (Fin.last n) earlier)
    have endpoint : (P.vertex (Fin.last n).castSucc - P.vertex j) +
        (1 : ℝ) • P.edge (Fin.last n) = P.vertex (Fin.last (n + 1)) - P.vertex j := by
      simp only [one_smul, edge, Fin.succ_last]
      abel
    rw [endpoint, one_smul] at estimate
    exact estimate

/-- Outward finite banks continue outward along their actual last directed edge. -/
theorem terminalEdgeRay_outward (outward : P.Outward) : P.terminalEdgeRay.Outward := by
  constructor
  · intro i earlier
    exact (P.radiallyMonotone_iff_outward.mpr outward) 0 i earlier
  · have start := outward 0 (Fin.last n) (Nat.zero_le _)
    have endpoint : P.vertex (Fin.last (n + 1)) - P.vertex 0 =
        (P.vertex (Fin.last n).castSucc - P.vertex 0) + P.edge (Fin.last n) := by
      unfold edge
      rw [Fin.succ_last]
      abel
    change 0 ≤ inner ℝ (P.vertex (Fin.last (n + 1)) - P.vertex 0) (P.edge (Fin.last n))
    rw [endpoint, inner_add_left]
    exact add_nonneg start (by rw [real_inner_self_eq_norm_sq]; exact sq_nonneg _)

/-- The complete bank remains outward from every original hinge, not only from its source. -/
theorem terminalEdgeRay_suffix_outward (outward : P.Outward) (j : Fin (n + 2)) :
    (P.terminalEdgeRay.suffix j).Outward := by
  apply P.terminalEdgeRay.suffix_outward j outward
  by_cases last : j = Fin.last (n + 1)
  · simp only [last, terminalEdgeRay, sub_self, inner_zero_left, le_refl]
  · have earlier : j.val ≤ n := by
      have bound := j.isLt
      have different : j.val ≠ n + 1 := fun same => last (Fin.ext same)
      omega
    have start := outward j (Fin.last n) earlier
    change 0 ≤ inner ℝ (P.vertex (Fin.last (n + 1)) - P.vertex j) (P.edge (Fin.last n))
    have endpoint : P.vertex (Fin.last (n + 1)) - P.vertex j =
        (P.vertex (Fin.last n).castSucc - P.vertex j) + P.edge (Fin.last n) := by
      unfold edge
      rw [Fin.succ_last]
      abel
    rw [endpoint, inner_add_left]
    exact add_nonneg start (by rw [real_inner_self_eq_norm_sq]; exact sq_nonneg _)

end Unfoldings.PolygonalChain
