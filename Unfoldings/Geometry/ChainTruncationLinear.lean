module

public import Unfoldings.Geometry.ChainTruncation

/-! Weak controlling-coordinate progress and flat zero steps survive exact finite truncation. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

theorem truncate_edge_before (i : Fin n) (s : unitInterval) (j : Fin (i.val + 1))
    (before : j.val < i.val) : (P.truncate i s).edge j = P.edge ⟨j.val, by omega⟩ := by
  have first : (P.truncate i s).vertex j.castSucc =
      P.vertex (⟨j.val, by omega⟩ : Fin n).castSucc :=
    P.truncate_vertex_before i s (⟨j.val, by omega⟩ : Fin (n + 1)) before.le
  have last : (P.truncate i s).vertex j.succ =
      P.vertex (⟨j.val, by omega⟩ : Fin n).succ :=
    P.truncate_vertex_before i s (⟨j.val + 1, by omega⟩ : Fin (n + 1))
      (by change j.val + 1 ≤ i.val; omega)
  rw [edge, first, last]
  rfl

theorem truncate_edge_last (i : Fin n) (s : unitInterval) :
    (P.truncate i s).edge (Fin.last i.val) = (s : ℝ) • P.edge i := by
  have first : (P.truncate i s).vertex (Fin.last i.val).castSucc = P.vertex i.castSucc :=
    P.truncate_vertex_before i s i.castSucc (le_refl i.val)
  have last : (P.truncate i s).vertex (Fin.last i.val).succ = P.point i s :=
    P.truncate_vertex_last i s
  rw [edge, first, last]
  simp only [point, edge, AffineMap.lineMap_apply_module]
  module

theorem truncate_linear_nonnegative (height : E →ₗ[ℝ] ℝ)
    (nonnegative : ∀ j, 0 ≤ height (P.edge j)) (i : Fin n) (s : unitInterval)
    (j : Fin (i.val + 1)) : 0 ≤ height ((P.truncate i s).edge j) := by
  by_cases before : j.val < i.val
  · rw [P.truncate_edge_before i s j before]
    exact nonnegative _
  · have last : j = Fin.last i.val := Fin.ext (by change j.val = i.val; omega)
    rw [last, P.truncate_edge_last, map_smul, smul_eq_mul]
    exact mul_nonneg s.property.1 (nonnegative i)

theorem truncate_linear_flat (height : E →ₗ[ℝ] ℝ)
    (flat : ∀ j, height (P.edge j) = 0 → P.edge j = 0) (i : Fin n) (s : unitInterval)
    (j : Fin (i.val + 1)) (zero : height ((P.truncate i s).edge j) = 0) :
    (P.truncate i s).edge j = 0 := by
  by_cases before : j.val < i.val
  · rw [P.truncate_edge_before i s j before] at zero ⊢
    exact flat _ zero
  · have last : j = Fin.last i.val := Fin.ext (by change j.val = i.val; omega)
    rw [last, P.truncate_edge_last] at zero ⊢
    rw [map_smul, smul_eq_mul] at zero
    rcases mul_eq_zero.mp zero with parameter | step
    · rw [parameter, zero_smul]
    · rw [flat i step, smul_zero]

end Unfoldings.PolygonalChain
