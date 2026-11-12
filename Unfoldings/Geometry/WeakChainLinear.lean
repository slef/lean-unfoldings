module

public import Unfoldings.Geometry.BankRadialOrder
public import Unfoldings.Geometry.SegmentHeightUnique

/-! A controlling coordinate is injective on a chain when every zero step is genuinely flat. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (height : E →ₗ[ℝ] ℝ)
  (nonnegative : ∀ i, 0 ≤ height (P.edge i))
  (flat : ∀ i, height (P.edge i) = 0 → P.edge i = 0)

include nonnegative flat

theorem vertices_eq_of_weak_linear_eq (u v : Fin (n + 1)) (ordered : u ≤ v)
    (equal : height (P.vertex u) = height (P.vertex v)) : P.vertex u = P.vertex v := by
  have monotone := (P.monotone_linear_vertices_iff height).mpr nonnegative
  revert ordered equal
  induction v using Fin.induction with
  | zero =>
    intro ordered _
    have same : u = 0 := le_antisymm ordered (show (0 : Fin (n + 1)) ≤ u from Nat.zero_le u.val)
    rw [same]
  | succ v ih =>
    intro ordered equal
    by_cases same : u = v.succ
    · rw [same]
    · have before : u ≤ v.castSucc := by
        change u.val ≤ v.val
        have different : u.val ≠ v.val + 1 := fun h => same (Fin.ext h)
        change u.val ≤ v.val + 1 at ordered
        omega
      have first := monotone before
      have last := monotone (Fin.castSucc_le_succ v)
      have collapsed : P.edge v = 0 := flat v (by
        simp only [edge, map_sub]
        linarith)
      change P.vertex v.succ - P.vertex v.castSucc = 0 at collapsed
      exact (ih before (by linarith)).trans (sub_eq_zero.mp collapsed).symm

theorem point_eq_on_edge_of_weak_linear_eq (i : Fin n) (t s : unitInterval)
    (equal : height (P.point i t) = height (P.point i s)) : P.point i t = P.point i s := by
  by_cases zero : height (P.edge i) = 0
  · have collapsed := flat i zero
    change P.vertex i.succ - P.vertex i.castSucc = 0 at collapsed
    simp only [point, sub_eq_zero.mp collapsed, AffineMap.lineMap_same, AffineMap.const_apply]
  · have positive : 0 < height (P.edge i) := lt_of_le_of_ne (nonnegative i) (Ne.symm zero)
    apply point_eq_of_mem_segment_of_linear_eq height
      (by simpa only [edge, map_sub, sub_pos] using positive)
      (lineMap_mem_segment ℝ _ _ t.property) (lineMap_mem_segment ℝ _ _ s.property) equal

/-- Flat repeated vertices are allowed; equality of the monotone coordinate still means
equality of the actual points on the entire chain image. -/
theorem point_eq_of_weak_linear_eq (i k : Fin n) (t s : unitInterval)
    (equal : height (P.point i t) = height (P.point k s)) : P.point i t = P.point k s := by
  have monotone := (P.monotone_linear_vertices_iff height).mpr nonnegative
  have forward (i k : Fin n) (t s : unitInterval) (before : i < k)
      (equal : height (P.point i t) = height (P.point k s)) : P.point i t = P.point k s := by
    have middle_order : i.succ ≤ k.castSucc := by change i.val + 1 ≤ k.val; omega
    have first : height (P.point i t) ≤ height (P.vertex i.succ) := by
      rw [P.linear_point]
      nlinarith [monotone (Fin.castSucc_le_succ i), t.property.1, t.property.2]
    have middle := monotone middle_order
    have last : height (P.vertex k.castSucc) ≤ height (P.point k s) := by
      rw [P.linear_point]
      nlinarith [monotone (Fin.castSucc_le_succ k), s.property.1, s.property.2]
    calc
      P.point i t = P.point i 1 := P.point_eq_on_edge_of_weak_linear_eq height nonnegative flat
        i t 1 (by rw [P.point_one]; linarith)
      _ = P.point k 0 := by
        rw [P.point_one, P.point_zero]
        exact P.vertices_eq_of_weak_linear_eq height nonnegative flat i.succ k.castSucc
          middle_order (by linarith)
      _ = P.point k s := P.point_eq_on_edge_of_weak_linear_eq height nonnegative flat
        k 0 s (by rw [P.point_zero]; linarith)
  rcases lt_trichotomy i k with before | rfl | after
  · exact forward i k t s before equal
  · exact P.point_eq_on_edge_of_weak_linear_eq height nonnegative flat i t s equal
  · exact (forward k i s t after equal.symm).symm

end Unfoldings.PolygonalChain
