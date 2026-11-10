module

public import Unfoldings.Geometry.ChainOrder

/-! Linear coordinates along complete polygonal chains. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) (height : E →ₗ[ℝ] ℝ)

theorem linear_point (i : Fin n) (t : unitInterval) :
    height (P.point i t) = (1 - (t : ℝ)) * height (P.vertex i.castSucc) +
      (t : ℝ) * height (P.vertex i.succ) := by
  simp only [point, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
  ring

/-- Nonnegative coordinate increments are equivalent to ordered vertex coordinates. -/
theorem monotone_linear_vertices_iff :
    Monotone (fun i => height (P.vertex i)) ↔ ∀ i, 0 ≤ height (P.edge i) := by
  rw [Fin.monotone_iff_le_succ]
  simp only [edge, map_sub, sub_nonneg]

/-- Monotone vertex coordinates extend to every point of the ordered polygonal chain. -/
theorem linear_point_le (monotone : Monotone (fun i => height (P.vertex i)))
    (i k : Fin n) (t s : unitInterval) (ordered : Before i t k s) :
    height (P.point i t) ≤ height (P.point k s) := by
  rcases ordered with different | ⟨rfl, parameters⟩
  · have first : height (P.point i t) ≤ height (P.vertex i.succ) := by
      rw [linear_point]
      nlinarith [monotone (Fin.castSucc_le_succ i), t.property.1, t.property.2]
    have middle := monotone (show i.succ ≤ k.castSucc from by change i.val + 1 ≤ k.val; omega)
    have last : height (P.vertex k.castSucc) ≤ height (P.point k s) := by
      rw [linear_point]
      nlinarith [monotone (Fin.castSucc_le_succ k), s.property.1, s.property.2]
    exact first.trans (middle.trans last)
  · rw [linear_point, linear_point]
    have nonnegative := monotone (Fin.castSucc_le_succ i)
    have product := mul_nonneg (show 0 ≤ (s : ℝ) - (t : ℝ) from sub_nonneg.mpr parameters)
      (sub_nonneg.mpr nonnegative)
    nlinarith

/-- Strict coordinate progress makes a linear coordinate injective on the actual chain image. -/
theorem point_eq_of_linear_eq (positive : ∀ i, 0 < height (P.edge i))
    (i k : Fin n) (t s : unitInterval) (ordered : Before i t k s)
    (equal : height (P.point i t) = height (P.point k s)) : P.point i t = P.point k s := by
  have strict : StrictMono (fun i => height (P.vertex i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    simpa only [edge, map_sub, sub_pos] using positive i
  rcases ordered with different | ⟨rfl, parameters⟩
  · have first : height (P.point i t) ≤ height (P.vertex i.succ) :=
      by rw [linear_point]; nlinarith [strict.monotone (Fin.castSucc_le_succ i), t.property.1,
        t.property.2]
    have middle := strict.monotone
      (show i.succ ≤ k.castSucc from by change i.val + 1 ≤ k.val; omega)
    have last : height (P.vertex k.castSucc) ≤ height (P.point k s) :=
      by rw [linear_point]; nlinarith [strict.monotone (Fin.castSucc_le_succ k), s.property.1,
        s.property.2]
    have same_vertex : i.succ = k.castSucc := strict.injective (by linarith)
    have t_one : t = 1 := by
      apply Subtype.ext
      change (t : ℝ) = 1
      have formula := P.linear_point height i t
      have step := strict (show i.castSucc < i.succ from Nat.lt_succ_self i.val)
      nlinarith
    have s_zero : s = 0 := by
      apply Subtype.ext
      change (s : ℝ) = 0
      have formula := P.linear_point height k s
      have step := strict (show k.castSucc < k.succ from Nat.lt_succ_self k.val)
      nlinarith
    rw [t_one, s_zero, point_one, point_zero, same_vertex]
  · have t_s : t = s := by
      apply Subtype.ext
      have first := P.linear_point height i t
      have last := P.linear_point height i s
      have step := strict (show i.castSucc < i.succ from Nat.lt_succ_self i.val)
      nlinarith
    rw [t_s]

end Unfoldings.PolygonalChain
