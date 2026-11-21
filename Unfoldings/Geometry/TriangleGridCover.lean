module

public import Unfoldings.Geometry.TriangleGrid

/-! The regular triangular grid covers the whole of any affine triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleGrid

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Affine grid coordinates, with spacing given by the two macroedge
directions divided by the frequency. -/
def point (a b c : E) (q u v : ℝ) : E :=
  a + (u / q) • (b - a) + (v / q) • (c - a)

/-- The small affine triangles are closed convex hulls of their three corners. -/
def cellCorners (a b c : E) (q i j : ℕ) (upper : Bool) (k : Fin 3) : E :=
  point a b c q (corner i j upper k).1 (corner i j upper k).2

def cell (a b c : E) (q i j : ℕ) (upper : Bool) : Set E :=
  convexHull ℝ (Set.range (cellCorners a b c q i j upper))

theorem point_mem_triangle (a b c : E) {q u v : ℝ}
    (hq : 0 < q) (hu : 0 ≤ u) (hv : 0 ≤ v) (sum : u + v ≤ q) :
    point a b c q u v ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → E)) := by
  have coeff : 0 ≤ 1 - u / q - v / q := by
    rw [sub_sub, ← add_div, sub_nonneg, div_le_iff₀ hq, one_mul]
    exact sum
  refine mem_convexHull_of_exists_fintype (![1 - u / q - v / q, u / q, v / q] : Fin 3 → ℝ)
    (![a, b, c] : Fin 3 → E) ?_ ?_ (fun k => Set.mem_range_self k) ?_
  · intro k
    fin_cases k
    · exact coeff
    · exact div_nonneg hu hq.le
    · exact div_nonneg hv hq.le
  · rw [Fin.sum_univ_three]
    change (1 - u / q - v / q) + u / q + v / q = 1
    ring
  · rw [Fin.sum_univ_three]
    change (1 - u / q - v / q) • a + (u / q) • b + (v / q) • c =
      a + (u / q) • (b - a) + (v / q) • (c - a)
    module

theorem cell_subset_triangle (a b c : E) {q i j : ℕ} (hq : 0 < q)
    {upper : Bool} (valid : Valid q i j upper) :
    cell a b c q i j upper ⊆ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → E)) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨k, rfl⟩
  apply point_mem_triangle a b c (by exact_mod_cast hq) (by positivity) (by positivity)
  exact_mod_cast corner_sum_le valid k

theorem point_mem_cell (a b c : E) (q i j : ℕ) (upper : Bool) {u v : ℝ}
    (nonnegative : ∀ k, 0 ≤ weight i j upper u v k) :
    point a b c q u v ∈ cell a b c q i j upper := by
  apply mem_convexHull_of_exists_fintype (weight i j upper u v) (cellCorners a b c q i j upper)
    nonnegative (sum_weight i j upper u v) (fun k => Set.mem_range_self k)
  simp only [cellCorners, point, smul_add, Finset.sum_add_distrib, smul_smul, ← Finset.sum_smul,
    ← mul_div_assoc, ← Finset.sum_div, sum_weight, sum_weight_fst, sum_weight_snd, one_smul]

/-- A convex combination on a finite indexed set extends to all its indices. -/
theorem exists_weights_of_mem_convexHull_range {I : Type*} [Fintype I]
    (vertices : I → E) {x : E} (hx : x ∈ convexHull ℝ (Set.range vertices)) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • vertices i) = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, total, eq⟩ := hx
  rw [Finset.affineCombination_eq_linear_combination _ _ _ total] at eq
  let z : I → ℝ := fun i => if i ∈ s then w i else 0
  have nonnegative (i : I) : 0 ≤ z i := by
    by_cases hi : i ∈ s
    · simpa [z, hi] using hw i hi
    · simp [z, hi]
  refine ⟨z, nonnegative, ?_, ?_⟩
  · simpa [z, Finset.sum_ite_mem] using total
  · simpa [z, ite_smul, Finset.sum_ite_mem] using eq

/-- Recover barycentric coordinates from a convex combination on the three macro corners. -/
theorem exists_grid_coordinates (a b c : E) {q : ℝ} (hq : 0 < q)
    {x : E} (hx : x ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → E))) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ q ∧ point a b c q u v = x := by
  obtain ⟨z, nonnegative, ztotal, xeq⟩ :=
    exists_weights_of_mem_convexHull_range _ hx
  rw [Fin.sum_univ_three] at ztotal xeq
  change z 0 • a + z 1 • b + z 2 • c = x at xeq
  refine ⟨z 1 * q, z 2 * q, mul_nonneg (nonnegative 1) hq.le,
    mul_nonneg (nonnegative 2) hq.le, ?_, ?_⟩
  · rw [← add_mul]
    have le : z 1 + z 2 ≤ 1 := by linarith only [ztotal, nonnegative 0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right le hq.le
  · rw [point, mul_div_cancel_right₀ _ hq.ne', mul_div_cancel_right₀ _ hq.ne', ← xeq]
    have zzero : z 0 = 1 - z 1 - z 2 := by linarith only [ztotal]
    rw [zzero]
    module

/-- The canonical grid subdivides the whole closed macrotriangle. -/
theorem exists_cell_of_mem_triangle (a b c : E) {q : ℕ} (hq : 0 < q)
    {x : E} (hx : x ∈ convexHull ℝ (Set.range (![a, b, c] : Fin 3 → E))) :
    ∃ i j : ℕ, ∃ upper : Bool, Valid q i j upper ∧ x ∈ cell a b c q i j upper := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ :=
    exists_grid_coordinates a b c (q := (q : ℝ)) (by exact_mod_cast hq) hx
  obtain ⟨i, j, upper, valid, weights⟩ := exists_nonnegative_weights hq hu hv huv
  exact ⟨i, j, upper, valid, point_mem_cell a b c q i j upper weights⟩

end Unfoldings.TriangleGrid
