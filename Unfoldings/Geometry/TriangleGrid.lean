module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-! A regular triangular grid in barycentric coordinates. -/

@[expose] public section

namespace Unfoldings.TriangleGrid

open scoped BigOperators

/-- The three corners of a lower or upper small triangle in an integer grid square. -/
def corner (i j : ℕ) (upper : Bool) (k : Fin 3) : ℕ × ℕ :=
  if upper then ![(i + 1, j + 1), (i, j + 1), (i + 1, j)] k
  else ![(i, j), (i + 1, j), (i, j + 1)] k

/-- A lower triangle consumes one step from the square's base to the outer
edge. An upper triangle needs both steps. -/
def Valid (q i j : ℕ) (upper : Bool) : Prop :=
  i + j + (if upper then 2 else 1) ≤ q

theorem corner_sum_le {q i j : ℕ} {upper : Bool} (h : Valid q i j upper) (k : Fin 3) :
    (corner i j upper k).1 + (corner i j upper k).2 ≤ q := by
  cases upper <;> fin_cases k <;>
    simp [Valid, corner] at h ⊢ <;> omega

/-- The coefficients of a point with given grid coordinates in the candidate cell. -/
def weight (i j : ℕ) (upper : Bool) (u v : ℝ) (k : Fin 3) : ℝ :=
  let x := u - i
  let y := v - j
  if upper then ![x + y - 1, 1 - x, 1 - y] k else ![1 - x - y, x, y] k

theorem sum_weight (i j : ℕ) (upper : Bool) (u v : ℝ) :
    ∑ k, weight i j upper u v k = 1 := by
  rw [Fin.sum_univ_three]
  cases upper <;> (simp [weight] <;> ring_nf)

theorem sum_weight_fst (i j : ℕ) (upper : Bool) (u v : ℝ) :
    ∑ k, weight i j upper u v k * (corner i j upper k).1 = u := by
  rw [Fin.sum_univ_three]
  cases upper <;> simp [weight, corner, Nat.cast_add] <;> ring

theorem sum_weight_snd (i j : ℕ) (upper : Bool) (u v : ℝ) :
    ∑ k, weight i j upper u v k * (corner i j upper k).2 = v := by
  rw [Fin.sum_univ_three]
  cases upper <;> simp [weight, corner, Nat.cast_add] <;> ring

private theorem nonnegative_lower {i j : ℕ} {u v : ℝ}
    (x : (i : ℝ) ≤ u) (y : (j : ℝ) ≤ v) (sum : u + v ≤ (i : ℝ) + j + 1) :
    ∀ k, 0 ≤ weight i j false u v k := by
  intro k
  fin_cases k <;> simp [weight] <;> linarith only [x, y, sum]

private theorem nonnegative_upper {i j : ℕ} {u v : ℝ}
    (x : u ≤ (i : ℝ) + 1) (y : v ≤ (j : ℝ) + 1) (sum : (i : ℝ) + j + 1 ≤ u + v) :
    ∀ k, 0 ≤ weight i j true u v k := by
  intro k
  fin_cases k <;> simp [weight] <;> linarith only [x, y, sum]

/-- Every point of the closed macrotriangle belongs to at least one valid grid triangle.
The case of an integer point on the outer edge uses a cell of the preceding row. -/
theorem exists_nonnegative_weights {q : ℕ} (hq : 0 < q) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u + v ≤ q) :
    ∃ i j : ℕ, ∃ upper : Bool, Valid q i j upper ∧ ∀ k, 0 ≤ weight i j upper u v k := by
  let i := ⌊u⌋₊
  let j := ⌊v⌋₊
  have il : (i : ℝ) ≤ u := Nat.floor_le hu
  have jl : (j : ℝ) ≤ v := Nat.floor_le hv
  have ir : u < (i : ℝ) + 1 := Nat.lt_floor_add_one u
  have jr : v < (j : ℝ) + 1 := Nat.lt_floor_add_one v
  have base_le : i + j ≤ q := by
    have le : (i : ℝ) + j ≤ q := by linarith only [il, jl, h]
    exact_mod_cast le
  by_cases boundary : i + j = q
  · have sum : (i : ℝ) + j = q := by exact_mod_cast boundary
    have u_eq : u = i := by linarith only [il, jl, h, sum]
    have v_eq : v = j := by linarith only [il, jl, h, sum]
    by_cases i_pos : 0 < i
    · have eq : (i - 1 : ℕ) + 1 = i := by omega
      have eqR : ((i - 1 : ℕ) : ℝ) + 1 = i := by exact_mod_cast eq
      exact ⟨i - 1, j, false, by simp [Valid]; omega,
        nonnegative_lower (by linarith only [u_eq, eqR]) jl
          (by linarith only [u_eq, v_eq, eqR])⟩
    · have eq : (j - 1 : ℕ) + 1 = j := by omega
      have eqR : ((j - 1 : ℕ) : ℝ) + 1 = j := by exact_mod_cast eq
      exact ⟨i, j - 1, false, by simp [Valid]; omega,
        nonnegative_lower il (by linarith only [v_eq, eqR])
          (by linarith only [u_eq, v_eq, eqR])⟩
  · by_cases lower : u + v ≤ (i : ℝ) + j + 1
    · exact ⟨i, j, false, by simp [Valid]; omega, nonnegative_lower il jl lower⟩
    · have lt : (i : ℝ) + j + 1 < q := (lt_of_not_ge lower).trans_le h
      have ltN : i + j + 1 < q := by exact_mod_cast lt
      exact ⟨i, j, true, by simp [Valid]; omega,
        nonnegative_upper ir.le jr.le (le_of_not_ge lower)⟩

end Unfoldings.TriangleGrid
