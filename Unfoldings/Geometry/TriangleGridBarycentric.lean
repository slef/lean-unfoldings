module

public import Unfoldings.Geometry.TriangleGrid

/-! Integer barycentric coordinates characterize every small grid triangle. -/

@[expose] public section

namespace Unfoldings.TriangleGrid

open scoped BigOperators

/-- The coordinatewise minimum of the three small-cell corners. -/
def barycentricMin (q i j : ℕ) (upper : Bool) : Fin 3 → ℕ :=
  ![q - (i + j + if upper then 2 else 1), i, j]

/-- In a lower cell one coordinate increases from the minimum. In an upper
cell two increase. The corner index specifies the exceptional coordinate. -/
def barycentricCorner (q i j : ℕ) (upper : Bool) (k d : Fin 3) : ℕ :=
  barycentricMin q i j upper d + if (d = k) ↔ upper = false then 1 else 0

theorem barycentricCorner_bounds (q i j : ℕ) (upper : Bool) (k d : Fin 3) :
    barycentricMin q i j upper d ≤ barycentricCorner q i j upper k d ∧
      barycentricCorner q i j upper k d ≤ barycentricMin q i j upper d + 1 := by
  unfold barycentricCorner
  split <;> omega

theorem barycentricCorner_one (q i j : ℕ) (upper : Bool) (k : Fin 3) :
    barycentricCorner q i j upper k 1 = (corner i j upper k).1 := by
  cases upper <;> fin_cases k <;> simp [barycentricCorner, barycentricMin, corner]

theorem barycentricCorner_two (q i j : ℕ) (upper : Bool) (k : Fin 3) :
    barycentricCorner q i j upper k 2 = (corner i j upper k).2 := by
  cases upper <;> fin_cases k <;> simp [barycentricCorner, barycentricMin, corner]

theorem sum_barycentricMin {q i j : ℕ} {upper : Bool} (valid : Valid q i j upper) :
    (∑ d, barycentricMin q i j upper d) + (if upper then 2 else 1) = q := by
  rw [Fin.sum_univ_three]
  cases upper <;> simp [barycentricMin, Valid] at valid ⊢ <;> omega

theorem sum_barycentricCorner {q i j : ℕ} {upper : Bool} (valid : Valid q i j upper)
    (k : Fin 3) : (∑ d, barycentricCorner q i j upper k d) = q := by
  have sum := sum_barycentricMin valid
  unfold barycentricCorner
  rw [Finset.sum_add_distrib]
  suffices (∑ d : Fin 3, if (d = k) ↔ upper = false then (1 : ℕ) else 0) =
      (if upper then 2 else 1) by rwa [this]
  rw [Fin.sum_univ_three]
  cases upper <;> fin_cases k <;> decide +kernel

/-- Every integer vector with the cell's coordinate bounds and total weight
is one of the three cell corners. -/
theorem exists_barycentricCorner_of_bounds {q i j : ℕ} {upper : Bool} (valid : Valid q i j upper)
    (v : Fin 3 → ℕ) (total : ∑ d, v d = q)
    (bounds : ∀ d, barycentricMin q i j upper d ≤ v d ∧ v d ≤ barycentricMin q i j upper d + 1) :
    ∃ k : Fin 3, barycentricCorner q i j upper k = v := by
  let m := barycentricMin q i j upper
  let bit (d : Fin 3) : Fin 2 := ⟨v d - m d, by
    have h := (bounds d).2
    change v d ≤ m d + 1 at h
    omega⟩
  have decomp (d : Fin 3) : v d = m d + (bit d).val := by
    have h := (bounds d).1
    change m d ≤ v d at h
    change v d = m d + (v d - m d)
    omega
  have sum : ∑ d, (bit d).val = if upper then 2 else 1 := by
    have hm := sum_barycentricMin valid
    change (∑ d, m d) + (if upper then 2 else 1) = q at hm
    simp_rw [decomp, Finset.sum_add_distrib] at total
    change (∑ d, m d) + (∑ d, (bit d).val) = q at total
    omega
  have table : ∀ (upper : Bool) (bit : Fin 3 → Fin 2),
      (∑ d, (bit d).val) = (if upper then 2 else 1) →
      ∃ k : Fin 3, ∀ d : Fin 3, (bit d).val = if (d = k) ↔ upper = false then 1 else 0 := by
    decide +kernel
  obtain ⟨k, hk⟩ := table upper bit sum
  exact ⟨k, funext fun d => by rw [decomp, hk]; rfl⟩

end Unfoldings.TriangleGrid
