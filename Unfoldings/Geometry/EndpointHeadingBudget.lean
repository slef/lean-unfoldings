module

public import Unfoldings.Geometry.LocalHeadingBudget
public import Mathlib.Algebra.BigOperators.Fin

/-! Local comparisons control a prefix relative to its next, uncharged outgoing link. -/

@[expose] public section

namespace Unfoldings

variable {n : ℕ}

/-- The last link never lies strictly inside a comparison window. -/
theorem interiorVariation_ignore_last (variation : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    interiorVariation (Fin.snoc (fun k : Fin n => variation k.castSucc) 0) i j =
      interiorVariation variation i j := by
  classical
  simp only [interiorVariation, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have last : ¬ Fin.last n < j := not_lt_of_ge (Fin.le_last j)
  simp only [Fin.snoc_castSucc, last, and_false, ite_false, add_zero]

/-- Ignoring the outgoing link leaves exactly the preceding prefix's future variation. -/
theorem futureVariation_ignore_last (variation : Fin (n + 1) → ℝ) (i : Fin n) :
    futureVariation (Fin.snoc (fun k : Fin n => variation k.castSucc) 0) i.castSucc =
      futureVariation (fun k : Fin n => variation k.castSucc) i := by
  classical
  simp only [futureVariation, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, ite_self, add_zero,
    Fin.castSucc_lt_castSucc_iff]

/-- Compare every prefix link with the next outgoing link, charging only prefix variation. -/
theorem abs_heading_sub_next_le_weighted_local_budget
    (heading variation : Fin (n + 1) → ℝ) {B δ : ℝ}
    (budget : 0 ≤ B) (width : 0 < δ) (nonnegative : ∀ k, 0 ≤ variation k)
    (window : ∀ i j, i ≤ j → interiorVariation variation i j < δ →
      |heading i - heading j| ≤ B) (i : Fin n) :
    |heading i.castSucc - heading (Fin.last n)| ≤
      B * (1 + futureVariation (fun k : Fin n => variation k.castSucc) i / δ) := by
  have nonnegative_last : ∀ k : Fin (n + 1),
      0 ≤ Fin.snoc (α := fun _ : Fin (n + 1) => ℝ)
        (fun j : Fin n => variation j.castSucc) 0 k := by
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp
    · simpa using nonnegative j.castSucc
  have estimate := abs_heading_sub_le_weighted_local_budget heading
    (Fin.snoc (fun k : Fin n => variation k.castSucc) 0) budget width nonnegative_last
    (fun a b ordered short => window a b ordered
      (by simpa only [interiorVariation_ignore_last] using short))
    (Fin.last n) i.castSucc (Fin.le_last _)
  simpa only [futureVariation_ignore_last] using estimate

end Unfoldings
