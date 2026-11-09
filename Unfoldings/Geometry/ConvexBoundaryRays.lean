module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Module

/-! A ray from an interior origin meets a convex frontier at most once. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem smul_mem_interior_of_mem_frontier (convex : Convex ℝ s)
    (origin : (0 : E) ∈ interior s) {x : E} (boundary : x ∈ frontier s)
    {t : ℝ} (nonnegative : 0 ≤ t) (less : t < 1) : t • x ∈ interior s := by
  have member := convex.add_smul_sub_mem_interior' boundary.1 origin
    (t := 1 - t) ⟨sub_pos.mpr less, by linarith⟩
  have equal : x + (1 - t) • ((0 : E) - x) = t • x := by module
  rwa [equal] at member

theorem eq_of_frontier_eq_nonnegative_smul (convex : Convex ℝ s)
    (origin : (0 : E) ∈ interior s) {x y : E}
    (hx : x ∈ frontier s) (hy : y ∈ frontier s) {t : ℝ}
    (nonnegative : 0 ≤ t) (equal : y = t • x) : y = x := by
  rcases lt_trichotomy t 1 with less | same | greater
  · exact (hy.2 (equal.symm ▸ smul_mem_interior_of_mem_frontier convex origin hx
      nonnegative less)).elim
  · simpa only [same, one_smul] using equal
  · have positive : 0 < t := lt_trans zero_lt_one greater
    have inverse_less : t⁻¹ < 1 := (inv_lt_one₀ positive).mpr greater
    have reversed : x = t⁻¹ • y := by rw [equal, smul_smul, inv_mul_cancel₀ positive.ne', one_smul]
    exact (hx.2 (reversed.symm ▸ smul_mem_interior_of_mem_frontier convex origin hy
      (inv_nonneg.mpr positive.le) inverse_less)).elim

end Unfoldings
