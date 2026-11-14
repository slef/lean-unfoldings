module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin

/-! A finite nonnegative weight budget from any actual finite covering, allowing repeated cover. -/

@[expose] public section

namespace Unfoldings

/-- Covering pieces need not be disjoint when only an upper weight bound is required. -/
theorem sum_le_sum_of_finite_cover {I A : Type*} [Finite I] [Fintype A]
    (selected : Finset I) (pieces : A → Finset I) (weight : I → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i) (cover : ∀ i ∈ selected, ∃ a, i ∈ pieces a) :
    (∑ i ∈ selected, weight i) ≤ ∑ a, ∑ i ∈ pieces a, weight i := by
  classical
  let _ := Fintype.ofFinite I
  have pointwise (i : I) : (if i ∈ selected then weight i else 0) ≤
      ∑ a, if i ∈ pieces a then weight i else 0 := by
    by_cases member : i ∈ selected
    · obtain ⟨a, present⟩ := cover i member
      have bound := Finset.single_le_sum (s := Finset.univ)
        (f := fun a => if i ∈ pieces a then weight i else 0)
        (fun a _ => by split_ifs <;> first | exact nonnegative i | exact le_rfl) (Finset.mem_univ a)
      simpa only [member, present, ite_true] using bound
    · simp only [ite_eq_right member]
      exact Finset.sum_nonneg (fun a _ => by
        split_ifs <;> first | exact nonnegative i | exact le_rfl)
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pointwise i)
  rw [Finset.sum_comm] at bound
  simpa only [Finset.sum_ite_mem, Finset.univ_inter] using bound

end Unfoldings
