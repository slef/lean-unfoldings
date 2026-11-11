module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith

/-! A finite family of real affine functions has one fixed minimizer on a final half-line. -/

@[expose] public section

namespace Unfoldings

/-- Choose the least slope and then the least intercept among its ties. -/
theorem exists_final_affine_minimizer {ι : Type*} [Finite ι] [Nonempty ι]
    (intercept slope : ι → ℝ) :
    ∃ f : ι, ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ g,
      intercept f + t * slope f ≤ intercept g + t * slope g := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨first, _present, least_slope⟩ :=
    Finset.univ.exists_min_image slope Finset.univ_nonempty
  let tied := Finset.univ.filter (fun f => slope f = slope first)
  have first_tied : first ∈ tied := by simp only [tied, Finset.mem_filter, Finset.mem_univ,
    true_and]
  obtain ⟨f, f_tied, least_intercept⟩ :=
    tied.exists_min_image intercept ⟨first, first_tied⟩
  have same_slope : slope f = slope first := (Finset.mem_filter.mp f_tied).2
  let threshold (g : ι) := |(intercept f - intercept g) / (slope g - slope f)|
  let T := 1 + ∑ g : ι, threshold g
  have nonnegative : 0 ≤ ∑ g : ι, threshold g :=
    Finset.sum_nonneg (fun g _ => abs_nonneg _)
  refine ⟨f, T, by dsimp only [T]; linarith, ?_⟩
  intro t after g
  have slopes : slope f ≤ slope g := by
    rw [same_slope]
    exact least_slope g (Finset.mem_univ g)
  by_cases same : slope f = slope g
  · have g_tied : g ∈ tied := by
      simp only [tied, Finset.mem_filter, Finset.mem_univ, true_and]
      exact same.symm.trans same_slope
    have constants := least_intercept g g_tied
    rw [same]
    linarith
  · have positive : 0 < slope g - slope f := sub_pos.mpr (lt_of_le_of_ne slopes same)
    have single : threshold g ≤ ∑ h : ι, threshold h :=
      Finset.single_le_sum (fun h _ => abs_nonneg _) (Finset.mem_univ g)
    have quotient : (intercept f - intercept g) / (slope g - slope f) ≤ t :=
      (le_abs_self _).trans (single.trans (by dsimp only [T] at after; linarith))
    have multiplied := (div_le_iff₀ positive).mp quotient
    nlinarith

end Unfoldings
