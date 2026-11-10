module

public import Unfoldings.Basic
public import Unfoldings.Geometry.Normalize
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FinCases

/-! Orthonormal coordinates for two spatial vectors, allowing parallel and opposite directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Complete a prescribed orthonormal pair to a spatial orthonormal basis. -/
theorem exists_basis_first_two (a b : Space) (ua : ‖a‖ = 1) (ub : ‖b‖ = 1)
    (orthogonal : inner ℝ a b = 0) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ Space, B 0 = a ∧ B 1 = b := by
  let w : Fin 3 → Space := ![a, b, 0]
  let s : Set (Fin 3) := {0, 1}
  have reverse : inner ℝ b a = 0 := by rw [real_inner_comm, orthogonal]
  have ortho : Orthonormal ℝ (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    change i = 0 ∨ i = 1 at hi
    change j = 0 ∨ j = 1 at hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      norm_num [w, Set.domRestrict, real_inner_self_eq_norm_sq, ua, ub, orthogonal, reverse,
        Subtype.mk.injEq]
    all_goals
      intro equal
      have values := congrArg (fun i : s => i.val.val) equal
      norm_num at values
  obtain ⟨B, agrees⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin 3) (by simp [Space]) ortho
  exact ⟨B, agrees 0 (by simp [s]), agrees 1 (by simp [s])⟩

/-- A prescribed unit first vector can always be completed, without a nonparallel input. -/
theorem exists_basis_first (a : Space) (unit : ‖a‖ = 1) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ Space, B 0 = a := by
  let w : Fin 3 → Space := ![a, 0, 0]
  let s : Set (Fin 3) := {0}
  have ortho : Orthonormal ℝ (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    change i = 0 at hi
    change j = 0 at hj
    subst i
    subst j
    norm_num [w, Set.domRestrict, real_inner_self_eq_norm_sq, unit]
  obtain ⟨B, agrees⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin 3) (by simp [Space]) ortho
  exact ⟨B, agrees 0 (by simp [s])⟩

/-- Gram--Schmidt coordinates with a nonnegative second component, including dependence. -/
theorem exists_basis_two_vector_decomposition (u v : Space) (nonzero : u ≠ 0) :
    ∃ (B : OrthonormalBasis (Fin 3) ℝ Space) (c d : ℝ), 0 ≤ d ∧
      u = ‖u‖ • B 0 ∧ v = c • B 0 + d • B 1 := by
  let a : Space := NormedSpace.normalize u
  let c : ℝ := inner ℝ a v
  let residual : Space := v - c • a
  have unit : ‖a‖ = 1 := NormedSpace.norm_normalize nonzero
  have ortho : inner ℝ a residual = 0 := by
    dsimp only [residual, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, unit]
    ring
  by_cases flat : residual = 0
  · obtain ⟨B, first⟩ := exists_basis_first a unit
    refine ⟨B, c, 0, le_rfl, ?_, ?_⟩
    · rw [first]
      exact (NormedSpace.norm_smul_normalize u).symm
    · rw [zero_smul, add_zero, first]
      exact sub_eq_zero.mp flat
  · let b : Space := NormedSpace.normalize residual
    have unit_b : ‖b‖ = 1 := NormedSpace.norm_normalize flat
    have pair : inner ℝ a b = 0 := by
      change inner ℝ a (‖residual‖⁻¹ • residual) = 0
      rw [real_inner_smul_right, ortho, mul_zero]
    obtain ⟨B, first, second⟩ := exists_basis_first_two a b unit unit_b pair
    refine ⟨B, c, ‖residual‖, norm_nonneg _, ?_, ?_⟩
    · rw [first]
      exact (NormedSpace.norm_smul_normalize u).symm
    · rw [first, second]
      change v = c • a + ‖residual‖ • NormedSpace.normalize residual
      rw [NormedSpace.norm_smul_normalize]
      dsimp only [residual]
      module

end Unfoldings
