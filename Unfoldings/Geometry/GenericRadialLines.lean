module

public import Unfoldings.Basic
public import Unfoldings.Geometry.AffineArrangement
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Set.Card

/-! A generic translate of a line misses finitely many radial lines in space. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set Module

/-- In three dimensions two directions have a common nonzero linear annihilator. -/
theorem exists_linear_annihilator_pair (u v : Space) :
    ∃ L : Space →ₗ[ℝ] ℝ, L ≠ 0 ∧ L u = 0 ∧ L v = 0 := by
  let S := Submodule.span ℝ ({u, v} : Set Space)
  have finite : ({u, v} : Set Space).Finite := (finite_singleton v).insert u
  have card : ({u, v} : Set Space).ncard ≤ 2 := by
    simpa using ncard_insert_le u ({v} : Set Space)
  have rank : finrank ℝ S < finrank ℝ Space := by
    have h := (finrank_span_le_ncard (R := ℝ) _ finite).trans card
    have space_dim : finrank ℝ Space = 3 := by simp [Space]
    rw [space_dim]
    exact h.trans_lt (by decide)
  obtain ⟨L, ne, kernel⟩ := S.exists_le_ker_of_lt_top
    (Submodule.lt_top_of_finrank_lt_finrank rank)
  exact ⟨L, ne, kernel (Submodule.subset_span (by simp)),
    kernel (Submodule.subset_span (by simp))⟩

/-- Translates whose entire line avoids each specified radial line form a dense set. -/
theorem dense_radial_line_translations {I : Type*} [Finite I] (radial : I → Space)
    (p q : Space) :
    Dense {w : Space | ∀ (i : I) (t r : ℝ),
      AffineMap.lineMap (p + w) (q + w) t ≠ r • radial i} := by
  choose L nonzero direction killed using
    (fun i => exists_linear_annihilator_pair (q - p) (radial i))
  let equation (i : I) : Space →ᵃ[ℝ] ℝ :=
    (L i).toAffineMap + AffineMap.const ℝ Space (L i p)
  have proper (i : I) : equation i ≠ 0 := by
    intro h
    apply nonzero i
    have lin := congrArg AffineMap.linear h
    simpa [equation] using lin
  apply (AffineArrangement.dense_regular equation proper).mono
  intro w tested i t r same
  have value : L i (AffineMap.lineMap (p + w) (q + w) t) = equation i w := by
    simp only [AffineMap.lineMap_apply_module', add_sub_add_right_eq_sub, map_add, map_smul,
      smul_eq_mul, direction i, mul_zero, zero_add]
    change L i p + L i w = L i w + L i p
    ring
  rw [same, map_smul, killed i, smul_zero] at value
  exact tested i value.symm

end Unfoldings
