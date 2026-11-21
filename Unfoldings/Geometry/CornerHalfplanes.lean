module

public import Unfoldings.Geometry.TriangleCornerGuard
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Linear inequalities identify the coefficients in a corner sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The two supporting halfplanes of a pointed corner determine its nonnegative ray
coordinates. The altitude bound then makes the coefficient at the apex positive. -/
theorem exists_corner_coeff_of_halfplanes {p q x : Plane} (o : Orientation ℝ Plane (Fin 2))
    (f g : Plane →ₗ[ℝ] ℝ) (fp : f p = 0) (gq : g q = 0)
    (fq : 0 < f q) (gp : 0 < g p) (fx : 0 ≤ f x) (gx : 0 ≤ g x)
    (near : ‖x‖ < |o.areaForm p q| / ‖q - p‖) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b < 1 ∧ x = a • p + b • q := by
  have p_ne : p ≠ 0 := by
    intro zero
    simp [zero] at gp
  have pq : LinearIndependent ℝ (![p, q] : Fin 2 → Plane) :=
    (LinearIndependent.pair_iff' (K := ℝ) p_ne).mpr fun c eq => by
      have fg := congrArg f eq
      rw [map_smul, fp, smul_zero] at fg
      exact fq.ne' fg.symm
  have top := pq.span_eq_top_of_card_eq_finrank (by simp [Plane])
  have full : Submodule.span ℝ ({p, q} : Set Plane) = ⊤ := by
    rwa [Matrix.range_cons_cons_empty] at top
  obtain ⟨a, b, eq⟩ := Submodule.mem_span_pair.mp
    (show x ∈ Submodule.span ℝ ({p, q} : Set Plane) by rw [full]; exact Submodule.mem_top)
  have fsum := congrArg f eq
  rw [map_add, map_smul, map_smul, fp, smul_zero, zero_add, smul_eq_mul] at fsum
  have gsum := congrArg g eq
  rw [map_add, map_smul, map_smul, gq, smul_zero, add_zero, smul_eq_mul] at gsum
  have ap : 0 ≤ a := nonneg_of_mul_nonneg_left (gsum.trans_ge gx) gp
  have bp : 0 ≤ b := nonneg_of_mul_nonneg_left (fsum.trans_ge fx) fq
  have area : o.areaForm p q ≠ 0 := by
    intro zero
    rw [zero, abs_zero, zero_div] at near
    exact (not_lt_of_ge (norm_nonneg _)) near
  exact ⟨a, b, ap, bp, sum_coeff_lt_one_of_corner_altitude o area ap bp eq.symm near, eq.symm⟩

end Unfoldings
