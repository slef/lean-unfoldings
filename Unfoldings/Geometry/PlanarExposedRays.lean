module

public import Unfoldings.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.FinCases

/-! At a planar vertex at most two rays can be individually exposed. -/

@[expose] public section

namespace Unfoldings

/-- Three planar rays cannot each have a supporting functional that vanishes
on it and is positive on both others. -/
theorem false_of_three_exposed_planar_rays {u v w : Plane} {f g h : Plane →ₗ[ℝ] ℝ}
    (fu : f u = 0) (fv : 0 < f v) (fw : 0 < f w)
    (gu : 0 < g u) (gv : g v = 0) (gw : 0 < g w)
    (hu : 0 < h u) (hv : 0 < h v) (hw : h w = 0) : False := by
  have independent : LinearIndependent ℝ (![u, v] : Fin 2 → Plane) := by
    apply LinearIndependent.pair_iff.mpr
    intro a b equal
    have f_equal := congrArg f equal
    have g_equal := congrArg g equal
    simp only [map_add, map_smul, smul_eq_mul, fu, mul_zero, zero_add, map_zero] at f_equal
    simp only [map_add, map_smul, smul_eq_mul, gv, mul_zero, add_zero, map_zero] at g_equal
    exact ⟨(mul_eq_zero.mp g_equal).resolve_right gu.ne',
      (mul_eq_zero.mp f_equal).resolve_right fv.ne'⟩
  have pair_range : Set.range (![u, v] : Fin 2 → Plane) = {u, v} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | last
      · exact ⟨0, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp last
        exact ⟨1, rfl⟩
  have span : Submodule.span ℝ ({u, v} : Set Plane) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← pair_range, finrank_span_eq_card independent, Fintype.card_fin]
    norm_num [Plane]
  obtain ⟨a, b, equal⟩ := Submodule.mem_span_pair.mp (span.symm ▸ Submodule.mem_top (x := w))
  have f_equal := congrArg f equal
  have g_equal := congrArg g equal
  have h_equal := congrArg h equal
  simp only [map_add, map_smul, smul_eq_mul, fu, mul_zero, zero_add] at f_equal
  simp only [map_add, map_smul, smul_eq_mul, gv, mul_zero, add_zero] at g_equal
  simp only [map_add, map_smul, smul_eq_mul, hw] at h_equal
  have a_pos : 0 < a := pos_of_mul_pos_left (g_equal.symm ▸ gw) gu.le
  have b_pos : 0 < b := pos_of_mul_pos_left (f_equal.symm ▸ fw) fv.le
  exact (add_pos (mul_pos a_pos hu) (mul_pos b_pos hv)).ne' h_equal

end Unfoldings
