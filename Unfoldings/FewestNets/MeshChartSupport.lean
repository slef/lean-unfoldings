module

public import Unfoldings.FewestNets.MeshChartFrame

/-! Exact metric and bisector formulas for the finite certificate's chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open NormedSpace

def chartAxes (s : Space) : Fin 3 → Space := ![chartFirst s, chartSecond s, s]

theorem chartAxes_orthonormal {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) :
    Orthonormal ℝ (chartAxes s) := by
  obtain ⟨u, v, su, sv, uv⟩ := chartFrame_orthonormal unit genuine
  have us : inner ℝ (chartFirst s) s = 0 := (real_inner_comm s _).trans su
  have vs : inner ℝ (chartSecond s) s = 0 := (real_inner_comm s _).trans sv
  have vu : inner ℝ (chartSecond s) (chartFirst s) = 0 := (real_inner_comm _ _).trans uv
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simp [chartAxes, u, v, unit, su, sv, uv, us, vs, vu]

/-- The two certificate axes and the site direction form a full orthonormal frame. -/
def chartOrthonormalBasis {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) :
    OrthonormalBasis (Fin 3) ℝ Space :=
  let ortho := chartAxes_orthonormal unit genuine
  let base := basisOfOrthonormalOfCardEqFinrank ortho (by simp [Space])
  let repr : (base : Fin 3 → Space) = chartAxes s := coe_basisOfOrthonormalOfCardEqFinrank _ _
  base.toOrthonormalBasis (repr.symm ▸ ortho)

theorem chartOrthonormalBasis_apply {s : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0) (i : Fin 3) :
    chartOrthonormalBasis unit genuine i = (![chartFirst s, chartSecond s, s] : Fin 3 → Space) i := by
  let ortho := chartAxes_orthonormal unit genuine
  let card : Fintype.card (Fin 3) = Module.finrank ℝ Space := by simp [Space]
  let base := basisOfOrthonormalOfCardEqFinrank ortho card
  have axes : (base : Fin 3 → Space) = chartAxes s :=
    coe_basisOfOrthonormalOfCardEqFinrank ortho card
  have orthonormal : Orthonormal ℝ base := axes.symm ▸ ortho
  have coe : (base.toOrthonormalBasis orthonormal : Fin 3 → Space) = chartAxes s :=
    (Module.Basis.coe_toOrthonormalBasis _ _).trans axes
  exact congrFun coe i

/-- Coordinates in the tangent frame preserve the inner product there. -/
theorem chartPoint_inner {s x y : Space} (unit : ‖s‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (ty : inner ℝ s y = 0) :
    inner ℝ (chartPoint s x) (chartPoint s y) = inner ℝ x y := by
  let B := chartOrthonormalBasis unit genuine
  have sum := B.sum_inner_mul_inner x y
  have b0 : B 0 = chartFirst s := chartOrthonormalBasis_apply unit genuine 0
  have b1 : B 1 = chartSecond s := chartOrthonormalBasis_apply unit genuine 1
  have b2 : B 2 = s := chartOrthonormalBasis_apply unit genuine 2
  rw [Fin.sum_univ_three, b0, b1, b2, ty, mul_zero, add_zero] at sum
  conv_lhs => rw [PiLp.inner_apply, Fin.sum_univ_two]
  change inner ℝ y (chartFirst s) * inner ℝ x (chartFirst s) +
      inner ℝ y (chartSecond s) * inner ℝ x (chartSecond s) = _
  rw [real_inner_comm (chartFirst s) y, real_inner_comm (chartSecond s) y]
  simpa only [mul_comm] using sum

theorem inner_bisectorTangent (s t : Space) (unit : ‖s‖ = 1) :
    inner ℝ s (bisectorTangent s t) = 0 := by
  rw [bisectorTangent, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unit, one_pow, mul_one, sub_self]

theorem inner_meshGnomonic {s n : Space} (unit : ‖s‖ = 1) (nonzero : inner ℝ s n ≠ 0) :
    inner ℝ s (meshGnomonic s n) = 0 := by
  rw [meshGnomonic, inner_sub_right, real_inner_smul_right, inv_mul_cancel₀ nonzero,
    real_inner_self_eq_norm_sq, unit, one_pow, sub_self]

/-- Unit bisector normal and the apothem formula used in each finite record. -/
theorem chart_bisector_le_iff {s t n : Space} (unit : ‖s‖ = 1) (neighbor : ‖t‖ = 1)
    (genuine : bisectorTangent s (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (positive : 0 < inner ℝ s n) (side_nonzero : bisectorTangent s t ≠ 0) :
    inner ℝ (chartPoint s (meshGnomonic s n)) (chartPoint s (normalize (bisectorTangent s t))) ≤
      ‖bisectorTangent s t‖ / (1 + inner ℝ s t) ↔ inner ℝ n t ≤ inner ℝ n s := by
  let E := bisectorTangent s t
  let d := inner ℝ s t
  have Epos : 0 < ‖E‖ := norm_pos_iff.mpr side_nonzero
  have square : ‖E‖ ^ 2 = 1 - d ^ 2 := by
    dsimp [E, bisectorTangent, d]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, unit, neighbor, one_pow,
      mul_one, real_inner_smul_right, real_inner_comm s t]
    ring
  have d_pos : 0 < 1 + d := by
    have lower : -1 ≤ d := by
      have h := abs_real_inner_le_norm s t
      rw [unit, neighbor, one_mul] at h
      exact (abs_le.mp h).1
    have ne : d ≠ -1 := by
      intro bad
      rw [bad] at square
      norm_num at square
      exact side_nonzero square
    linarith only [lt_of_le_of_ne lower (Ne.symm ne)]
  have off_eq : ‖E‖ / (1 + d) = (1 - d) / ‖E‖ := by
    apply (div_eq_div_iff d_pos.ne' Epos.ne').mpr
    nlinarith only [square]
  have perp : inner ℝ s (normalize E) = 0 := by
    rw [NormedSpace.normalize, real_inner_smul_right, inner_bisectorTangent s t unit, mul_zero]
  change inner ℝ (chartPoint s (meshGnomonic s n)) (chartPoint s (normalize E)) ≤ _ ↔ _
  rw [chartPoint_inner unit genuine perp, off_eq,
    NormedSpace.normalize, real_inner_smul_right, ← div_eq_inv_mul,
    div_le_div_iff_of_pos_right Epos]
  exact inner_meshGnomonic_bisectorTangent_le_iff unit positive

end Unfoldings.FewestNets.MeshStar
