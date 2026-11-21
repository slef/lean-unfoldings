module

public import Unfoldings.Geometry.RadialTriangleGauge
public import Unfoldings.Geometry.AcuteSphericalHinge
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! The complementary corners at a common cone edge lie on opposite radial sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry InnerProductSpace Module
open scoped BigOperators

variable {a b c d : Space}

theorem opposite_radial_side_of_common_edge
    (left : LinearIndependent ℝ ![a, b, c]) (right : LinearIndependent ℝ ![a, b, d])
    (on_edge : ∀ x ∈ radialTriangleCone ![a, b, c],
      x ∈ radialTriangleCone ![a, b, d] → (radialTriangleBasis left).coord 2 x = 0) :
    (radialTriangleBasis left).coord 2 d < 0 := by
  let B := radialTriangleBasis left
  let L := B.coord 2
  have La : L a = 0 := by
    change B.coord 2 (![a, b, c] (0 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have Lb : L b = 0 := by
    change B.coord 2 (![a, b, c] (1 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have Lc : L c = 1 := by
    change B.coord 2 (![a, b, c] (2 : Fin 3)) = 1
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have d_ne : L d ≠ 0 := by
    intro zero
    have h : L = 0 := by
      apply LinearMap.ext_on_range (right.span_eq_top_of_card_eq_finrank (by simp [Space]))
      intro k
      fin_cases k
      · exact La
      · exact Lb
      · exact zero
    rw [h, LinearMap.zero_apply] at Lc
    norm_num at Lc
  by_contra! nonnegative
  have positive : 0 < L d := lt_of_le_of_ne nonnegative d_ne.symm
  let r := max (-(B.coord 0 d)) (-(B.coord 1 d)) + 1
  have r0 : 0 ≤ r + B.coord 0 d := by
    have le := le_max_left (-(B.coord 0 d)) (-(B.coord 1 d))
    dsimp [r]
    linarith only [le]
  have r1 : 0 ≤ r + B.coord 1 d := by
    have le := le_max_right (-(B.coord 0 d)) (-(B.coord 1 d))
    dsimp [r]
    linarith only [le]
  let R : ℝ := max r 0
  have R_nonnegative : 0 ≤ R := le_max_right _ _
  have r_le_R : r ≤ R := le_max_left _ _
  let x := R • a + R • b + d
  have in_right : x ∈ radialTriangleCone ![a, b, d] := by
    refine ⟨![R, R, 1], fun k => ?_, ?_⟩
    · fin_cases k
      · exact R_nonnegative
      · exact R_nonnegative
      · exact zero_le_one
    · rw [Fin.sum_univ_three]
      change R • a + R • b + d = R • a + R • b + 1 • d
      rw [one_smul]
  have in_left : x ∈ radialTriangleCone ![a, b, c] := by
    refine ⟨![R + B.coord 0 d, R + B.coord 1 d, L d], fun k => ?_, ?_⟩
    · fin_cases k
      · exact r0.trans (add_le_add r_le_R le_rfl)
      · exact r1.trans (add_le_add r_le_R le_rfl)
      · exact positive.le
    · rw [Fin.sum_univ_three]
      change R • a + R • b + d =
        (R + B.coord 0 d) • a + (R + B.coord 1 d) • b + (L d) • c
      have repr := B.sum_repr d
      rw [Fin.sum_univ_three] at repr
      simp only [← Basis.coord_apply] at repr
      rw [radialTriangleBasis_eq_corner left 0, radialTriangleBasis_eq_corner left 1,
        radialTriangleBasis_eq_corner left 2] at repr
      change (B.coord 0 d) • a + (B.coord 1 d) • b + (L d) • c = d at repr
      nth_rw 1 [← repr]
      rw [add_smul, add_smul]
      abel
  have overlap : L x = 0 := on_edge x in_left in_right
  dsimp [x] at overlap
  simp only [map_add, map_smul, La, Lb, smul_zero, zero_add] at overlap
  exact d_ne overlap

/-- On the opposite corner of an adjoining acute triangle, the first
triangle's normalized supporting gauge is strictly below one. -/
theorem radialTriangleGauge_lt_of_acute_common_edge
    (left : LinearIndependent ℝ ![a, b, c]) (right : LinearIndependent ℝ ![a, b, d])
    (on_edge : ∀ x ∈ radialTriangleCone ![a, b, c],
      x ∈ radialTriangleCone ![a, b, d] → (radialTriangleBasis left).coord 2 x = 0)
    (au : ‖a‖ = 1) (bu : ‖b‖ = 1) (cu : ‖c‖ = 1) (du : ‖d‖ = 1)
    (acute_c : angle (a - c) (b - c) < Real.pi / 2)
    (acute_d : angle (a - d) (b - d) < Real.pi / 2) :
    radialTriangleGauge left d < 1 := by
  let B := radialTriangleBasis left
  let L := B.coord 2
  let v := (toDual ℝ Space).symm L.toContinuousLinearMap
  have eq (z : Space) : inner ℝ v z = L z := toDual_symm_apply
  have a0 : L a = 0 := by
    change B.coord 2 (![a, b, c] (0 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have b0 : L b = 0 := by
    change B.coord 2 (![a, b, c] (1 : Fin 3)) = 0
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have c1 : L c = 1 := by
    change B.coord 2 (![a, b, c] (2 : Fin 3)) = 1
    rw [radialTriangleBasis_coord_corner]
    norm_num
  have chord : a + b ≠ 0 := by
    intro zero
    have h := congrArg (B.coord 0) zero
    rw [map_add, map_zero] at h
    change B.coord 0 (![a, b, c] (0 : Fin 3)) +
      B.coord 0 (![a, b, c] (1 : Fin 3)) = 0 at h
    rw [radialTriangleBasis_coord_corner, radialTriangleBasis_coord_corner] at h
    norm_num at h
  have slope := opposite_radial_side_of_common_edge left right on_edge
  obtain ⟨n, np, ab, ac, nd⟩ := exists_strict_support_of_acute_spherical_hinge
    au bu cu du chord ((eq a).trans a0) ((eq b).trans b0)
    (by rw [eq, c1]; norm_num) ((eq d).trans_lt slope) acute_c acute_d
  let N := (inner ℝ n a)⁻¹ • (innerSL ℝ n).toLinearMap
  have value (z : Space) : N z = inner ℝ n z / inner ℝ n a := by
    simp only [N, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
      smul_eq_mul, div_eq_inv_mul]
  have unit (i : Fin 3) : N (![a, b, c] i) = 1 := by
    rw [value]
    fin_cases i
    · exact div_self np.ne'
    · change inner ℝ n b / inner ℝ n a = 1
      rw [← ab, div_self np.ne']
    · change inner ℝ n c / inner ℝ n a = 1
      rw [← ac, div_self np.ne']
  rw [radialTriangleGauge_unique left N unit, value, div_lt_one np]
  exact nd

end Unfoldings
