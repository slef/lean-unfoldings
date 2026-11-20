module

public import Unfoldings.Geometry.AngleConeBound
public import Unfoldings.Geometry.Affine
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-! Two supporting linear inequalities bound the angle between directions in their wedge. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry
open scoped NNReal

/-- The nonnegative sides of two independent linear forms in the plane are
the positive span of the two inward-pointing boundary rays. -/
theorem inDirectionWedge_of_linear_nonneg {u v x : Plane} (f g : Plane →ₗ[ℝ] ℝ)
    (fu : f u = 0) (gv : g v = 0) (fv : 0 < f v) (gu : 0 < g u)
    (fx : 0 ≤ f x) (gx : 0 ≤ g x) : InDirectionWedge u v x := by
  have independent : LinearIndependent ℝ ![u, v] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c eq i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at eq
    have cg := congrArg g eq
    have cf := congrArg f eq
    simp only [map_add, map_smul, smul_eq_mul, fu, gv, mul_zero, zero_add,
      add_zero, map_zero] at cg cf
    fin_cases i
    · exact (mul_eq_zero.mp cg).resolve_right gu.ne'
    · exact (mul_eq_zero.mp cf).resolve_right fv.ne'
  have span := independent.span_eq_top_of_card_eq_finrank (by simp [Plane])
  have range : Set.range ![u, v] = {u, v} := by
    ext y
    simp [eq_comm, or_comm]
  rw [range] at span
  have member : x ∈ Submodule.span ℝ ({u, v} : Set Plane) := by rw [span]; trivial
  obtain ⟨a, b, ab⟩ := Submodule.mem_span_pair.mp member
  have cg := congrArg g ab
  have cf := congrArg f ab
  simp only [map_add, map_smul, smul_eq_mul, fu, gv, mul_zero, zero_add, add_zero] at cg cf
  exact ⟨a, b, nonneg_of_mul_nonneg_left (cg.symm ▸ gx) gu,
    nonneg_of_mul_nonneg_left (cf.symm ▸ fx) fv, ab.symm⟩

/-- The angle between two nonzero directions in a wedge is at most its opening. -/
theorem angle_le_angle_of_inDirectionWedge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (first : InDirectionWedge u v x) (last : InDirectionWedge u v y) :
    angle x y ≤ angle u v := by
  have split {w : E} (hne : w ≠ 0) (inside : InDirectionWedge u v w) :
      angle u v = angle u w + angle w v := by
    obtain ⟨a, b, ha, hb, expression⟩ := inside
    apply (angle_eq_angle_add_angle_iff hne).mpr
    right
    exact Submodule.mem_span_pair.mpr ⟨⟨a, ha⟩, ⟨b, hb⟩, expression.symm⟩
  have left := angle_le_angle_add_angle x u y
  have right := angle_le_angle_add_angle x v y
  rw [angle_comm x u] at left
  rw [angle_comm v y] at right
  linarith only [left, right, split hx first, split hy last]

/-- Two planar half-planes with inward normals making a genuine angle cut
out an angular wedge of supplementary opening. -/
theorem angle_le_pi_sub_angle_of_inward_normals {a b x y : Plane}
    (a_ne : a ≠ 0) (b_ne : b ≠ 0) (x_ne : x ≠ 0) (y_ne : y ≠ 0)
    (angle_pos : 0 < angle a b) (angle_small : angle a b < Real.pi)
    (ax : 0 ≤ inner ℝ a x) (bx : 0 ≤ inner ℝ b x)
    (ay : 0 ≤ inner ℝ a y) (by' : 0 ≤ inner ℝ b y) :
    angle x y ≤ Real.pi - angle a b := by
  let : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩
  let initial := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have no_zero : initial.areaForm a b ≠ 0 := by
    intro zero
    have size := initial.inner_sq_add_areaForm_sq a b
    rw [zero, zero_pow (by decide), add_zero, ← cos_angle_mul_norm_mul_norm] at size
    have factor : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 :=
      mul_pos (sq_pos_of_pos (norm_pos_iff.mpr a_ne)) (sq_pos_of_pos (norm_pos_iff.mpr b_ne))
    have ratio : Real.cos (angle a b) ^ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) =
        1 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by linear_combination size
    have eq := mul_right_cancel₀ factor.ne' ratio
    have sine := Real.sin_sq_add_cos_sq (angle a b)
    have positive := Real.sin_pos_of_pos_of_lt_pi angle_pos angle_small
    linarith only [eq, sine, sq_pos_of_pos positive]
  obtain ⟨o, o_pos⟩ : ∃ o : Orientation ℝ Plane (Fin 2), 0 < o.areaForm a b := by
    rcases lt_or_gt_of_ne no_zero with neg | pos
    · refine ⟨-initial, ?_⟩
      simpa [Orientation.areaForm_neg_orientation] using neg
    · exact ⟨initial, pos⟩
  let J := o.rightAngleRotation
  let u := J a
  let v := -J b
  have au : inner ℝ a u = 0 := by rw [real_inner_comm]; exact o.inner_rightAngleRotation_self a
  have bv : inner ℝ b v = 0 := by
    dsimp only [v, J]
    rw [inner_neg_right, real_inner_comm, o.inner_rightAngleRotation_self, neg_zero]
  have bu : 0 < inner ℝ b u := by
    rw [real_inner_comm]
    exact (o.inner_rightAngleRotation_left a b).symm ▸ o_pos
  have av : 0 < inner ℝ a v := by
    dsimp only [v, J]
    rw [inner_neg_right, o.inner_rightAngleRotation_right, neg_neg]
    exact o_pos
  have cone (z : Plane) (az : 0 ≤ inner ℝ a z) (bz : 0 ≤ inner ℝ b z) :
      InDirectionWedge u v z :=
    inDirectionWedge_of_linear_nonneg (innerSL ℝ a).toLinearMap (innerSL ℝ b).toLinearMap
      au bv av bu az bz
  have local_bound := angle_le_angle_of_inDirectionWedge x_ne y_ne (cone x ax bx) (cone y ay by')
  change angle x y ≤ angle (J a) (-J b) at local_bound
  have map_angle : angle (J a) (J b) = angle a b := J.toLinearIsometry.angle_map a b
  rwa [angle_neg_right, map_angle] at local_bound

end Unfoldings
