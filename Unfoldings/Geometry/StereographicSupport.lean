module

public import Unfoldings.Geometry.StereographicConformal
public import Unfoldings.Geometry.PlanarWedgeAngle

/-! Tangent inequalities of supporting hemispheres contain every projected chord. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry

/-- The differential's image lies in the tangent plane of the unit sphere. -/
theorem inner_inverseStereographic_derivative_self (x u : Plane) :
    inner ℝ (inverseStereographic x) (inverseStereographicDerivative x u) = 0 := by
  have diff := (hasFDerivAt_inverseStereographic x).norm_sq
  have constant : (fun y : Plane => ‖inverseStereographic y‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext y
    simp [inverseStereographic_unit]
  rw [constant] at diff
  have zero := diff.unique (hasFDerivAt_const (1 : ℝ) x)
  have at_u := DFunLike.congr_fun zero u
  simp only [ContinuousLinearMap.comp_apply, two_nsmul, add_apply,
    innerSL_apply_apply, zero_apply] at at_u
  linarith

/-- The tangent inequality at a boundary point of a supporting hemisphere has
normal equal to the gradient of the chart's defining quadratic. -/
theorem inner_inverseStereographic_derivative_of_support (n : Space) (x u : Plane)
    (boundary : inner ℝ n (inverseStereographic x) = 0) :
    inner ℝ n (inverseStereographicDerivative x u) =
      (2 / (1 + ‖x‖ ^ 2)) * (inner ℝ (horizontal n) u - n 2 * inner ℝ x u) := by
  let dot := innerSL ℝ n
  have geometric := dot.hasFDerivAt.comp x (hasFDerivAt_inverseStereographic x)
  let a := innerSL ℝ (horizontal n)
  let numerator := fun y : Plane => 2 * a y + n 2 * (1 - ‖y‖ ^ 2)
  let den := fun y : Plane => 1 + ‖y‖ ^ 2
  let nsqDerivative : Plane →L[ℝ] ℝ := 2 • innerSL ℝ x
  have nsq : HasFDerivAt (fun y : Plane => ‖y‖ ^ 2) nsqDerivative x :=
    (hasFDerivAt_id x).norm_sq
  have numeratorDerivative : HasFDerivAt numerator ((2 : ℝ) • a - n 2 • nsqDerivative) x := by
    have h₁ := (a.hasFDerivAt (x := x)).const_smul (2 : ℝ)
    have h₂ := ((hasFDerivAt_const (1 : ℝ) x).sub nsq).const_smul (n 2)
    have h := h₁.add h₂
    rw [zero_sub, smul_neg, ← sub_eq_add_neg] at h
    change HasFDerivAt (fun y => (2 : ℝ) * a y + n 2 * (1 - ‖y‖ ^ 2)) _ x at h
    exact h
  have denDerivative : HasFDerivAt den nsqDerivative x := by
    have h := (hasFDerivAt_const (1 : ℝ) x).add nsq
    rwa [zero_add] at h
  have den_pos : 0 < den x := by dsimp [den]; positivity
  have exact_formula : dot ∘ inverseStereographic = fun y => numerator y / den y := by
    funext y
    exact inverseStereographic_inner n y
  have at_boundary : numerator x = 0 := by
    have eq := congrFun exact_formula x
    change inner ℝ n (inverseStereographic x) = numerator x / den x at eq
    rw [boundary] at eq
    exact (div_eq_zero_iff.mp eq.symm).resolve_right den_pos.ne'
  have scalar := ((hasFDerivAt_inv den_pos.ne').comp x denDerivative).mul numeratorDerivative
  rw [at_boundary, zero_smul, add_zero] at scalar
  have eqfun : ((fun t : ℝ => t⁻¹) ∘ den) * numerator = dot ∘ inverseStereographic := by
    rw [exact_formula]
    funext y
    change (den y)⁻¹ * numerator y = numerator y / den y
    ring
  rw [eqfun] at scalar
  have compare := DFunLike.congr_fun (geometric.unique scalar) u
  simp only [dot, a, den, nsqDerivative, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, add_apply, Function.comp_apply, innerSL_apply_apply,
    smul_eq_mul, two_nsmul] at compare
  rw [compare]
  ring

/-- The entire projected region lies on the inward side of the linear tangent
at any supported boundary point, after pushing its chords to the sphere's tangent plane. -/
theorem inner_inverseStereographic_derivative_chord_nonneg {n : Space} {x y : Plane}
    (center : 0 ≤ n 2) (boundary : inner ℝ n (inverseStereographic x) = 0)
    (inside : 0 ≤ inner ℝ n (inverseStereographic y)) :
    0 ≤ inner ℝ n (inverseStereographicDerivative x (y - x)) := by
  rw [inner_inverseStereographic_derivative_of_support n x _ boundary]
  apply mul_nonneg (by positivity)
  have inside' :
      0 ≤ 2 * inner ℝ (horizontal n) y + n 2 * (1 - ‖y‖ ^ 2) := by
    rw [inverseStereographic_inner] at inside
    have h := (le_div_iff₀ (show 0 < 1 + ‖y‖ ^ 2 by positivity)).mp inside
    simpa only [zero_mul] using h
  have boundary' :=
    (div_eq_zero_iff.mp ((inverseStereographic_inner n x).symm.trans boundary)).resolve_right
      (by positivity)
  have eq := norm_sub_pow_two_real y x
  rw [real_inner_comm x y] at eq
  rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
  have curvature := mul_nonneg center (sq_nonneg ‖y - x‖)
  have identity := congrArg (fun t : ℝ => n 2 * t) eq
  nlinarith only [inside', boundary', curvature, identity]

/-- An inward spherical support normal, expressed in planar tangent coordinates. -/
def stereographicSupportNormal (x : Plane) (n : Space) : Plane :=
  horizontal n - n 2 • x

/-- Chart support normals have exactly the same Gram products as the original
normals in the tangent plane of the sphere. -/
theorem inner_stereographicSupportNormal (x : Plane) (n m : Space)
    (hn : inner ℝ n (inverseStereographic x) = 0)
    (hm : inner ℝ m (inverseStereographic x) = 0) :
    inner ℝ (stereographicSupportNormal x n) (stereographicSupportNormal x m) = inner ℝ n m := by
  have tangent (u : Space) (hu : inner ℝ u (inverseStereographic x) = 0) :
      2 * inner ℝ (horizontal u) x + u 2 * (1 - ‖x‖ ^ 2) = 0 :=
    (div_eq_zero_iff.mp ((inverseStereographic_inner u x).symm.trans hu)).resolve_right
      (by positivity)
  have first := congrArg (fun t : ℝ => m 2 * t) (tangent n hn)
  have second := congrArg (fun t : ℝ => n 2 * t) (tangent m hm)
  rw [stereographicSupportNormal, stereographicSupportNormal, inner_sub_left,
    inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm (horizontal m) x, horizontal_inner]
  linarith only [first, second]

theorem norm_stereographicSupportNormal (x : Plane) (n : Space)
    (hn : inner ℝ n (inverseStereographic x) = 0) :
    ‖stereographicSupportNormal x n‖ = ‖n‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_stereographicSupportNormal x n n hn hn]

theorem angle_stereographicSupportNormal (x : Plane) (n m : Space)
    (hn : inner ℝ n (inverseStereographic x) = 0)
    (hm : inner ℝ m (inverseStereographic x) = 0) :
    angle (stereographicSupportNormal x n) (stereographicSupportNormal x m) = angle n m := by
  rw [angle, angle, norm_stereographicSupportNormal x n hn, norm_stereographicSupportNormal x m hm,
    inner_stereographicSupportNormal x n m hn hm]

/-- The chord corner turns at least as much as the exterior corner of an
intersection of supporting hemispheres. Both chords may point at any other
points inside the two supports. -/
theorem angle_chords_le_pi_sub_spherical_exterior {n m : Space} {x y z : Plane}
    (n_ne : n ≠ 0) (m_ne : m ≠ 0) (y_ne : y ≠ x) (z_ne : z ≠ x)
    (angle_pos : 0 < angle n m) (angle_small : angle n m < Real.pi)
    (n_center : 0 ≤ n 2) (m_center : 0 ≤ m 2)
    (hn : inner ℝ n (inverseStereographic x) = 0)
    (hm : inner ℝ m (inverseStereographic x) = 0)
    (hny : 0 ≤ inner ℝ n (inverseStereographic y))
    (hmy : 0 ≤ inner ℝ m (inverseStereographic y))
    (hnz : 0 ≤ inner ℝ n (inverseStereographic z))
    (hmz : 0 ≤ inner ℝ m (inverseStereographic z)) :
    angle (y - x) (z - x) ≤ Real.pi - angle n m := by
  have n_nonzero : stereographicSupportNormal x n ≠ 0 := by
    exact norm_pos_iff.mp (norm_stereographicSupportNormal x n hn ▸ norm_pos_iff.mpr n_ne)
  have m_nonzero : stereographicSupportNormal x m ≠ 0 := by
    exact norm_pos_iff.mp (norm_stereographicSupportNormal x m hm ▸ norm_pos_iff.mpr m_ne)
  have halfspace {a : Space} {p : Plane} (a_up : 0 ≤ a 2)
      (ha : inner ℝ a (inverseStereographic x) = 0)
      (hap : 0 ≤ inner ℝ a (inverseStereographic p)) :
      0 ≤ inner ℝ (stereographicSupportNormal x a) (p - x) := by
    have h := inner_inverseStereographic_derivative_chord_nonneg a_up ha hap
    rw [inner_inverseStereographic_derivative_of_support a x _ ha] at h
    rw [stereographicSupportNormal, inner_sub_left, real_inner_smul_left]
    exact nonneg_of_mul_nonneg_right h (by positivity)
  have angle_eq := angle_stereographicSupportNormal x n m hn hm
  rw [← angle_eq]
  exact angle_le_pi_sub_angle_of_inward_normals n_nonzero m_nonzero
    (sub_ne_zero.mpr y_ne) (sub_ne_zero.mpr z_ne)
    (by rwa [angle_eq]) (by rwa [angle_eq])
    (halfspace n_center hn hny) (halfspace m_center hm hmy)
    (halfspace n_center hn hnz) (halfspace m_center hm hmz)

end Unfoldings.Cap
