module

public import Unfoldings.Roof.NormalImage
public import Unfoldings.Cap.SectionAngles
public import Unfoldings.Geometry.IntervalVariationPacking
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The inclinations on both links of a closing path telescope through its common support face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Real inclination of a genuine support-plane direction, without reduction modulo a turn. -/
def faceInclination (f : Face) (direction : Plane) : ℝ :=
  Real.arctan (-inner ℝ (K.normalSlope f) direction)

/-- Every active face at a later contact has no greater inclination than any earlier active face. -/
theorem active_faceInclination_antitone (origin direction : Plane) {a b : ℝ} (ordered : a < b)
    (f g : Face)
    (first : K.supportHeight f (origin + a • direction) = K.roofHeight (origin + a • direction))
    (last : K.supportHeight g (origin + b • direction) = K.roofHeight (origin + b • direction)) :
    K.faceInclination g direction ≤ K.faceInclination f direction := by
  have monotone := supportingSlopes_monotone K.roofHeight
    (origin + a • direction) (origin + b • direction) (K.normalSlope f) (K.normalSlope g)
    (K.normalSlope_supports first) (K.normalSlope_supports last)
  have displacement : (origin + a • direction) - (origin + b • direction) =
      (a - b) • direction := by module
  rw [displacement, real_inner_smul_right, inner_sub_left] at monotone
  apply Real.arctan_strictMono.monotone
  nlinarith

/-- Uniform normal-slope bounds control every actual support-plane inclination. -/
theorem abs_faceInclination_le {R : ℝ} (bound : ∀ f, ‖K.normalSlope f‖ ≤ R)
    (direction : Plane) (unit : ‖direction‖ = 1) (f : Face) :
    |K.faceInclination f direction| ≤ Real.arctan R := by
  have scalar := (abs_real_inner_le_norm (K.normalSlope f) direction).trans
    (mul_le_mul_of_nonneg_right (bound f) (norm_nonneg direction))
  rw [unit, mul_one] at scalar
  rw [abs_le] at scalar ⊢
  constructor
  · have lower := Real.arctan_strictMono.monotone (neg_le_neg scalar.2)
    simpa only [faceInclination, Real.arctan_neg] using lower
  · exact Real.arctan_strictMono.monotone (by linarith [scalar.1])

/-- The horizontal direction lifted into the supporting plane of an actual roof face. -/
def sectionDirection (f : Face) (direction : Plane) : Space :=
  Cap.horizontalAtHeight direction (-inner ℝ (K.normalSlope f) direction)

theorem sectionDirection_angle (f g : Face) (direction : Plane) (unit : ‖direction‖ = 1) :
    angle (K.sectionDirection f direction) (K.sectionDirection g direction) =
      |arctan (-inner ℝ (K.normalSlope g) direction) -
        arctan (-inner ℝ (K.normalSlope f) direction)| :=
  Cap.angle_horizontalAtHeight direction unit _ _

private theorem abs_arctan_sub_le (x y : ℝ) : |arctan x - arctan y| ≤ |x - y| := by
  have ordered {x y : ℝ} (h : x ≤ y) : arctan y - arctan x ≤ y - x := by
    rcases eq_or_lt_of_le h with rfl | h
    · simp
    obtain ⟨c, _, slope⟩ := exists_deriv_eq_slope arctan h
      continuous_arctan.continuousOn differentiable_arctan.differentiableOn
    rw [Real.deriv_arctan] at slope
    change 1 / (1 + c ^ 2) = (arctan y - arctan x) / (y - x) at slope
    have le_one : 1 / (1 + c ^ 2) ≤ 1 :=
      (div_le_one₀ (by positivity)).mpr (by linarith only [sq_nonneg c])
    rw [slope] at le_one
    simpa only [one_mul] using (div_le_iff₀ (sub_pos.mpr h)).mp le_one
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr (arctan_mono h))]
    linarith only [ordered h]
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr (arctan_mono h))]
    exact ordered h

/-- A bend in an actual support face changes its inclination by at most the
normal-slope norm times the change of direction. -/
theorem abs_faceInclination_sub_le (f : Face) (d e : Plane) :
    |K.faceInclination f d - K.faceInclination f e| ≤ ‖K.normalSlope f‖ * ‖d - e‖ := by
  unfold faceInclination
  apply (abs_arctan_sub_le _ _).trans
  rw [neg_sub_neg, ← inner_sub_right, ← neg_sub d e, inner_neg_right, abs_neg]
  exact abs_real_inner_le_norm _ _

/-- Contacts on one straight link occupy disjoint inclination intervals inside
the actual endpoint range. -/
theorem sum_active_section_angles_le_bounds {I : Type*} [Fintype I] (origin direction : Plane)
    (unit : ‖direction‖ = 1) (time : I → ℝ) (distinct : Function.Injective time)
    (face : I → Bool → Face)
    (active : ∀ i b, K.supportHeight (face i b) (origin + time i • direction) =
      K.roofHeight (origin + time i • direction))
    {lower upper : ℝ} (ordered : lower ≤ upper)
    (bounds : ∀ i side, K.faceInclination (face i side) direction ∈ Set.Icc lower upper) :
    (∑ i, angle (K.sectionDirection (face i false) direction)
      (K.sectionDirection (face i true) direction)) ≤ upper - lower := by
  let a (i : I) := K.faceInclination (face i false) direction
  let b (i : I) := K.faceInclination (face i true) direction
  have order {i j : I} (before : time i < time j) : max (a j) (b j) ≤ min (a i) (b i) := by
    apply max_le <;> apply le_min
    all_goals exact K.active_faceInclination_antitone origin direction before _ _ (active i _) (active j _)
  have separated : Pairwise fun i j => Disjoint
      (Set.Ioo (min (a i) (b i)) (max (a i) (b i)))
      (Set.Ioo (min (a j) (b j)) (max (a j) (b j))) := by
    intro i j different
    rw [Set.disjoint_left]
    intro x at_i at_j
    rcases lt_or_gt_of_ne (distinct.ne different) with before | after
    · exact (not_lt_of_ge (order before)) (at_i.1.trans at_j.2)
    · exact (not_lt_of_ge (order after)) (at_j.1.trans at_i.2)
  have estimate := sum_abs_sub_le_of_disjoint_intervals a b ordered
    (fun i => ⟨bounds i false, bounds i true⟩) separated
  simp only [K.sectionDirection_angle _ _ direction unit, abs_sub_comm] at ⊢
  simpa only [a, b, faceInclination] using estimate

/-- The absolute bends on two closing links share one tilt budget. Their extra
cost tends to zero as the two unit directions coalesce. -/
theorem sum_active_closing_angles_le {I J : Type*} [Fintype I] [Fintype J]
    (origin d e : Plane) (d_unit : ‖d‖ = 1) (e_unit : ‖e‖ = 1)
    (bendTime : ℝ) (middle : Face)
    (bend_active : K.supportHeight middle (origin + bendTime • d) =
      K.roofHeight (origin + bendTime • d))
    (s : I → ℝ) (s_distinct : Function.Injective s) (before : ∀ i, s i < bendTime)
    (t : J → ℝ) (t_distinct : Function.Injective t) (after : ∀ j, 0 < t j)
    (f : I → Bool → Face) (g : J → Bool → Face)
    (f_active : ∀ i b, K.supportHeight (f i b) (origin + s i • d) =
      K.roofHeight (origin + s i • d))
    (g_active : ∀ j b, K.supportHeight (g j b) (origin + bendTime • d + t j • e) =
      K.roofHeight (origin + bendTime • d + t j • e))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i, angle (K.sectionDirection (f i false) d) (K.sectionDirection (f i true) d)) +
      (∑ j, angle (K.sectionDirection (g j false) e) (K.sectionDirection (g j true) e)) ≤
      2 * φ + tan φ * ‖d - e‖ := by
  let p := origin + bendTime • d
  have lower : -(π / 2) < φ := by linarith only [nonnegative, pi_pos]
  have slopes : ∀ f, ‖K.normalSlope f‖ ≤ tan φ := by
    have h := K.normalSlope_norm_le (cos_pos_of_mem_Ioo ⟨lower, small⟩) tilt
    simpa only [← sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith only [small, pi_pos]),
      ← tan_eq_sin_div_cos] using h
  have inclination (w : Plane) (unit : ‖w‖ = 1) (f : Face) :
      K.faceInclination f w ∈ Set.Icc (-φ) φ := by
    have h := K.abs_faceInclination_le slopes w unit f
    rwa [arctan_tan lower small, abs_le] at h
  have left := K.sum_active_section_angles_le_bounds origin d d_unit s s_distinct f f_active
    (inclination d d_unit middle).2 (fun i b => ⟨K.active_faceInclination_antitone origin d
      (before i) _ _ (f_active i b) bend_active, (inclination d d_unit (f i b)).2⟩)
  have start : K.supportHeight middle (p + (0 : ℝ) • e) = K.roofHeight (p + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using bend_active
  have right := K.sum_active_section_angles_le_bounds p e e_unit t t_distinct g g_active
    (inclination e e_unit middle).1 (fun j b => ⟨(inclination e e_unit (g j b)).1,
      K.active_faceInclination_antitone p e (after j) _ _ start (g_active j b)⟩)
  have correction := (le_abs_self _).trans ((K.abs_faceInclination_sub_le middle e d).trans
    (mul_le_mul_of_nonneg_right (slopes middle) (norm_nonneg _)))
  rw [norm_sub_rev] at correction
  linarith only [left, right, correction]

end Unfoldings.ConvexRoof
