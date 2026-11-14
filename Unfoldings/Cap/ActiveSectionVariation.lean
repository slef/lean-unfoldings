module

public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Geometry.IntervalVariationPacking

/-!
# Active-face turning on an actual straight roof section

Two actual supporting faces at each of finitely many distinct collinear contacts
define disjoint inclination intervals. Their total angular variation is bounded
independently of enumeration, intervening mesh vertices, or boundary adjacency.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

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

/-- Distinct contacts give an actual interval packing, with no contour-order hypothesis. -/
theorem sum_active_section_angles_le {I : Type*} [Fintype I] (origin direction : Plane)
    (unit : ‖direction‖ = 1) (time : I → ℝ) (distinct : Function.Injective time)
    (face : I → Bool → Face)
    (active : ∀ i b, K.supportHeight (face i b) (origin + time i • direction) =
      K.roofHeight (origin + time i • direction))
    {R : ℝ} (nonnegative : 0 ≤ R) (bound : ∀ f, ‖K.normalSlope f‖ ≤ R) :
    (∑ i, InnerProductGeometry.angle (K.spatialDirection (face i false) direction)
      (K.spatialDirection (face i true) direction)) ≤ 2 * Real.arctan R := by
  let a (i : I) := K.faceInclination (face i false) direction
  let b (i : I) := K.faceInclination (face i true) direction
  have inclination_bound (i : I) (side : Bool) :
      K.faceInclination (face i side) direction ∈ Set.Icc (-Real.arctan R) (Real.arctan R) :=
    abs_le.mp (K.abs_faceInclination_le bound direction unit (face i side))
  have bounds (i : I) : a i ∈ Set.Icc (-Real.arctan R) (Real.arctan R) ∧
      b i ∈ Set.Icc (-Real.arctan R) (Real.arctan R) :=
    ⟨inclination_bound i false, inclination_bound i true⟩
  have separated : Pairwise (fun i j => Disjoint
      (Set.Ioo (min (a i) (b i)) (max (a i) (b i)))
      (Set.Ioo (min (a j) (b j)) (max (a j) (b j)))) := by
    have order {i j : I} (before : time i < time j) : max (a j) (b j) ≤ min (a i) (b i) := by
      apply max_le <;> apply le_min
      all_goals
        exact K.active_faceInclination_antitone origin direction before _ _
          (active i _) (active j _)
    intro i j different
    have unequal : time i ≠ time j := distinct.ne different
    rcases lt_or_gt_of_ne unequal with before | after
    · apply Set.disjoint_left.mpr
      intro x first last
      exact (not_lt_of_ge (order before)) (first.1.trans last.2)
    · apply Set.disjoint_left.mpr
      intro x first last
      exact (not_lt_of_ge (order after)) (last.1.trans first.2)
  have packing := sum_abs_sub_le_of_disjoint_intervals a b
    (by linarith [Real.arctan_nonneg.mpr nonnegative]) bounds separated
  simp only [K.spatialDirection_angle _ _ direction unit, abs_sub_comm] at ⊢
  simpa only [a, b, faceInclination, sub_neg_eq_add, ← two_mul] using packing

/-- Tilt controls all active-face section bends, including arbitrary-valence contact points. -/
theorem sum_active_section_angles_le_tilt {I : Type*} [Fintype I] (origin direction : Plane)
    (unit : ‖direction‖ = 1) (time : I → ℝ) (distinct : Function.Injective time)
    (face : I → Bool → Face)
    (active : ∀ i b, K.supportHeight (face i b) (origin + time i • direction) =
      K.roofHeight (origin + time i • direction))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    (∑ i, InnerProductGeometry.angle (K.spatialDirection (face i false) direction)
      (K.spatialDirection (face i true) direction)) ≤ 2 * φ := by
  have lower : -(Real.pi / 2) < φ := by linarith [Real.pi_pos]
  have height := Real.cos_pos_of_mem_Ioo ⟨lower, small⟩
  have radius_nonnegative : 0 ≤ Real.sqrt (1 - Real.cos φ ^ 2) / Real.cos φ :=
    div_nonneg (Real.sqrt_nonneg _) height.le
  have bound := K.sum_active_section_angles_le origin direction unit time distinct face active
    radius_nonnegative (K.normalSlope_norm_le height tilt)
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq nonnegative (by linarith [Real.pi_pos]),
    ← Real.tan_eq_sin_div_cos, Real.arctan_tan lower small] at bound
  exact bound

end Unfoldings.ConvexCap
