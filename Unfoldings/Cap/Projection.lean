module

public import Unfoldings.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Orthogonal cap projection and exact normal-dependent metric estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

/-- Orthogonal projection to the plane of the horizontal cap rim. -/
def horizontal : Space →ₗ[ℝ] Plane where
  toFun v := WithLp.toLp 2 (fun i : Fin 2 => v i.castSucc)
  map_add' _ _ := by ext i; rfl
  map_smul' _ _ := by ext i; rfl

@[simp] theorem horizontal_apply (v : Space) (i : Fin 2) : horizontal v i = v i.castSucc := rfl

def horizontalCLM : Space →L[ℝ] Plane := horizontal.toContinuousLinearMap

theorem horizontal_norm_sq (v : Space) : ‖v‖ ^ 2 = ‖horizontal v‖ ^ 2 + (v 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [horizontal_apply]
  rfl

theorem horizontal_inner (u v : Space) :
    inner ℝ u v = inner ℝ (horizontal u) (horizontal v) + u 2 * v 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, horizontal_apply,
    Real.inner_apply]
  rfl

theorem horizontal_norm_le (v : Space) : ‖horizontal v‖ ≤ ‖v‖ := by
  have identity := horizontal_norm_sq v
  nlinarith [norm_nonneg (horizontal v), norm_nonneg v, sq_nonneg (v 2)]

/-- A unit upward normal bounds the contraction of horizontal projection on its tangent plane. -/
theorem normal_tangent_projection_lower (normal v : Space) (unit : ‖normal‖ = 1)
    (upward : 0 ≤ normal 2) (tangent : inner ℝ normal v = 0) :
    normal 2 * ‖v‖ ≤ ‖horizontal v‖ := by
  have normal_sq := horizontal_norm_sq normal
  have vector_sq := horizontal_norm_sq v
  have perpendicular := horizontal_inner normal v
  have cs := real_inner_mul_inner_self_le (horizontal normal) (horizontal v)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at cs
  rw [unit] at normal_sq
  have square_bound : (normal 2) ^ 2 * ‖v‖ ^ 2 ≤ ‖horizontal v‖ ^ 2 := by
    have orth : inner ℝ (horizontal normal) (horizontal v) = -normal 2 * v 2 := by
      linarith
    rw [orth] at cs
    have first := congrArg (fun x : ℝ => x * ‖horizontal v‖ ^ 2) normal_sq
    have last := congrArg (fun x : ℝ => (normal 2) ^ 2 * x) vector_sq
    nlinarith [first, last]
  have product_nonnegative := mul_nonneg upward (norm_nonneg v)
  nlinarith [norm_nonneg (horizontal v)]

/-- Vertical motion is uniformly small on a tangent plane with a nearly vertical normal. -/
theorem tangent_vertical_sq_le (normal v : Space) (unit : ‖normal‖ = 1)
    {c : ℝ} (nonnegative : 0 ≤ c) (height : c ≤ normal 2)
    (tangent : inner ℝ normal v = 0) :
    (v 2) ^ 2 ≤ (1 - c ^ 2) * ‖v‖ ^ 2 := by
  have lower := normal_tangent_projection_lower normal v unit
    (nonnegative.trans height) tangent
  have bound : c * ‖v‖ ≤ ‖horizontal v‖ :=
    (mul_le_mul_of_nonneg_right height (norm_nonneg v)).trans lower
  have squared := mul_self_le_mul_self (mul_nonneg nonnegative (norm_nonneg v)) bound
  have identity := horizontal_norm_sq v
  nlinarith [squared]

theorem tangent_horizontal_ne_zero (normal v : Space) (unit : ‖normal‖ = 1)
    (upward : 0 < normal 2) (tangent : inner ℝ normal v = 0) (nonzero : v ≠ 0) :
    horizontal v ≠ 0 := by
  have lower := normal_tangent_projection_lower normal v unit upward.le tangent
  intro equal
  rw [equal, norm_zero] at lower
  exact (not_lt_of_ge lower) (mul_pos upward (norm_pos_iff.mpr nonzero))

/-- The isometric inclusion of the horizontal plane into space. -/
def horizontalLift : Plane →ₗ[ℝ] Space where
  toFun v := WithLp.toLp 2 ![v 0, v 1, 0]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

theorem horizontalLift_norm (v : Plane) : ‖horizontalLift v‖ = ‖v‖ := by
  have squared : ‖horizontalLift v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three, Fin.sum_univ_two]
    simp [horizontalLift]
  nlinarith [norm_nonneg (horizontalLift v), norm_nonneg v]

def horizontalLiftIsometry : Plane →ₗᵢ[ℝ] Space :=
  { horizontalLift with norm_map' := horizontalLift_norm }

theorem dist_horizontalLift_horizontal (v : Space) :
    dist v (horizontalLift (horizontal v)) = |v 2| := by
  have squared : ‖v - horizontalLift (horizontal v)‖ ^ 2 = (v 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [horizontalLift, horizontal_apply]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (v - horizontalLift (horizontal v)), abs_nonneg (v 2),
    sq_abs (v 2)]

end Unfoldings.Cap
