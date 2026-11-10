module

public import Unfoldings.Cap.Projection
public import Unfoldings.Geometry.UniformAngles
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Uniform projection angle distortion

The normal-height threshold depends only on the requested angular error.
Neither the number of triangles nor the number of turns occurs in this bound.
This is a local angle estimate; bounding an entire path's turn is a separate result.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry

/-- Unit tangent directions have uniformly small angle distortion as the normal becomes vertical. -/
theorem exists_unit_projection_angle_height {ε : ℝ} (positive : 0 < ε) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ normal a b : Space,
      ‖normal‖ = 1 → c ≤ normal 2 → ‖a‖ = 1 → ‖b‖ = 1 →
      inner ℝ normal a = 0 → inner ℝ normal b = 0 →
      |angle (horizontal a) (horizontal b) - angle a b| < ε := by
  obtain ⟨δ, δpos, bound⟩ := exists_uniform_angle_delta (E := Space) positive
  let η : ℝ := min (δ ^ 2 / 4) (1 / 4)
  have ηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have ηsmall : η ≤ 1 / 4 := min_le_right _ _
  have ηδ : η ≤ δ ^ 2 / 4 := min_le_left _ _
  let c : ℝ := 1 - η
  have cpos : 0 < c := by dsimp [c]; linarith
  have chalf : 1 / 2 ≤ c := by dsimp [c]; linarith
  refine ⟨c, ⟨cpos, by dsimp [c]; linarith⟩, ?_⟩
  intro normal a b unit height au bu tangent_a tangent_b
  have small (v : Space) (vu : ‖v‖ = 1) (vt : inner ℝ normal v = 0) : |v 2| < δ := by
    have square := tangent_vertical_sq_le normal v unit cpos.le height vt
    rw [vu] at square
    have δsquare : 0 < δ ^ 2 := sq_pos_of_pos δpos
    dsimp [c] at square
    nlinarith [sq_abs (v 2), abs_nonneg (v 2), sq_nonneg η]
  have lower (v : Space) (vu : ‖v‖ = 1) (vt : inner ℝ normal v = 0) :
      1 / 2 ≤ ‖horizontalLift (horizontal v)‖ := by
    rw [horizontalLift_norm]
    have estimate := normal_tangent_projection_lower normal v unit (cpos.le.trans height) vt
    rw [vu, mul_one] at estimate
    exact chalf.trans (height.trans estimate)
  have upper (v : Space) (vu : ‖v‖ = 1) : ‖horizontalLift (horizontal v)‖ ≤ 1 := by
    rw [horizontalLift_norm]
    exact (horizontal_norm_le v).trans_eq vu
  have result := bound a b (horizontalLift (horizontal a)) (horizontalLift (horizontal b))
    (by rw [au]; norm_num) au.le (by rw [bu]; norm_num) bu.le
    (lower a au tangent_a) (upper a au) (lower b bu tangent_b) (upper b bu)
    (by rw [dist_horizontalLift_horizontal]; exact small a au tangent_a)
    (by rw [dist_horizontalLift_horizontal]; exact small b bu tangent_b)
  have angles : angle (horizontalLift (horizontal a)) (horizontalLift (horizontal b)) =
      angle (horizontal a) (horizontal b) := horizontalLiftIsometry.angle_map _ _
  rw [angles, abs_sub_comm] at result
  exact result

/-- The same threshold works at every scale and for all nonzero tangent directions. -/
theorem exists_projection_angle_height {ε : ℝ} (positive : 0 < ε) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ normal a b : Space,
      ‖normal‖ = 1 → c ≤ normal 2 → a ≠ 0 → b ≠ 0 →
      inner ℝ normal a = 0 → inner ℝ normal b = 0 →
      |angle (horizontal a) (horizontal b) - angle a b| < ε := by
  obtain ⟨c, bounds, estimate⟩ := exists_unit_projection_angle_height positive
  refine ⟨c, bounds, fun normal a b unit height an bn tangent_a tangent_b => ?_⟩
  have result := estimate normal (NormedSpace.normalize a) (NormedSpace.normalize b)
    unit height (NormedSpace.norm_normalize an) (NormedSpace.norm_normalize bn)
    (by simp [NormedSpace.normalize, inner_smul_right, tangent_a])
    (by simp [NormedSpace.normalize, inner_smul_right, tangent_b])
  have projected (v : Space) (vn : v ≠ 0) (w : Plane) :
      angle (horizontal (NormedSpace.normalize v)) w = angle (horizontal v) w := by
    rw [NormedSpace.normalize, map_smul, angle_smul_left_of_pos _ _ (by positivity)]
  rw [projected a an, angle_comm (horizontal a), projected b bn,
    angle_comm _ (horizontal a), angle_normalize_left, angle_normalize_right] at result
  exact result

/-- Every strict normal-height threshold contains a positive interval of tilt angles. -/
theorem exists_positive_tilt_of_height {c : ℝ} (below_one : c < 1) :
    ∃ φ > 0, φ < Real.pi / 2 ∧ c < Real.cos φ := by
  have near : ∀ᶠ φ : ℝ in nhds 0, c < Real.cos φ :=
    (Real.continuous_cos.continuousAt.eventually (lt_mem_nhds (by simpa using below_one)))
  obtain ⟨δ, δpos, bound⟩ := Metric.eventually_nhds_iff.mp near
  let φ := min (δ / 2) (Real.pi / 4)
  have φpos : 0 < φ := lt_min (by positivity) (by positivity)
  have φδ : φ < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨φ, φpos, (min_le_right _ _).trans_lt (by linarith [Real.pi_pos]), ?_⟩
  apply bound
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos φpos] using φδ

end Unfoldings.Cap
