module

public import Unfoldings.FewestNets.CheckedDevelopment
public import Unfoldings.FewestNets.FiniteMeshExample

/-! Numerical development checks for the first frequency-100 face record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real CheckedReal MeshStar

/-- The uniform frequency-100 tilt used for this face record. -/
def q100UniformTilt : ℝ := (3 - Real.sqrt 5) / 100

def checkQ100UniformTilt : CheckedReal certificateDenominator q100UniformTilt :=
  let pos := certificateDenominator_pos
  ((rat certificateDenominator 3).sub ((rat certificateDenominator 5).sqrt pos)).div pos
    (rat certificateDenominator 100) |>.convert (by simp [q100UniformTilt])

theorem q100UniformTilt_tan_half_sq_lt_one : tan (q100UniformTilt / 2) ^ 2 < 1 := by
  have sq5 : Real.sqrt 5 < 3 := (sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have pos : 0 ≤ q100UniformTilt / 2 := by
    unfold q100UniformTilt
    linarith
  have small : q100UniformTilt / 2 < π / 4 := by
    unfold q100UniformTilt
    linarith [sqrt_nonneg (5 : ℝ), pi_gt_three]
  have hp : q100UniformTilt / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hq : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have bound := strictMonoOn_tan hp hq small
  rw [tan_pi_div_four] at bound
  have nonneg := tan_nonneg_of_nonneg_of_le_pi_div_two pos hp.2.le
  simpa only [one_pow] using (sq_lt_sq₀ nonneg zero_le_one).mpr bound

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction evaluates the Taylor and fixed-point checks for all three gaps.
theorem developmentGaps_q100_face_one_one (i : Fin 3) :
    0 < developmentGaps q100UniformTilt 0.0073243 1.751491 i := by
  let pos := certificateDenominator_pos
  let cg : CheckedReal certificateDenominator (0.0073243 : ℝ) :=
    (rat certificateDenominator 0.0073243).convert (by norm_num)
  let cl : CheckedReal certificateDenominator (1.751491 : ℝ) :=
    (rat certificateDenominator 1.751491).convert (by norm_num)
  let check := checkDevelopmentGaps pos checkQ100UniformTilt cg cl
    q100UniformTilt_tan_half_sq_lt_one (by norm_num) (by norm_num) 12
  have h : (List.finRange 3).all (fun j => (check j).isPositive) = true := by
    decide +kernel
  exact positive_of_isPositive pos (check i) (List.all_eq_true.mp h i (List.mem_finRange i))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction evaluates the Taylor enclosures for the actual rational cotangent bound.
theorem cotangent_margin_q100_face_one_one :
    0 < sin (8.159 * π / 180) - 0.1433718319 * cos (8.159 * π / 180) := by
  let pos := certificateDenominator_pos
  let x : CheckedReal certificateDenominator (8.159 * π / 180) :=
    (((rat certificateDenominator 8.159).mul pos (checkPi certificateDenominator)).div pos
      (rat certificateDenominator 180)).convert (by norm_num)
  let cot : CheckedReal certificateDenominator (0.1433718319 : ℝ) :=
    (rat certificateDenominator 0.1433718319).convert (by norm_num)
  let value := (x.checkSin pos 12).sub (cot.mul pos (x.checkCos pos 12))
  exact positive_of_isPositive pos value (by decide +kernel)

end Unfoldings.FewestNets
