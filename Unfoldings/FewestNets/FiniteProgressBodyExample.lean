module

public import Unfoldings.FewestNets.CheckedProgressBody
public import Unfoldings.FewestNets.FiniteVisualExample

/-! Check the first saved body's inscribed disk and its cell's length ratio. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

def q100FirstInradius : ℚ := 574077 / 1000000

def q100FirstLengthConstant : ℚ := 1751491 / 1000000

set_option maxRecDepth 8192 in
theorem closedBall_subset_first_progressBody :
    Metric.closedBall (0 : Plane) (q100FirstInradius : ℝ) ⊆
      convexHull ℝ (Set.range q100FirstBody) :=
  closedBall_subset_progressBody_of_check certificateDenominator_pos checkQ100FirstBody
    (CheckedReal.rat certificateDenominator q100FirstInradius)
    (by norm_num [q100FirstInradius]) (by decide +kernel)

set_option maxRecDepth 8192 in
theorem q100FirstCell_norm_lt_length_mul_inradius {x : Plane}
    (member : x ∈ convexHull ℝ (Set.range q100FirstCorner)) :
    ‖x‖ < (q100FirstLengthConstant : ℝ) * (q100FirstInradius : ℝ) := by
  let R := (q100FirstLengthConstant : ℝ) * (q100FirstInradius : ℝ)
  have inside : convexHull ℝ (Set.range q100FirstCorner) ⊆ Metric.ball (0 : Plane) R := by
    apply convexHull_min _ (convex_ball _ _)
    rintro _ ⟨i, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using
      CheckedReal.lt_of_isLT certificateDenominator_pos
        (CheckedPlane.norm certificateDenominator_pos (checkQ100FirstCorner i))
        ((CheckedReal.rat certificateDenominator q100FirstLengthConstant).mul
          certificateDenominator_pos (CheckedReal.rat certificateDenominator q100FirstInradius))
        (by fin_cases i <;> decide +kernel)
  simpa only [Metric.mem_ball, dist_zero_right] using inside member

end Unfoldings.FewestNets
