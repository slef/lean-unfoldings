module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith

/-! Every interior point of a planar domain can be extended slightly along its radial line. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_gt_one_smul_mem_of_interior {s : Set E} {z : E} (inside : z ∈ interior s) :
    ∃ t : ℝ, 1 < t ∧ t • z ∈ s := by
  have continuous : Continuous (fun t : ℝ => t • z) := continuous_id.smul continuous_const
  have preimage_open : IsOpen {t : ℝ | t • z ∈ interior s} := isOpen_interior.preimage continuous
  have at_one : (1 : ℝ) ∈ {t : ℝ | t • z ∈ interior s} := by
    change (1 : ℝ) • z ∈ interior s
    rw [one_smul]
    exact inside
  obtain ⟨r, positive, ball⟩ := Metric.isOpen_iff.mp preimage_open 1 at_one
  let t := 1 + r / 2
  have gt_one : 1 < t := by dsimp [t]; linarith
  have near : t ∈ Metric.ball (1 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq]
    have difference : t - 1 = r / 2 := by dsimp [t]; ring
    rw [difference, abs_of_pos (half_pos positive)]
    linarith
  exact ⟨t, gt_one, interior_subset (ball near)⟩

end Unfoldings
