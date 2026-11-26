module

public import Unfoldings.Topology.SignedGraphLenses
public import Unfoldings.Geometry.AffineOrientation

/-! The sign of a lens is fixed by its two initial or terminal rays. -/

@[expose] public section

namespace Unfoldings.PlanarTopology

private theorem orient_mul_eq_graphDiff (f g : ℝ → ℝ) {p u v : Plane} {s t r : ℝ}
    (on_f : graphPoint f r = p + s • u) (on_g : graphPoint g r = p + t • v) :
    (g r - f r) * u 0 = t * orient 0 u v := by
  have fx := congrArg (fun x : Plane => x 0) on_f
  have gx := congrArg (fun x : Plane => x 0) on_g
  have fy := congrArg (fun x : Plane => x 1) on_f
  have gy := congrArg (fun x : Plane => x 1) on_g
  change r = p 0 + s * u 0 at fx
  change r = p 0 + t * v 0 at gx
  change f r = p 1 + s * u 1 at fy
  change g r = p 1 + t * v 1 at gy
  rw [fy, gy]
  simp only [orient, PiLp.zero_apply, sub_zero]
  linear_combination u 1 * (fx - gx)

/-- The lens sign at its increasing endpoint agrees with the determinant of
the two forward rays. -/
theorem graphLensSign_of_forward_rays {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b r s t : ℝ} (at_r : r ∈ Set.Ioo a b) (separate : ∀ x ∈ Set.Ioo a b, f x ≠ g x)
    {p u v : Plane} (forward : 0 < u 0) (t_pos : 0 < t)
    (on_f : graphPoint f r = p + s • u) (on_g : graphPoint g r = p + t • v) :
    graphLensSign f g a b = if 0 ≤ orient 0 u v then 1 else -1 := by
  have mid : (a + b) / 2 ∈ Set.Ioo a b :=
    ⟨by linarith only [at_r.1, at_r.2], by linarith only [at_r.1, at_r.2]⟩
  have eq := orient_mul_eq_graphDiff f g on_f on_g
  have signs : f r < g r ↔ 0 ≤ orient 0 u v := by
    constructor
    · intro less
      have positive := mul_pos (sub_pos.mpr less) forward
      rw [eq] at positive
      exact (pos_of_mul_pos_right positive t_pos.le).le
    · intro positive
      rcases lt_or_gt_of_ne (separate r at_r) with less | greater
      · exact less
      · have neg := mul_neg_of_neg_of_pos (sub_neg.mpr greater) forward
        rw [eq] at neg
        exact (not_lt_of_ge (mul_nonneg t_pos.le positive) neg).elim
  have order := (graph_order_iff_at hf hg mid at_r separate).trans signs
  unfold graphLensSign
  by_cases pos : 0 ≤ orient 0 u v
  · rw [if_pos (order.mpr pos), if_pos pos]
  · rw [if_neg (fun h => pos (order.mp h)), if_neg pos]

/-- The lens sign at its decreasing endpoint is the opposite of the
determinant sign of the two backward rays. -/
theorem graphLensSign_of_backward_rays {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b r s t : ℝ} (at_r : r ∈ Set.Ioo a b) (separate : ∀ x ∈ Set.Ioo a b, f x ≠ g x)
    {p u v : Plane} (backward : u 0 < 0) (t_pos : 0 < t)
    (on_f : graphPoint f r = p + s • u) (on_g : graphPoint g r = p + t • v) :
    graphLensSign f g a b = -(if 0 ≤ orient 0 u v then 1 else -1) := by
  have mid : (a + b) / 2 ∈ Set.Ioo a b :=
    ⟨by linarith only [at_r.1, at_r.2], by linarith only [at_r.1, at_r.2]⟩
  have eq := orient_mul_eq_graphDiff f g on_f on_g
  have signs : f r < g r ↔ orient 0 u v < 0 := by
    constructor
    · intro less
      have neg := mul_neg_of_pos_of_neg (sub_pos.mpr less) backward
      rw [eq] at neg
      exact neg_of_mul_neg_right neg t_pos.le
    · intro neg
      rcases lt_or_gt_of_ne (separate r at_r) with less | greater
      · exact less
      · have positive := mul_pos_of_neg_of_neg (sub_neg.mpr greater) backward
        rw [eq] at positive
        exact ((mul_neg_of_pos_of_neg t_pos neg).not_gt positive).elim
  have order := (graph_order_iff_at hf hg mid at_r separate).trans signs
  unfold graphLensSign
  by_cases pos : 0 ≤ orient 0 u v
  · rw [if_neg (fun h => (not_lt_of_ge pos) (order.mp h)), if_pos pos]
  · rw [if_pos (order.mpr (lt_of_not_ge pos)), if_neg pos, neg_neg]

end Unfoldings.PlanarTopology
