module

public import Unfoldings.Topology.SubtreeWeights

/-! Only vertices with positive weight need a root-path crossing bound. -/

@[expose] public section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Fintype V] (P : AscendingParents V)

open scoped Classical in
/-- Zero-weight auxiliary branches impose no geometric condition on their root paths. -/
theorem abs_sum_subtree_weights_le_of_pos (curvature crossing : V → ℝ)
    (nonnegative : ∀ v, 0 ≤ curvature v)
    (path_bound : ∀ v, 0 < curvature v →
      |∑ i : Fin (P.distanceToRoot v), crossing (P.parent^[i.val] v)| ≤ 1) :
    |∑ e : V, if e ∉ P.roots then crossing e * (∑ v ∈ P.descendants e, curvature v) else 0| ≤
      ∑ v : V, curvature v := by
  classical
  rw [P.sum_subtree_weights_eq_rootPaths]
  calc
    _ ≤ ∑ v : V, |curvature v *
        (∑ i : Fin (P.distanceToRoot v), crossing (P.parent^[i.val] v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases positive : 0 < curvature v
      · rw [abs_mul, abs_of_nonneg (nonnegative v)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (path_bound v positive)
          (nonnegative v)
      · have zero : curvature v = 0 := le_antisymm (not_lt.mp positive) (nonnegative v)
        simp only [zero, zero_mul, abs_zero, le_refl]

end Unfoldings.AscendingParents
