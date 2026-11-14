module

public import Unfoldings.Geometry.OpeningBudget

/-! Curvature spent once controls actual suffix rotations and real heading oscillation. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} {V : Type*} [Fintype V]

theorem openingBudget_le_curvature (events : List (Opening n)) (vertex : Opening n → V)
    (curvature : V → ℝ) (nonnegative : ∀ v, 0 ≤ curvature v)
    (spent_once : (events.map vertex).Nodup)
    (angles : ∀ event ∈ events, |event.angle| ≤ curvature (vertex event)) :
    openingBudget events ≤ ∑ v, curvature v := by
  classical
  have total := List.sum_toFinset curvature spent_once
  rw [List.map_map] at total
  calc
    openingBudget events ≤ (events.map (fun event => curvature (vertex event))).sum :=
      List.sum_le_sum angles
    _ = ∑ v ∈ (events.map vertex).toFinset, curvature v := total.symm
    _ ≤ ∑ v, curvature v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => nonnegative v)

/-- Signed comparisons with an original reference bank have oscillation at most twice the
original curvature budget, even when different prefixes use different signs. -/
theorem signed_curvature_heading_oscillation {A : Type*} (curvature : V → ℝ)
    (nonnegative : ∀ v, 0 ≤ curvature v) (coefficient : A → V → ℝ)
    (signed : ∀ i v, |coefficient i v| ≤ 1) (i j : A) :
    |(∑ v, coefficient i v * curvature v) - (∑ v, coefficient j v * curvature v)| ≤
      2 * ∑ v, curvature v := by
  have bound (k : A) : |∑ v, coefficient k v * curvature v| ≤ ∑ v, curvature v := by
    calc
      _ ≤ ∑ v, |coefficient k v * curvature v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v, curvature v := by
        apply Finset.sum_le_sum
        intro v _
        rw [abs_mul, abs_of_nonneg (nonnegative v)]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (signed k v) (nonnegative v)
  have triangle :
      |(∑ v, coefficient i v * curvature v) - (∑ v, coefficient j v * curvature v)| ≤
        |∑ v, coefficient i v * curvature v| + |∑ v, coefficient j v * curvature v| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (∑ v, coefficient i v * curvature v) (-(∑ v, coefficient j v * curvature v))
  linarith [bound i, bound j]

end Unfoldings.PolygonalChain
