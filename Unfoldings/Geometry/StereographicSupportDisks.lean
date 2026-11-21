module

public import Unfoldings.Geometry.StereographicArea
public import Mathlib.Analysis.Convex.StrictConvexSpace

/-! A strictly inward support hemisphere becomes a disk in the centered chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

private theorem support_disk_square (n : Space) (up : 0 < n 2) (x : Plane) :
    (n 2) ^ 2 * ‖x - (n 2)⁻¹ • horizontal n‖ ^ 2 =
      ‖n‖ ^ 2 - n 2 * (2 * inner ℝ (horizontal n) x + n 2 * (1 - ‖x‖ ^ 2)) := by
  let k := n 2
  have k_ne : k ≠ 0 := up.ne'
  rw [norm_sub_pow_two_real, real_inner_smul_right, real_inner_comm (horizontal n) x,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr up.le), mul_pow,
    horizontal_norm_sq n]
  change k ^ 2 * (‖x‖ ^ 2 - 2 * (k⁻¹ * inner ℝ (horizontal n) x) +
      k⁻¹ ^ 2 * ‖horizontal n‖ ^ 2) = ‖horizontal n‖ ^ 2 + k ^ 2 -
    k * (2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2))
  field_simp [k_ne]
  ring

/-- A supporting hemisphere whose inward normal pairs positively with the
center projects to the closed disk given by completing the square. -/
theorem inverseStereographic_hemisphere_eq_closedBall (n : Space) (up : 0 < n 2) :
    {x | 0 ≤ inner ℝ n (inverseStereographic x)} =
      Metric.closedBall ((n 2)⁻¹ • horizontal n) (‖n‖ / n 2) := by
  let k := n 2
  ext x
  rw [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, inverseStereographic_inner]
  change 0 ≤ (2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2)) / (1 + ‖x‖ ^ 2) ↔
    ‖x - k⁻¹ • horizontal n‖ ≤ ‖n‖ / k
  have formula : k ^ 2 * ‖x - k⁻¹ • horizontal n‖ ^ 2 =
      ‖n‖ ^ 2 - k * (2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2)) :=
    support_disk_square n up x
  have k2_pos : 0 < k ^ 2 := sq_pos_of_pos up
  rw [← sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) up.le), div_pow,
    le_div_iff₀ k2_pos, mul_comm (‖x - k⁻¹ • horizontal n‖ ^ 2), formula]
  have den_pos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  constructor
  · intro h
    have h' := (le_div_iff₀ den_pos).mp h
    simp only [zero_mul] at h'
    exact sub_le_self _ (mul_nonneg up.le h')
  · intro h
    exact div_nonneg (nonneg_of_mul_nonneg_right (by linarith only [h]) up) den_pos.le

/-- The zero set of a strictly inward spherical support is the full sphere
of the corresponding support disk in the chart. -/
theorem inverseStereographic_support_zero_iff_dist_eq (n : Space) (up : 0 < n 2)
    (x : Plane) :
    inner ℝ n (inverseStereographic x) = 0 ↔
      dist x ((n 2)⁻¹ • horizontal n) = ‖n‖ / n 2 := by
  let k := n 2
  have positive : 0 < k ^ 2 := sq_pos_of_pos up
  have den_ne : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  rw [inverseStereographic_inner, div_eq_zero_iff, or_iff_left den_ne, dist_eq_norm]
  change 2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2) = 0 ↔
    ‖x - k⁻¹ • horizontal n‖ = ‖n‖ / k
  rw [← sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) up.le), div_pow,
    eq_div_iff positive.ne', mul_comm (‖x - k⁻¹ • horizontal n‖ ^ 2)]
  have formula : k ^ 2 * ‖x - k⁻¹ • horizontal n‖ ^ 2 =
      ‖n‖ ^ 2 - k * (2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2)) :=
    support_disk_square n up x
  rw [formula]
  constructor
  · intro zero
    rw [zero, mul_zero, sub_zero]
  · intro equal
    have prod : k * (2 * inner ℝ (horizontal n) x + k * (1 - ‖x‖ ^ 2)) = 0 := by
      linarith only [equal]
    exact (mul_eq_zero.mp prod).resolve_left up.ne'

/-- Finitely many strictly inward supports give a strictly convex chart. -/
theorem strictConvex_inverseStereographic_region {I : Type*} [Finite I] (normal : I → Space)
    (up : ∀ i, 0 < normal i 2) :
    StrictConvex ℝ {x | ∀ i, 0 ≤ inner ℝ (normal i) (inverseStereographic x)} := by
  let disk (i : I) := {x | 0 ≤ inner ℝ (normal i) (inverseStereographic x)}
  have each (i : I) : StrictConvex ℝ (disk i) := by
    change StrictConvex ℝ {x | 0 ≤ inner ℝ (normal i) (inverseStereographic x)}
    rw [inverseStereographic_hemisphere_eq_closedBall _ (up i)]
    exact strictConvex_closedBall ℝ _ _
  rw [show {x | ∀ i, 0 ≤ inner ℝ (normal i) (inverseStereographic x)} = ⋂ i, disk i by
    ext x; simp [disk]]
  rw [strictConvex_iff_openSegment_subset]
  intro x hx y hy ne v hv
  have included : (⋂ i, interior (disk i)) ⊆ interior (⋂ i, disk i) :=
    interior_maximal (Set.iInter_mono fun _ => interior_subset)
      (isOpen_iInter_of_finite fun _ => isOpen_interior)
  apply included
  apply Set.mem_iInter.mpr
  intro i
  exact (strictConvex_iff_openSegment_subset.mp (each i))
    (Set.mem_iInter.mp hx i) (Set.mem_iInter.mp hy i) ne hv

end Unfoldings.Cap
