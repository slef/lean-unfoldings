module

public import Unfoldings.Geometry.AngleConeBound
public import Unfoldings.Geometry.ChainInterval

/-! Quantitative length and radial margins when every heading lies in a narrow cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open InnerProductGeometry Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n) {axis : E} {halfAngle : ℝ}

/-- Projection onto the cone axis bounds the sum of the lengths by the chord. -/
theorem cone_length_bound (axis_unit : ‖axis‖ = 1)
    (nonnegative : 0 ≤ halfAngle) (acute : halfAngle < π / 2)
    (headings : ∀ i, P.edge i ≠ 0 → angle axis (P.edge i) ≤ halfAngle) :
    P.projectedLength ≤ (cos halfAngle)⁻¹ * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
  have axis_ne : axis ≠ 0 := by
    intro zero
    simp [zero] at axis_unit
  have half_pi : halfAngle ≤ π := by linarith [pi_pos]
  have cos_pos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], acute⟩
  have project (i : Fin n) : cos halfAngle * ‖P.edge i‖ ≤ inner ℝ axis (P.edge i) := by
    by_cases he : P.edge i = 0
    · simp [he]
    · simpa only [axis_unit, one_mul] using
        (angle_le_iff_cos_mul_norm_le axis_ne he nonnegative half_pi).mp (headings i he)
  have chord : cos halfAngle * P.projectedLength ≤ ‖P.vertex (Fin.last n) - P.vertex 0‖ := calc
    _ = ∑ i, cos halfAngle * ‖P.edge i‖ := by rw [projectedLength, Finset.mul_sum]
    _ ≤ ∑ i, inner ℝ axis (P.edge i) := Finset.sum_le_sum fun i _ => project i
    _ = inner ℝ axis (P.vertex (Fin.last n) - P.vertex 0) := by rw [← inner_sum, P.sum_edge]
    _ ≤ _ := by simpa only [axis_unit, one_mul] using
      real_inner_le_norm axis (P.vertex (Fin.last n) - P.vertex 0)
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ cos_pos).mpr (by simpa only [mul_comm] using chord)

/-- A cone of total aperture at most a right angle gives length constant √2. -/
theorem cone_length_bound_sqrt_two (axis_unit : ‖axis‖ = 1)
    (nonnegative : 0 ≤ halfAngle) (bound : halfAngle ≤ π / 4)
    (headings : ∀ i, P.edge i ≠ 0 → angle axis (P.edge i) ≤ halfAngle) :
    P.projectedLength ≤ √2 * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
  have acute : halfAngle < π / 2 := by linarith [pi_pos]
  have cosine := cos_le_cos_of_nonneg_of_le_pi nonnegative
    (show π / 4 ≤ π by linarith [pi_pos]) bound
  rw [cos_pi_div_four] at cosine
  have root_pos : 0 < √(2 : ℝ) := sqrt_pos.2 (by norm_num)
  have positive : 0 < cos halfAngle := (half_pos root_pos).trans_le cosine
  have inverse : (cos halfAngle)⁻¹ ≤ √2 := by
    rw [← one_div, div_le_iff₀ positive]
    nlinarith only [mul_le_mul_of_nonneg_left cosine root_pos.le, sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  exact (P.cone_length_bound axis_unit nonnegative acute headings).trans
    (mul_le_mul_of_nonneg_right inverse (norm_nonneg _))

/-- Comparing the headings directly with a direction in the same cone preserves
the radial margin for the whole chord, including the zero chord. -/
theorem cone_chord_margin (nonnegative : 0 ≤ halfAngle)
    (acute : 2 * halfAngle ≤ π / 2)
    (headings : ∀ i, P.edge i ≠ 0 → angle axis (P.edge i) ≤ halfAngle)
    {direction : E} (direction_bound : angle axis direction ≤ halfAngle) :
    cos (2 * halfAngle) * (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖direction‖) ≤
      inner ℝ (P.vertex (Fin.last n) - P.vertex 0) direction := by
  rw [← P.sum_edge, sum_inner]
  have width_nonneg : 0 ≤ 2 * halfAngle := by positivity
  have width_pi : 2 * halfAngle ≤ π := by linarith [pi_pos]
  have cos_nonneg : 0 ≤ cos (2 * halfAngle) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], acute⟩
  have pair (i : Fin n) : cos (2 * halfAngle) * (‖P.edge i‖ * ‖direction‖) ≤
      inner ℝ (P.edge i) direction := by
    by_cases he : P.edge i = 0
    · simp [he]
    by_cases hd : direction = 0
    · simp [hd]
    apply (angle_le_iff_cos_mul_norm_le he hd width_nonneg width_pi).mp
    have first := headings i he
    rw [angle_comm] at first
    have h := angle_le_angle_add_angle (P.edge i) axis direction
    linarith
  calc
    _ ≤ cos (2 * halfAngle) * ((∑ i, ‖P.edge i‖) * ‖direction‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _))
        cos_nonneg
    _ = ∑ i, cos (2 * halfAngle) * (‖P.edge i‖ * ‖direction‖) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => pair i

/-- The same axis gives the sharp length constant and radial margin on every
contiguous subpath, including those beginning at a subdivision vertex. -/
theorem cone_subpath_bounds (axis_unit : ‖axis‖ = 1)
    (nonnegative : 0 ≤ halfAngle) (bound : halfAngle ≤ π / 4)
    (headings : ∀ i, P.edge i ≠ 0 → angle axis (P.edge i) ≤ halfAngle)
    (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val) :
    let L := (P.interval j.val (i.val - j.val) (by omega)).projectedLength
    let chord := P.vertex i.castSucc - P.vertex j
    L ≤ √2 * ‖chord‖ ∧
      cos (2 * halfAngle) * (‖chord‖ * ‖P.edge i‖) ≤ inner ℝ chord (P.edge i) := by
  let A := P.interval j.val (i.val - j.val) (by omega)
  have ends : A.vertex (Fin.last (i.val - j.val)) - A.vertex 0 =
      P.vertex i.castSucc - P.vertex j := by
    simp only [A, interval_start, interval_last, Nat.add_sub_cancel' earlier]
    rfl
  have directions (k : Fin (i.val - j.val)) (genuine : A.edge k ≠ 0) :
      angle axis (A.edge k) ≤ halfAngle :=
    headings ⟨j.val + k.val, by have := k.isLt; omega⟩ genuine
  have radial (genuine : P.edge i ≠ 0) :
      cos (2 * halfAngle) * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i) := by
    rw [← ends]
    exact A.cone_chord_margin nonnegative (by linarith only [bound])
      directions (headings i genuine)
  refine ⟨?_, ?_⟩
  · simpa only [ends] using A.cone_length_bound_sqrt_two axis_unit nonnegative bound directions
  · by_cases genuine : P.edge i = 0
    · simp [genuine]
    · exact radial genuine

end Unfoldings.PolygonalChain
