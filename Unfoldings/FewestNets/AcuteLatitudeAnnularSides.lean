module

public import Unfoldings.FewestNets.AcuteLatitudeAnnularCorners
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! The revised annular chart radius bounds the actual spherical side lengths and perimeter. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real InnerProductGeometry

/-- The minor-arc length of an actual spherical triangle side. -/
def annularSideLength {a : ℝ} (i : AnnularTriangle a) (j : Fin 3) : ℝ :=
  angle (annularVertices a i j) (annularVertices a i (j + 1))

/-- The longest side of the original spherical chord triangle. -/
def annularLongestSide {a : ℝ} (i : AnnularTriangle a) : ℝ :=
  max (annularSideLength i 0) (max (annularSideLength i 1) (annularSideLength i 2))

/-- The perimeter counts the three actual spherical sides exactly once. -/
def annularPerimeter {a : ℝ} (i : AnnularTriangle a) : ℝ := ∑ j : Fin 3, annularSideLength i j

theorem annularSideLength_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (j : Fin 3) : 0 < annularSideLength i j := by
  let u := annularVertices a i j
  let v := annularVertices a i (j + 1)
  have different : u ≠ v := by
    intro same
    have at_vertex (k : Fin 3) :
        chordBasis positive small (.inr (.inl i)) k = annularVertices a i k :=
      chordBasis_apply positive small (.inr (.inl i)) k
    have index : j = j + 1 := (chordBasis positive small (.inr (.inl i))).injective
      ((at_vertex j).trans (same.trans (at_vertex (j + 1)).symm))
    exact (show j ≠ j + 1 from by fin_cases j <;> decide) index
  change 0 < angle u v
  refine lt_of_le_of_ne (angle_nonneg _ _) ?_
  intro zero
  obtain ⟨_, t, positive_t, scale⟩ := angle_eq_zero_iff.mp zero.symm
  have norm := congrArg (fun z : Space => ‖z‖) scale
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos positive_t,
    show ‖u‖ = 1 from annularVertices_unit a i j,
    show ‖v‖ = 1 from annularVertices_unit a i (j + 1), mul_one] at norm
  exact different ((by rw [scale, ← norm, one_smul] : v = u).symm)

theorem annularSideLength_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) (j : Fin 3) : annularSideLength i j < 1.136 * radius a := by
  let center := latitudeSite (chartColatitude a i.1.val) (annularChartLongitude a i)
  have near (k : Fin 3) : angle center (annularVertices a i k) < 0.568 * radius a := by
    obtain ⟨row, w, which, offset, vertex⟩ := annularVertex_offset positive small i k
    rw [vertex]
    exact (chartSite_bounds positive small i.1.isLt which (annularChartLongitude a i) w offset).2.2.2.2.2
  have triangle := angle_le_angle_add_angle (annularVertices a i j) center (annularVertices a i (j + 1))
  rw [angle_comm (annularVertices a i j) center] at triangle
  unfold annularSideLength
  linarith only [triangle, near j, near (j + 1)]

theorem annularPerimeter_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) : annularPerimeter i ≤ 6 * (0.568 * radius a) := by
  calc
    _ ≤ ∑ _ : Fin 3, 1.136 * radius a :=
      Finset.sum_le_sum (fun j _ => (annularSideLength_lt positive small i j).le)
    _ = _ := by simp; ring

/-- The actual longest-side multiplier is strictly below the annular cutoff constant. -/
theorem annular_longestSide_factor {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    0 < 2 * annularLongestSide i / (π * sin (annularLongestSide i)) ∧
      2 * annularLongestSide i / (π * sin (annularLongestSide i)) < 0.645 := by
  have lo : 0 < annularLongestSide i := (annularSideLength_pos positive small i 0).trans_le (le_max_left _ _)
  have hi : annularLongestSide i < 1.136 * radius a :=
    max_lt (annularSideLength_lt positive small i 0) (max_lt
      (annularSideLength_lt positive small i 1) (annularSideLength_lt positive small i 2))
  have upper : annularLongestSide i ≤ 0.266 := by linarith only [hi, radius_lt small]
  have sine := sin_pos_of_pos_of_lt_pi lo (by linarith only [upper, pi_gt_three])
  exact ⟨div_pos (mul_pos (by norm_num) lo) (mul_pos pi_pos sine),
    tri_longest_side_factor lo upper⟩

/-- The cutoff sum and perimeter alternative for the actual spherical triangle
both satisfy the annular crossing estimate's numerical bound. -/
theorem annular_crossing_cutoff_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : AnnularTriangle a) :
    let l := annularLongestSide i
    let c := 2 * l / (π * sin l)
    max (∑ j : Fin 3, c / sin (min (annularCornerAngle i j) (π / 2)))
      (annularPerimeter i / (π * (1 / 10))) < 2.462 / a := by
  dsimp only
  let c := 2 * annularLongestSide i / (π * sin (annularLongestSide i))
  let b (j : Fin 3) := c / sin (min (annularCornerAngle i j) (π / 2))
  change max (∑ j, b j) _ < _
  obtain ⟨c_pos, c_lt⟩ := annular_longestSide_factor positive small i
  obtain ⟨apex, base⟩ := annular_spherical_capped_sines positive small i
  have ratio : spacing a / radius a = 0.56 * a := by
    unfold spacing
    field_simp [(radius_pos positive).ne']
  rw [ratio, ← mul_assoc] at apex
  have cutoff (j : Fin 3) {d : ℝ} (d_pos : 0 < d)
      (h : d ≤ sin (min (annularCornerAngle i j) (π / 2))) : b j ≤ 0.645 / d :=
    (div_le_div_of_nonneg_left c_pos.le d_pos h).trans
      (div_le_div_of_nonneg_right c_lt.le d_pos.le)
  have apex_bound := cutoff 2 (show 0 < 0.664 * 0.56 * a by positivity) apex.le
  have base_bound (j : Fin 3) (ne_apex : j ≠ 2) := cutoff j
    (show 0 < (0.93 : ℝ) by norm_num) (base j ne_apex).le
  have sum : (∑ j, b j) = b 2 + b 0 + b 1 := by
    rw [Fin.sum_univ_three]
    ring
  rw [sum]
  exact tri_count_max_lt positive small apex_bound (base_bound 0 (by decide))
    (base_bound 1 (by decide)) (annularPerimeter_le positive small i)

end Unfoldings.FewestNets.AcuteLatitudeGrid
