module

public import Unfoldings.Geometry.PlanarWidthArea
public import Unfoldings.Geometry.StereographicAngularDistance
public import Unfoldings.Geometry.StereographicAreaExpansion
public import Unfoldings.Geometry.TwoSideChordBound

/-! Transfer the planar width estimate to spherical side lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory InnerProductGeometry
open scoped BigOperators ENNReal

/-- The chord estimate in a centered chart, with the area left in planar units.
The input headings are those of the projected chords, in cyclic order beginning
at the positive horizontal direction. The horizontal chord bounds the
spherical diameter after multiplying its length by two. -/
theorem exists_omit_two_spherical_chords_of_small_minimum {s : Set Plane} (compact : IsCompact s)
    (convex : Convex ℝ s) (unit_disk : ∀ x ∈ s, ‖x‖ ≤ 1)
    {a b : Plane} (ha : a ∈ s) (hb : b ∈ s) (horizontal_base : a 1 = b 1)
    {d : ℝ} (d_nonneg : 0 ≤ d) (d_le : d ≤ 2 * dist a b)
    (n : ℕ) (p : ℕ → Plane) (heading : ℕ → ℝ) (points : ∀ i ≤ n, p i ∈ s)
    (closed : p n = p 0) {η : ℝ} (positive : 0 < η) (small : η ≤ Real.pi / 2)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (gaps : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (vertical : ∀ i < n, p (i + 1) 1 - p i 1 = dist (p i) (p (i + 1)) * Real.sin (heading i)) :
    ∃ omitted : Finset ℕ, omitted ⊆ Finset.range n ∧ omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.range n \ omitted,
        angle (inverseStereographic (p i)) (inverseStereographic (p (i + 1)))) *
        d * Real.sin η ≤ 16 * (volume : Measure Plane).real s := by
  have ne : s.Nonempty := ⟨a, ha⟩
  have coord_cont : Continuous (fun x : Plane => x 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous
  obtain ⟨lo, hlo, min⟩ := compact.exists_isMinOn ne coord_cont.continuousOn
  obtain ⟨hi, hhi, max⟩ := compact.exists_isMaxOn ne coord_cont.continuousOn
  have min := isMinOn_iff.mp min
  have max := isMaxOn_iff.mp max
  have area := chord_mul_height_span_le_twice_area compact convex ha hb hlo hhi horizontal_base
    (min a ha) (max a ha)
  obtain ⟨omitted, subset, size, length⟩ := exists_omit_two_chords_with_cutoff n heading
    (fun i => dist (p i) (p (i + 1))) (fun i => p i 1) positive small le_rfl head_in gaps
    (fun _ _ => dist_nonneg) vertical (congrArg (fun x : Plane => x 1) closed)
    (fun i hi' => ⟨min (p i) (points i hi'), max (p i) (points i hi')⟩)
  let S := ∑ i ∈ Finset.range n \ omitted,
    angle (inverseStereographic (p i)) (inverseStereographic (p (i + 1)))
  let L := ∑ i ∈ Finset.range n \ omitted, dist (p i) (p (i + 1))
  have compare : S ≤ 2 * L := by
    dsimp only [S, L]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi'
    have hin := Finset.mem_range.mp (Finset.mem_sdiff.mp hi').1
    rw [dist_eq_norm]
    exact angle_inverseStereographic_le
      (unit_disk _ (points i (by omega))) (unit_disk _ (points (i + 1) (by omega)))
  have sin_nonneg : 0 ≤ Real.sin η :=
    Real.sin_nonneg_of_nonneg_of_le_pi positive.le (by linarith only [small, Real.pi_pos])
  have width_nonneg : 0 ≤ hi 1 - lo 1 := sub_nonneg.mpr (min hi hhi)
  refine ⟨omitted, subset, size, ?_⟩
  change S * d * Real.sin η ≤ _
  calc
    _ = S * Real.sin η * d := by ring
    _ ≤ (2 * L * Real.sin η) * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right compare sin_nonneg) d_nonneg
    _ ≤ (4 * (hi 1 - lo 1)) * d := by
      apply mul_le_mul_of_nonneg_right _ d_nonneg
      change L * Real.sin η ≤ 2 * (hi 1 - lo 1) at length
      linarith only [length]
    _ ≤ (4 * (hi 1 - lo 1)) * (2 * dist a b) :=
      mul_le_mul_of_nonneg_left d_le (by positivity)
    _ ≤ _ := by linarith only [area]

/-- The half-angle bound for arbitrary positive minimum turn up to a straight angle. -/
theorem exists_omit_two_spherical_chords {s : Set Plane} (compact : IsCompact s)
    (convex : Convex ℝ s) (unit_disk : ∀ x ∈ s, ‖x‖ ≤ 1)
    {a b : Plane} (ha : a ∈ s) (hb : b ∈ s) (horizontal_base : a 1 = b 1)
    {d : ℝ} (d_nonneg : 0 ≤ d) (d_le : d ≤ 2 * dist a b)
    (n : ℕ) (p : ℕ → Plane) (heading : ℕ → ℝ) (points : ∀ i ≤ n, p i ∈ s)
    (closed : p n = p 0) {η : ℝ} (positive : 0 < η) (small : η ≤ Real.pi)
    (head_in : ∀ i < n, 0 ≤ heading i ∧ heading i ≤ 2 * Real.pi)
    (gaps : ∀ i j, i < j → j < n →
      η ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - η)
    (vertical : ∀ i < n, p (i + 1) 1 - p i 1 = dist (p i) (p (i + 1)) * Real.sin (heading i)) :
    ∃ omitted : Finset ℕ, omitted ⊆ Finset.range n ∧ omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.range n \ omitted,
        angle (inverseStereographic (p i)) (inverseStereographic (p (i + 1)))) *
        d * Real.sin (η / 2) ≤ 16 * (volume : Measure Plane).real s :=
  exists_omit_two_spherical_chords_of_small_minimum compact convex unit_disk ha hb horizontal_base
    d_nonneg d_le n p heading points closed (η := η / 2)
    (by linarith only [positive]) (by linarith only [small]) head_in
    (fun i j hij hj => ⟨by linarith only [(gaps i j hij hj).1, positive],
      by linarith only [(gaps i j hij hj).2, positive]⟩) vertical

/-- The angular diameter bound follows from a planar diameter bound. -/
theorem spherical_diameter_le_of_planar_diameter {s : Set Plane} {D : ℝ}
    (unit_disk : ∀ x ∈ s, ‖x‖ ≤ 1) (diameter : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {u v : Space} (hu : u ∈ inverseStereographic '' s) (hv : v ∈ inverseStereographic '' s) :
    angle u v ≤ 2 * D := by
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  refine (angle_inverseStereographic_le (unit_disk x hx) (unit_disk y hy)).trans ?_
  rw [← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (diameter x hx y hy) (by norm_num)

/-- Convert the chord bound in planar units to the global spherical area bound. -/
theorem two_side_bound_of_planar_area {s : Set Plane} (compact : IsCompact s)
    (star : StarConvex ℝ (0 : Plane) s) (unit_disk : ∀ x ∈ s, ‖x‖ ≤ 1)
    {weightedLength : ℝ} (bound : weightedLength ≤ 16 * (volume : Measure Plane).real s) :
    weightedLength ≤ 8 * solidAngleMeasure.real (inverseStereographic '' s) := by
  have area := stereographic_area_lower compact star (R := 1) (by norm_num) unit_disk
  norm_num at area
  have real_area := ENNReal.toReal_mono (by finiteness) area
  rw [ENNReal.toReal_mul] at real_area
  norm_num at real_area
  change 2 * (volume : Measure Plane).real s ≤
    solidAngleMeasure.real (inverseStereographic '' s) at real_area
  linarith only [bound, real_area]

/-- Convert the chord bound to the sharper estimate using the angular radius. -/
theorem two_side_bound_of_angular_radius {s : Set Plane} (compact : IsCompact s)
    (star : StarConvex ℝ (0 : Plane) s) {d : ℝ} (small : d < Real.pi / 2)
    (radius : ∀ x ∈ s, angle (northLift 0) (inverseStereographic x) ≤ d)
    {weightedLength : ℝ} (bound : weightedLength ≤ 16 * (volume : Measure Plane).real s) :
    Real.cos (d / 2) ^ 2 * weightedLength ≤
      4 * solidAngleMeasure.real (inverseStereographic '' s) := by
  have area := stereographic_area_lower_of_angle compact star small radius
  have real_area := ENNReal.toReal_mono (by finiteness) area
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at real_area
  change (4 * Real.cos (d / 2) ^ 2) * (volume : Measure Plane).real s ≤
    solidAngleMeasure.real (inverseStereographic '' s) at real_area
  have mul := mul_le_mul_of_nonneg_left bound (sq_nonneg (Real.cos (d / 2)))
  linarith only [mul, real_area]

end Unfoldings.Cap
