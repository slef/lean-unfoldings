module

public import Unfoldings.Geometry.NorthFrame
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! A horizontal chord and the vertical extent of a convex region bound its area. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped Affine ENNReal

private theorem height_eq_of_mem_horizontalLine {a b p : Plane} (height : a 1 = b 1)
    (p_mem : p ∈ line[ℝ, a, b]) : p 1 = a 1 := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp p_mem
  simp [AffineMap.lineMap_apply, height]

private theorem mem_horizontalLine_of_height_eq {a b p : Plane} (hne : a ≠ b)
    (height : a 1 = b 1) (p_height : p 1 = a 1) : p ∈ line[ℝ, a, b] := by
  have x_ne : b 0 - a 0 ≠ 0 := by
    intro h
    apply hne
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp h).symm
    · exact height
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
  ext i
  fin_cases i
  · rw [AffineMap.lineMap_apply]
    change (p 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) + a 0 = p 0
    rw [div_mul_cancel₀ _ x_ne, sub_add_cancel]
  · simp [AffineMap.lineMap_apply, ← height, p_height]

private theorem triangle_of_height_ne {a b c : Plane} (hne : a ≠ b)
    (height : a 1 = b 1) (c_height : c 1 ≠ a 1) :
    AffineIndependent ℝ ![c, a, b] := by
  apply affineIndependent_iff_not_collinear_set.mpr
  intro collinear
  exact c_height (height_eq_of_mem_horizontalLine height
    (collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne))

private theorem triangle_range (s : Affine.Simplex ℝ Plane 2) {a b c : Plane}
    (points : s.points = ![c, a, b]) : Set.range s.points = {c, a, b} := by
  rw [points]
  ext p
  simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem chord_triangle_area {a b c : Plane} (hne : a ≠ b) (height : a 1 = b 1)
    (c_height : c 1 ≠ a 1) :
    dist a b * |c 1 - a 1| / 2 ≤ (volume : Measure Plane).real (convexHull ℝ {c, a, b}) := by
  let s : Affine.Simplex ℝ Plane 2 := ⟨![c, a, b], triangle_of_height_ne hne height c_height⟩
  have points : s.points = ![c, a, b] := rfl
  have base : Set.range (s.faceOpposite 0).points = {a, b} := by
    ext p
    simp [Affine.Simplex.faceOpposite, Affine.Simplex.face, points, Fin.exists_fin_two, eq_comm]
  have foot : s.altitudeFoot 0 ∈ line[ℝ, a, b] := by
    rw [← base]
    exact s.altitudeFoot_mem_affineSpan_faceOpposite 0
  have lower : |c 1 - a 1| ≤ s.height 0 := by
    rw [Affine.Simplex.height]
    have h := PiLp.dist_apply_le c (s.altitudeFoot 0) (1 : Fin 2)
    simpa [points, Real.dist_eq, height_eq_of_mem_horizontalLine height foot] using h
  have base_length : (s.faceOpposite 0).volume = dist a b := by
    rw [Affine.Simplex.volume_eq_dist]
    simp [Affine.Simplex.faceOpposite, Affine.Simplex.face, points]
  have interior_eq : s.closedInterior = convexHull ℝ {c, a, b} := by
    rw [← s.convexHull_eq_closedInterior, triangle_range s points]
  rw [← interior_eq, ← s.volume_eq_volume_real_closedInterior (by simp [Plane]),
    Affine.Simplex.volume_eq s 0, base_length]
  norm_num
  nlinarith only [mul_le_mul_of_nonneg_right lower (dist_nonneg (x := a) (y := b))]

/-- The convex hull of a horizontal chord and points above and below it has
area at least half the chord length times the difference in heights. -/
theorem chord_mul_height_span_le_twice_area {s : Set Plane} (compact : IsCompact s)
    (convex : Convex ℝ s) {a b low high : Plane} (ha : a ∈ s) (hb : b ∈ s)
    (hl : low ∈ s) (hh : high ∈ s) (height : a 1 = b 1)
    (low_le : low 1 ≤ a 1) (high_ge : a 1 ≤ high 1) :
    dist a b * (high 1 - low 1) ≤ 2 * (volume : Measure Plane).real s := by
  by_cases same : a = b
  · subst b
    simp [measureReal_nonneg]
  let lowTriangle : Set Plane := convexHull ℝ {low, a, b}
  let highTriangle : Set Plane := convexHull ℝ {high, a, b}
  have low_in : lowTriangle ⊆ s :=
    convexHull_min (by simp [Set.insert_subset_iff, hl, ha, hb]) convex
  have high_in : highTriangle ⊆ s :=
    convexHull_min (by simp [Set.insert_subset_iff, hh, ha, hb]) convex
  have finite : (volume : Measure Plane) s ≠ ∞ := compact.measure_lt_top.ne
  have coord (i : Fin 2) : IsLinearMap ℝ (fun p : Plane => p i) :=
    (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) i : Plane →ₗ[ℝ] ℝ).isLinear
  have low_half : lowTriangle ⊆ {p | p 1 ≤ a 1} :=
    convexHull_min (by simp [Set.insert_subset_iff, ← height, low_le])
      (convex_halfSpace_le (coord 1) (a 1))
  have high_half : highTriangle ⊆ {p | a 1 ≤ p 1} :=
    convexHull_min (by simp [Set.insert_subset_iff, ← height, high_ge])
      (convex_halfSpace_ge (coord 1) (a 1))
  rcases eq_or_lt_of_le low_le with low_eq | low_lt
  · rcases eq_or_lt_of_le high_ge with high_eq | high_lt
    · simp [low_eq, ← high_eq, measureReal_nonneg]
    · have h := (chord_triangle_area same height high_lt.ne').trans
        (measureReal_mono high_in finite)
      rw [abs_of_nonneg (sub_nonneg.mpr high_ge)] at h
      rw [low_eq]
      linarith only [h]
  · rcases eq_or_lt_of_le high_ge with high_eq | high_lt
    · have h := (chord_triangle_area same height low_lt.ne).trans
        (measureReal_mono low_in finite)
      rw [abs_of_nonpos (sub_nonpos.mpr low_le)] at h
      rw [← high_eq]
      nlinarith only [h]
    · have line_null : (volume : Measure Plane) (line[ℝ, a, b] : Set Plane) = 0 := by
        apply Measure.addHaar_affineSubspace
        intro top
        have mem : high ∈ line[ℝ, a, b] := by rw [top]; trivial
        exact high_lt.ne' (height_eq_of_mem_horizontalLine height mem)
      have disjoint : AEDisjoint (volume : Measure Plane) lowTriangle highTriangle := by
        apply measure_mono_null _ line_null
        exact fun p hp => mem_horizontalLine_of_height_eq same height
          (le_antisymm (low_half hp.1) (high_half hp.2))
      have hlow := chord_triangle_area same height low_lt.ne
      have hhigh := chord_triangle_area same height high_lt.ne'
      rw [abs_of_nonpos (sub_nonpos.mpr low_le)] at hlow
      rw [abs_of_nonneg (sub_nonneg.mpr high_ge)] at hhigh
      have measurable : MeasurableSet highTriangle := by
        apply IsCompact.measurableSet
        exact (show ({high, a, b} : Set Plane).Finite by simp).isCompact_convexHull ℝ
      have monotone := measureReal_mono (Set.union_subset low_in high_in) finite
      rw [measureReal_union₀ measurable.nullMeasurableSet disjoint
        (ne_top_of_le_ne_top finite (measure_mono low_in))
        (ne_top_of_le_ne_top finite (measure_mono high_in))] at monotone
      nlinarith only [hlow, hhigh, monotone]

end Unfoldings.Cap
