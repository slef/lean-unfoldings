module

public import Unfoldings.Polyhedron.GaussianChart
public import Unfoldings.Convex.FiniteNormalFanInterior
public import Unfoldings.Geometry.StereographicSupportDisks

/-! Gaussian two-cells are exactly the full-dimensional normal cones at extreme sites. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open MeasureTheory Cap
open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem gaussianCone_interior_nonempty_iff_extreme (i : F.hullSites) :
    (interior (F.gaussianCone i)).Nonempty ↔ (i : Space) ∈ F.vertexHull.extremePoints ℝ := by
  rw [F.vertexHull_eq_convexHull_sites, gaussianCone]
  have range : Set.range (fun j : F.hullSites => (j : Space)) = (F.hullSites : Set Space) :=
    Subtype.range_coe_subtype
  simpa only [range] using
    (interior_finiteHullNormalCone_nonempty_iff
      (site := fun j : F.hullSites => (j : Space)) Subtype.val_injective i)

theorem solidAngle_gaussianCell_eq_zero_of_not_extreme (i : F.hullSites)
    (nonextreme : (i : Space) ∉ F.vertexHull.extremePoints ℝ) :
    solidAngleMeasure (F.gaussianCell i) = 0 := by
  rw [F.solidAngle_gaussianCell, gaussianCone]
  apply solidAngle_finiteHullNormalCone_eq_zero_of_not_extreme Subtype.val_injective
  have range : Set.range (fun j : F.hullSites => (j : Space)) = (F.hullSites : Set Space) :=
    Subtype.range_coe_subtype
  rwa [range, ← F.vertexHull_eq_convexHull_sites]

/-- At an extreme site, the hemisphere center can be chosen in the strict
interior of its normal cone, so all competing sites pair strictly below it. -/
theorem exists_strict_gaussianCell_center (P : F.ConvexBoundary) (i : F.hullSites)
    (extreme : (i : Space) ∈ F.vertexHull.extremePoints ℝ) :
    ∃ q ∈ F.gaussianCell i,
      q ∈ interior (F.gaussianCone i) ∧ ∀ z ∈ F.gaussianCell i, 0 < inner ℝ q z := by
  obtain ⟨q, hq, hemisphere⟩ := F.exists_gaussianCell_center P i (F.gaussianCell_nonempty P i)
  obtain ⟨b, hb⟩ := (F.gaussianCone_interior_nonempty_iff_extreme i).mpr extreme
  obtain ⟨w, hw, minimum⟩ := (F.isCompact_gaussianCell i).exists_isMinOn
    (F.gaussianCell_nonempty P i) ((innerSL ℝ q).continuous.continuousOn)
  let a := inner ℝ q w
  have a_pos : 0 < a := hemisphere w hw
  let t := a / (2 * (‖b‖ + 1))
  have t_pos : 0 < t := by dsimp [t]; positivity
  let x := q + t • b
  have loss : t * ‖b‖ ≤ a / 2 := by
    have h : ‖b‖ / (‖b‖ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ a / 2)
    have scale : t * ‖b‖ = a / 2 * (‖b‖ / (‖b‖ + 1)) := by
      dsimp [t]
      field_simp
    simpa only [scale, mul_one] using h'
  have x_positive (z : Space) (hz : z ∈ F.gaussianCell i) : 0 < inner ℝ x z := by
    have q_lower : a ≤ inner ℝ q z := isMinOn_iff.mp minimum z hz
    have unit : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
    have bound : -‖b‖ ≤ inner ℝ b z := by
      have h := abs_real_inner_le_norm b z
      rw [unit, mul_one] at h
      exact neg_le_of_abs_le h
    have lower := mul_le_mul_of_nonneg_left bound t_pos.le
    dsimp [x]
    rw [inner_add_left, real_inner_smul_left]
    linarith only [q_lower, lower, loss, a_pos]
  have x_ne : x ≠ 0 := by
    intro zero
    have h := x_positive w hw
    rw [zero, inner_zero_left] at h
    exact (lt_irrefl _) h
  have strict (j : F.hullSites) (ji : j ≠ i) :
      inner ℝ x (j : Space) < inner ℝ x (i : Space) := by
    have hb' := (mem_interior_finiteHullNormalCone_iff Subtype.val_injective i).mp hb j ji
    have hq' := hq.1 j
    dsimp [x]
    rw [inner_add_left, real_inner_smul_left, inner_add_left, real_inner_smul_left]
    exact add_lt_add_of_le_of_lt hq' (mul_lt_mul_of_pos_left hb' t_pos)
  have normalized : NormedSpace.normalize x ∈ interior (F.gaussianCone i) := by
    apply (mem_interior_finiteHullNormalCone_iff Subtype.val_injective i).mpr
    intro j ji
    simp only [NormedSpace.normalize, real_inner_smul_left]
    exact mul_lt_mul_of_pos_left (strict j ji) (inv_pos.mpr (norm_pos_iff.mpr x_ne))
  refine ⟨NormedSpace.normalize x, ⟨interior_subset normalized, ?_⟩, normalized, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize x_ne
  · intro z hz
    rw [NormedSpace.normalize, real_inner_smul_left]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr x_ne)) (x_positive z hz)

/-- Strictly centered extreme Gaussian cells have strictly convex charts.
The self-comparison is the single redundant zero support. -/
theorem strictConvex_gaussianChartRegion (i : F.hullSites) {q : Space}
    (hq : q ∈ F.gaussianCell i) (strict : q ∈ interior (F.gaussianCone i)) :
    StrictConvex ℝ (F.gaussianChartRegion i q) := by
  have unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq.2
  let normal (j : {j : F.hullSites // j ≠ i}) := northFrame q ((i : Space) - j.val)
  have up (j : {j : F.hullSites // j ≠ i}) : 0 < normal j 2 := by
    change 0 < northFrame q ((i : Space) - j.val) 2
    rw [northFrame_height q unit, inner_sub_right, sub_pos]
    exact (mem_interior_finiteHullNormalCone_iff Subtype.val_injective i).mp strict j j.property
  have region : F.gaussianChartRegion i q =
      {x | ∀ j, 0 ≤ inner ℝ (normal j) (inverseStereographic x)} := by
    ext x
    constructor
    · intro hx j
      exact hx j
    · intro hx j
      by_cases same : j = i
      · subst j
        simp
      · exact hx ⟨j, same⟩
  rw [region]
  exact strictConvex_inverseStereographic_region normal up

open Classical in
/-- Subdivision vertices contribute no area, so the genuine Gaussian cells
alone account for the full sphere. -/
theorem sum_extreme_gaussianCellArea (P : F.ConvexBoundary) :
    (∑ i ∈ (Finset.univ : Finset F.hullSites).filter
      (fun i : F.hullSites => (i : Space) ∈ F.vertexHull.extremePoints ℝ),
      solidAngleMeasure.real (F.gaussianCell i)) = 4 * Real.pi := by
  rw [Finset.sum_filter, ← F.sum_gaussianArea P]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with extreme
  · simp only [Measure.real, F.solidAngle_gaussianCell]
  · rw [← F.solidAngle_gaussianCell,
      F.solidAngle_gaussianCell_eq_zero_of_not_extreme i extreme, ENNReal.toReal_zero]

end Unfoldings.SpatialFolding
