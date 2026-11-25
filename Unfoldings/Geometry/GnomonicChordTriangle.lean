module

public import Unfoldings.Geometry.RadialTrianglePartition
public import Unfoldings.Geometry.GnomonicMinorArc
public import Mathlib.Analysis.Convex.Combination

/-! A spherical chord triangle is exactly the gnomonic image of its planar selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Module

/-- The planar selector uses the gnomonic coordinates of the three actual sites. -/
def chordChartVertex (b : Basis (Fin 3) ℝ Space) (i : Fin 3) : Plane :=
  (b i 2)⁻¹ • horizontal (b i)

private theorem northLift_chordChartVertex (b : Basis (Fin 3) ℝ Space)
    (upward : ∀ i, 0 < b i 2) (i : Fin 3) :
    northLift (chordChartVertex b i) = (b i 2)⁻¹ • b i :=
  northLift_slope (b i) (upward i)

/-- Gnomonic projection carries a planar triangle to the corresponding spherical cone section. -/
theorem mem_convexHull_chordChartVertex_iff (b : Basis (Fin 3) ℝ Space)
    (upward : ∀ i, 0 < b i 2) (p : Plane) :
    p ∈ convexHull ℝ (Set.range (chordChartVertex b)) ↔
      ∀ i, 0 ≤ b.coord i (gnomonicNormal p) := by
  let S : Set Plane := {x | ∀ i, 0 ≤ b.coord i (northLift x)}
  have convex : Convex ℝ S := by
    intro x hx y hy a d ha hd total
    intro i
    rw [northLift_combo x y a d total, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hd (hy i))
  have included : Set.range (chordChartVertex b) ⊆ S := by
    rintro _ ⟨i, rfl⟩ j
    rw [northLift_chordChartVertex b upward, map_smul, smul_eq_mul, Basis.coord_apply, b.repr_self,
      Finsupp.single_apply]
    exact mul_nonneg (inv_nonneg.mpr (upward i).le) (by split <;> norm_num)
  have scaled : ∀ i, b.coord i (gnomonicNormal p) = ‖northLift p‖⁻¹ * b.coord i (northLift p) := by
    intro i
    unfold gnomonicNormal NormedSpace.normalize
    rw [map_smul, smul_eq_mul]
  have factor_pos : 0 < ‖northLift p‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero p))
  simp only [scaled, mul_nonneg_iff_of_pos_left factor_pos]
  constructor
  · exact fun h => convexHull_min included convex h
  · intro h
    let w (i : Fin 3) := b.coord i (northLift p) * b i 2
    have expand := b.sum_repr (northLift p)
    change (∑ i, b.coord i (northLift p) • b i) = northLift p at expand
    have total : ∑ i, w i = 1 := by
      have height := congrArg (EuclideanSpace.proj 2) expand
      simp only [map_sum, map_smul, smul_eq_mul] at height
      change (∑ i, w i) = northLift p 2 at height
      rwa [northLift_height] at height
    have slope : (∑ i, w i • chordChartVertex b i) = p := by
      have xy := congrArg horizontal expand
      rw [map_sum, northLift_horizontal] at xy
      rw [← xy]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, chordChartVertex, smul_smul]
      have identity : w i * (b i 2)⁻¹ = b.coord i (northLift p) := by
        dsimp only [w]
        rw [mul_assoc, mul_inv_cancel₀ (upward i).ne', mul_one]
      rw [identity]
    exact mem_convexHull_of_exists_fintype w (chordChartVertex b)
      (fun i => mul_nonneg (h i) (upward i).le) total (fun i => Set.mem_range_self i) slope

/-- The complete closed spherical section is the image of its planar chart triangle. -/
theorem gnomonicNormal_image_chordChart (b : Basis (Fin 3) ℝ Space)
    (upward : ∀ i, 0 < b i 2) :
    gnomonicNormal '' convexHull ℝ (Set.range (chordChartVertex b)) =
      {p | ‖p‖ = 1 ∧ ∀ i, 0 ≤ b.coord i p} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨gnomonicNormal_unit x, (mem_convexHull_chordChartVertex_iff b upward x).mp hx⟩
  · rintro ⟨unit, nonneg⟩
    have expand := b.sum_repr p
    change (∑ i, b.coord i p • b i) = p at expand
    have exists_pos : ∃ i, 0 < b.coord i p := by
      by_contra! all
      have zero (i : Fin 3) : b.coord i p = 0 := le_antisymm (all i) (nonneg i)
      simp only [zero, zero_smul, Finset.sum_const_zero] at expand
      rw [← expand, norm_zero] at unit
      exact zero_ne_one unit
    have height := congrArg (EuclideanSpace.proj 2) expand
    simp only [map_sum, map_smul, smul_eq_mul] at height
    change (∑ i, b.coord i p * b i 2) = p 2 at height
    have positive : 0 < p 2 := by
      rw [← height]
      obtain ⟨i, hi⟩ := exists_pos
      exact Finset.sum_pos' (fun j _ => mul_nonneg (nonneg j) (upward j).le)
        ⟨i, Finset.mem_univ _, mul_pos hi (upward i)⟩
    let x := (p 2)⁻¹ • horizontal p
    have at_x : gnomonicNormal x = p := gnomonicNormal_slope p unit positive
    refine ⟨x, (mem_convexHull_chordChartVertex_iff b upward x).mpr ?_, at_x⟩
    rwa [at_x]

end Unfoldings.Cap
