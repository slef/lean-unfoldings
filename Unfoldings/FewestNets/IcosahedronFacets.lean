module

public import Unfoldings.FewestNets.IcosahedronHull

/-! Strict supporting planes, exact intersections, and frontier coverage for the macrofaces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Real InnerProductSpace
open scoped BigOperators

def faceNormal (f : Fin 20) : Space := ∑ k, faceCorners f k

theorem inner_rawVertex_self (i : Fin 12) :
    inner ℝ (rawVertex i) (rawVertex i) = 2 + goldenRatio := by
  rw [inner_rawVertex, dotData_classify, ite_eq_left rfl]
  norm_num [goldenValue]

theorem inner_rawVertex_of_adjacent {i j : Fin 12} (h : Adjacent i j) :
    inner ℝ (rawVertex i) (rawVertex j) = goldenRatio := by
  rw [inner_rawVertex, h]
  norm_num [goldenValue]

theorem inner_rawVertex_le_of_ne {i j : Fin 12} (h : i ≠ j) :
    inner ℝ (rawVertex i) (rawVertex j) ≤ goldenRatio := by
  by_cases adj : Adjacent i j
  · exact (inner_rawVertex_of_adjacent adj).le
  rw [inner_rawVertex, dotData_classify, ite_eq_right h, ite_eq_right adj]
  split <;>
    dsimp only [goldenValue] <;> push_cast <;>
    linarith only [goldenRatio_pos]

theorem inner_faceNormal_corner (f : Fin 20) (i : Fin 3) :
    inner ℝ (faceNormal f) (faceCorners f i) = 2 + 3 * goldenRatio := by
  have item (j : Fin 3) : inner ℝ (faceCorners f j) (faceCorners f i) =
      goldenRatio + if j = i then (2 : ℝ) else 0 := by
    by_cases equal : j = i
    · subst j
      rw [ite_eq_left rfl, faceCorners, inner_rawVertex_self]
      ring
    · rw [ite_eq_right equal, add_zero]
      exact inner_rawVertex_of_adjacent (adjacent_faceVertex f equal)
  rw [faceNormal, sum_inner]
  simp_rw [item, Finset.sum_add_distrib]
  simp
  ring

theorem inner_faceNormal_lt_of_outside (f : Fin 20) {i : Fin 12}
    (hi : i ∉ Set.range (faceVertex f)) :
    inner ℝ (faceNormal f) (rawVertex i) < 2 + 3 * goldenRatio := by
  rw [faceNormal, sum_inner]
  have le : (∑ k : Fin 3, inner ℝ (faceCorners f k) (rawVertex i)) ≤ ∑ _ : Fin 3, goldenRatio :=
    Finset.sum_le_sum (fun k _ =>
      inner_rawVertex_le_of_ne (fun eq => hi ⟨k, eq⟩))
  simp at le
  linarith only [le]

theorem inner_faceNormal_rawVertex_le (f : Fin 20) (i : Fin 12) :
    inner ℝ (faceNormal f) (rawVertex i) ≤ 2 + 3 * goldenRatio := by
  by_cases hi : i ∈ Set.range (faceVertex f)
  · obtain ⟨k, rfl⟩ := hi
    exact (inner_faceNormal_corner f k).le
  · exact (inner_faceNormal_lt_of_outside f hi).le

theorem inner_faceNormal_le_on_hull (f : Fin 20) {x : Space} (hx : x ∈ hull) :
    inner ℝ (faceNormal f) x ≤ 2 + 3 * goldenRatio :=
  convexHull_min (by
      rintro _ ⟨i, rfl⟩
      exact inner_faceNormal_rawVertex_le f i)
    (convex_halfSpace_le (innerSL ℝ (faceNormal f)).toLinearMap.isLinear (2 + 3 * goldenRatio)) hx

/-- Each coordinate triangle is the entire slice of the hull by its supporting plane. -/
theorem faceTriangle_eq_support (f : Fin 20) :
    faceTriangle f = hull ∩ {x | inner ℝ (faceNormal f) x = 2 + 3 * goldenRatio} := by
  let n := faceNormal f
  let m := 2 + 3 * goldenRatio
  have inHull : faceTriangle f ⊆ hull :=
    convexHull_mono (by rintro _ ⟨i, rfl⟩; exact Set.mem_range_self _)
  have onPlane : faceTriangle f ⊆ {x | inner ℝ n x = m} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact inner_faceNormal_corner f i)
      (convex_hyperplane (innerSL ℝ n).toLinearMap.isLinear m)
  refine Set.Subset.antisymm (fun x hx => ⟨inHull hx, onPlane hx⟩) ?_
  rintro x ⟨hx, eq⟩
  have sub : rawVertex '' {i | inner ℝ n (rawVertex i) = m} ⊆ Set.range (faceCorners f) := by
    rintro _ ⟨i, hi, rfl⟩
    by_contra blocked
    have outside : i ∉ Set.range (faceVertex f) := by
      rintro ⟨k, rfl⟩
      exact blocked ⟨k, rfl⟩
    exact (inner_faceNormal_lt_of_outside f outside).ne hi
  exact convexHull_mono sub
    (mem_convexHull_maximizingCorners (inner_faceNormal_rawVertex_le f) hx eq)

theorem faceTriangle_subset_frontier (f : Fin 20) : faceTriangle f ⊆ frontier hull := by
  intro x hx
  rw [faceTriangle_eq_support f] at hx
  obtain ⟨hx, eq⟩ := hx
  rw [frontier, isClosed_hull.closure_eq, Set.mem_sdiff]
  refine ⟨hx, fun interior => ?_⟩
  let n := faceNormal f
  let m := 2 + 3 * goldenRatio
  change inner ℝ n x = m at eq
  have positive : 0 < m := by dsimp [m]; linarith only [goldenRatio_pos]
  have nonzero : n ≠ 0 := by
    intro zero
    rw [zero, inner_zero_left] at eq
    exact positive.ne' eq.symm
  obtain ⟨ε, hε, ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp interior)
  let t := ε / (2 * ‖n‖)
  have ht : 0 < t := div_pos hε (by positivity)
  have inBall : x + t • n ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * ‖n‖)]
    nlinarith only [mul_pos hε (norm_pos_iff.mpr nonzero)]
  have le := inner_faceNormal_le_on_hull f (ball inBall)
  change inner ℝ n (x + t • n) ≤ m at le
  rw [inner_add_right, real_inner_smul_right, eq, real_inner_self_eq_norm_sq] at le
  have gain : 0 < t * ‖n‖ ^ 2 := mul_pos ht (pow_pos (norm_pos_iff.mpr nonzero) _)
  linarith only [le, gain]

/-- The twenty triangles cover exactly the boundary of the regular icosahedron. -/
theorem frontier_hull_eq_faces : frontier hull = ⋃ f : Fin 20, faceTriangle f :=
  frontier_hull_subset_faces.antisymm (Set.iUnion_subset faceTriangle_subset_frontier)

end Unfoldings.FewestNets.Icosahedron
