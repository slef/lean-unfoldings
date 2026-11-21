module

public import Unfoldings.Geometry.TriangleGridCover
public import Unfoldings.Geometry.RadialTriangleReindex
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Every point of an equilateral triangle is within the circumradius of a corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem exists_corner_within_radius {v : Fin 3 → E} {o x : E} {r : ℝ}
    (hr : 0 ≤ r) (sphere : ∀ i, ‖v i - o‖ = r) (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ i, ‖v i - x‖ ≤ r := by
  obtain ⟨w, nonnegative, total, eq⟩ :=
    TriangleGrid.exists_weights_of_mem_convexHull_range v hx
  by_contra! farther
  have weighted : (∑ i, w i • (v i - o)) = x - o := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, total, one_smul, eq]
  have average : ∑ i, w i * inner ℝ (x - o) (v i - o) = ‖x - o‖ ^ 2 := by
    have h := congrArg (inner ℝ (x - o)) weighted
    simpa only [inner_sum, real_inner_smul_right, real_inner_self_eq_norm_sq] using h
  have each (i : Fin 3) : inner ℝ (x - o) (v i - o) < ‖x - o‖ ^ 2 / 2 := by
    have squared := (sq_lt_sq₀ hr (norm_nonneg _)).mpr (farther i)
    rw [norm_sub_rev, show x - v i = (x - o) - (v i - o) by abel,
      norm_sub_sq_real, sphere] at squared
    linarith only [squared]
  have some : ∃ i, 0 < w i := by
    by_contra! none
    have zero (i : Fin 3) : w i = 0 := le_antisymm (none i) (nonnegative i)
    simp [zero] at total
  obtain ⟨i, hi⟩ := some
  have upper : (∑ i, w i * inner ℝ (x - o) (v i - o)) < ∑ i, w i * (‖x - o‖ ^ 2 / 2) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (each i).le (nonnegative i))
      ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (each i) hi⟩
  rw [average, ← Finset.sum_mul, total, one_mul] at upper
  linarith only [upper, sq_nonneg ‖x - o‖]

private theorem norm_sub_centroid_eq {v : Fin 3 → E} {L : ℝ} (hL : 0 ≤ L)
    (edge : ∀ i j, i ≠ j → ‖v i - v j‖ = L) (i : Fin 3) :
    ‖v i - (1 / 3 : ℝ) • ∑ j, v j‖ = L / Real.sqrt 3 := by
  have table : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide +kernel
  obtain ⟨j, k, ij, ik, jk⟩ := table i
  let perm := Equiv.ofBijective ![i, j, k] (vector_three_bijective ij ik jk)
  have sum : ∑ l, v l = v i + v j + v k := by
    have h := Equiv.sum_comp perm v
    rw [Fin.sum_univ_three] at h
    exact h.symm
  let u := v j - v i
  let w := v k - v i
  have un : ‖u‖ = L := edge j i ij.symm
  have wn : ‖w‖ = L := edge k i ik.symm
  have diff : ‖u - w‖ = L := by
    rw [show u - w = v j - v k by dsimp [u, w]; abel]
    exact edge j k jk
  have inner : 2 * inner ℝ u w = L ^ 2 := by
    have h := norm_sub_sq_real u w
    rw [un, wn, diff] at h
    linarith only [h]
  rw [sum, norm_sub_rev, show (1 / 3 : ℝ) • (v i + v j + v k) - v i =
      (1 / 3 : ℝ) • (u + w) by dsimp [u, w]; module,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  apply (sq_eq_sq₀ (by positivity) (div_nonneg hL (Real.sqrt_nonneg _))).mp
  rw [mul_pow, norm_add_sq_real, un, wn]
  simp only [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  linarith only [inner]

/-- The three closed disks of the equilateral covering radius cover the triangle. -/
theorem exists_corner_norm_le_of_equilateral {v : Fin 3 → E} {L : ℝ} (hL : 0 ≤ L)
    (edge : ∀ i j, i ≠ j → ‖v i - v j‖ = L) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ i, ‖v i - x‖ ≤ L / Real.sqrt 3 :=
  exists_corner_within_radius (div_nonneg hL (Real.sqrt_nonneg _))
    (norm_sub_centroid_eq hL edge) hx

end Unfoldings
