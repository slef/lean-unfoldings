module

public import Unfoldings.Geometry.RadialSlice
public import Mathlib.Analysis.Convex.Combination

/-!
# The finite-hull description of a transverse vertex section

A positive level below all other generator heights cuts the body in exactly
the convex hull of their radial projections. The forward inclusion rescales
the barycentric weights by each generator's height, and discards zero-height
copies of the original vertex. No polygon or conic-hull representation is
assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

private theorem sum_filter_ne_eq_sum {ι A M : Type*} [Fintype ι] [DecidableEq A]
    [AddCommMonoid M] (points : ι → A) (x : A) (g : ι → M)
    (zero : ∀ i, points i = x → g i = 0) :
    (∑ i ∈ Finset.univ.filter (fun i => points i ≠ x), g i) = ∑ i, g i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ absent
  have equal : points i = x := by
    by_contra different
    exact absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _, different⟩)
  exact zero i equal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialSlice_convexHull_eq {s : Set E} (f : E →L[ℝ] ℝ) (x : E) (h : ℝ)
    (vertex : x ∈ convexHull ℝ s) (positive : 0 < h)
    (supported : ∀ y ∈ s, y ≠ x → h ≤ f (y - x)) :
    radialSlice (convexHull ℝ s) f x h =
      convexHull ℝ (radialSlicePoint f x h '' (s \ {x})) := by
  classical
  let Q := radialSlicePoint f x h '' (s \ {x})
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨body, level⟩ := hz
    obtain ⟨ι, _, w, points, nonnegative, sum_one, generators, combination⟩ :=
      mem_convexHull_iff_exists_fintype.mp body
    let J := Finset.univ.filter (fun i : ι => points i ≠ x)
    let weights (i : ι) := w i * f (points i - x) / h
    have displacements : (∑ i, w i • (points i - x)) = z - x := by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, sum_one, one_smul, combination]
    have weighted_height : (∑ i, w i * f (points i - x)) = h := by
      calc
        _ = f (∑ i, w i • (points i - x)) := by
          simp only [map_sum, map_smul, smul_eq_mul]
        _ = h := by rw [displacements]; exact level
    have filtered_weights : (∑ i ∈ J, weights i) = ∑ i, weights i :=
      sum_filter_ne_eq_sum points x weights (fun i equal => by
        simp only [weights, equal, sub_self, map_zero, mul_zero, zero_div])
    have weights_sum : (∑ i ∈ J, weights i) = 1 := by
      rw [filtered_weights]
      change (∑ i, w i * f (points i - x) / h) = 1
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, weighted_height, mul_inv_cancel₀ positive.ne']
    have weights_nonnegative (i : ι) (hi : i ∈ J) : 0 ≤ weights i := by
      have different := (Finset.mem_filter.mp hi).2
      have bound := supported (points i) (generators i) different
      exact div_nonneg (mul_nonneg (nonnegative i) (positive.le.trans bound)) positive.le
    have filtered_displacements : (∑ i ∈ J, w i • (points i - x)) = z - x :=
      (sum_filter_ne_eq_sum points x (fun i => w i • (points i - x))
        (fun i equal => by simp only [equal, sub_self, smul_zero])).trans displacements
    have projected_sum : (∑ i ∈ J, weights i • radialSlicePoint f x h (points i)) = z := by
      calc
        _ = ∑ i ∈ J, (w i • (points i - x) + weights i • x) := by
          apply Finset.sum_congr rfl
          intro i hi
          have different := (Finset.mem_filter.mp hi).2
          have height : 0 < f (points i - x) :=
            positive.trans_le (supported (points i) (generators i) different)
          have cancel : weights i * (h / f (points i - x)) = w i := by
            dsimp only [weights]
            field_simp [positive.ne', height.ne']
          rw [radialSlicePoint, AffineMap.lineMap_apply_module', smul_add, smul_smul, cancel]
        _ = (z - x) + x := by
          rw [Finset.sum_add_distrib, filtered_displacements, ← Finset.sum_smul,
            weights_sum, one_smul]
        _ = z := sub_add_cancel _ _
    have inside (i : ι) (hi : i ∈ J) : radialSlicePoint f x h (points i) ∈ convexHull ℝ Q := by
      apply subset_convexHull ℝ Q
      refine ⟨points i, ⟨generators i, ?_⟩, rfl⟩
      simpa only [Set.mem_singleton_iff] using (Finset.mem_filter.mp hi).2
    have member := (convex_convexHull ℝ Q).sum_mem weights_nonnegative weights_sum inside
    rwa [projected_sum] at member
  · apply convexHull_min _ (convex_radialSlice (convex_convexHull ℝ s) f x h)
    rintro _ ⟨y, hy, rfl⟩
    have different : y ≠ x := by simpa only [Set.mem_singleton_iff] using hy.2
    have bound := supported y hy.1 different
    exact radialSlicePoint_mem (convex_convexHull ℝ s) f x h y vertex
      (subset_convexHull ℝ s hy.1) (positive.trans_le bound) positive.le bound

end Unfoldings
