module

public import Unfoldings.Geometry.SphericalConvex
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Convex.Topology

/-! A finite spherical hull in an open hemisphere has an internal hemisphere center. -/

@[expose] public section

noncomputable section

namespace Unfoldings

private theorem convex_positive_normalized_preimage {N : Set Space} (convex : SphericalConvex N)
    (axis : Space) :
    Convex ℝ {x | 0 < inner ℝ axis x ∧ NormedSpace.normalize x ∈ N} := by
  intro x hx y hy a b ha hb total
  have hx' : 0 < inner ℝ axis x ∧ NormedSpace.normalize x ∈ N := hx
  have hy' : 0 < inner ℝ axis y ∧ NormedSpace.normalize y ∈ N := hy
  have positive : 0 < inner ℝ axis (a • x + b • y) := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rcases eq_or_lt_of_le ha with zero | pos
    · have hb' : 0 < b := by linarith
      simp only [← zero, zero_mul, zero_add]
      exact mul_pos hb' hy'.1
    · exact add_pos_of_pos_of_nonneg (mul_pos pos hx'.1) (mul_nonneg hb hy'.1.le)
  have ne : a • x + b • y ≠ 0 := by
    intro zero
    rw [zero, inner_zero_right] at positive
    exact (lt_irrefl _) positive
  have equal :
      (a * ‖x‖) • NormedSpace.normalize x + (b * ‖y‖) • NormedSpace.normalize y =
        a • x + b • y := by
    rw [mul_smul, mul_smul, NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]
  refine ⟨positive, ?_⟩
  have inside := convex.2 _ hx'.2 _ hy'.2 (a * ‖x‖) (b * ‖y‖)
    (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hb (norm_nonneg _)) (equal ▸ ne)
  rwa [equal] at inside

/-- The normalized closest point in the Euclidean hull belongs to the
spherical region. Its open hemisphere contains the entire normalized hull,
even when the closest point is on the region boundary. -/
theorem exists_sphericalHull_center {sites N : Set Space} (finite : sites.Finite)
    (nonempty : sites.Nonempty) (convex : SphericalConvex N) (subset : sites ⊆ N)
    (axis : Space) (up : ∀ x ∈ sites, 0 < inner ℝ axis x) :
    ∃ q ∈ N, ‖q‖ = 1 ∧ ∀ z ∈ convexHull ℝ sites, 0 < inner ℝ q (NormedSpace.normalize z) := by
  let H := convexHull ℝ sites
  have members : H ⊆ {x | 0 < inner ℝ axis x ∧ NormedSpace.normalize x ∈ N} := by
    apply convexHull_min ?_ (convex_positive_normalized_preimage convex axis)
    intro x hx
    exact ⟨up x hx, by simpa [NormedSpace.normalize, convex.1 _ (subset hx)] using subset hx⟩
  obtain ⟨x, hx, minNorm⟩ := exists_norm_eq_iInf_of_complete_convex
    nonempty.convexHull (finite.isCompact_convexHull ℝ).isComplete (convex_convexHull ℝ sites) 0
  have ne (z : Space) (hz : z ∈ H) : z ≠ 0 := by
    intro zero
    have hz' : 0 < inner ℝ axis z := (members hz).1
    rw [zero, inner_zero_right] at hz'
    exact (lt_irrefl _) hz'
  refine ⟨NormedSpace.normalize x, (members hx).2, NormedSpace.norm_normalize (ne x hx), ?_⟩
  intro z hz
  have bound := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ sites) hx).1 minNorm z hz
  rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at bound
  have pos : 0 < inner ℝ x z := (sq_pos_of_pos (norm_pos_iff.mpr (ne x hx))).trans_le (by linarith)
  simp only [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (ne z hz)))
    (mul_pos (inv_pos.mpr (norm_pos_iff.mpr (ne x hx))) pos)

end Unfoldings
