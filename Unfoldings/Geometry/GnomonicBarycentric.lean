module

public import Unfoldings.Geometry.SphericalConvex
public import Mathlib.Analysis.Convex.Combination

/-! Normalized barycentric interpolation is projective reweighting in a gnomonic chart. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {I : Type*} [Fintype I]

/-- Rescale each barycentric coordinate by the corresponding positive height. -/
def projectiveWeight (height weight : I → ℝ) (i : I) : ℝ :=
  weight i * height i / ∑ j, weight j * height j

private theorem weighted_height_pos {height weight : I → ℝ}
    (positive : ∀ i, 0 < height i) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) : 0 < ∑ i, weight i * height i := by
  have exists_pos : ∃ i, 0 < weight i := by
    by_contra! none
    have zero : (∑ i, weight i) = 0 := Finset.sum_eq_zero
      (fun i _ => le_antisymm (none i) (nonneg i))
    exact one_ne_zero (sum.symm.trans zero)
  obtain ⟨i, hi⟩ := exists_pos
  exact Finset.sum_pos' (fun j _ => mul_nonneg (nonneg j) (positive j).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (positive i)⟩

theorem projectiveWeight_nonneg {height weight : I → ℝ}
    (positive : ∀ i, 0 < height i) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) (i : I) : 0 ≤ projectiveWeight height weight i :=
  div_nonneg (mul_nonneg (nonneg i) (positive i).le) (weighted_height_pos positive nonneg sum).le

theorem sum_projectiveWeight {height weight : I → ℝ}
    (positive : ∀ i, 0 < height i) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) : ∑ i, projectiveWeight height weight i = 1 := by
  simp only [projectiveWeight, ← Finset.sum_div,
    div_self (weighted_height_pos positive nonneg sum).ne']

/-- Reweighting keeps exactly the same nonzero vertices, so on an edge no
weight from a third vertex enters the spherical interpolation. -/
theorem projectiveWeight_eq_zero_iff {height weight : I → ℝ}
    (positive : ∀ i, 0 < height i) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) (i : I) : projectiveWeight height weight i = 0 ↔ weight i = 0 := by
  simp [projectiveWeight, (positive i).ne', (weighted_height_pos positive nonneg sum).ne']

/-- Inverting each height reverses the change of barycentric coordinates. -/
theorem projectiveWeight_inverse {height weight : I → ℝ}
    (positive : ∀ i, 0 < height i) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) :
    projectiveWeight (fun i => (height i)⁻¹) (projectiveWeight height weight) = weight := by
  let total := ∑ i, weight i * height i
  have total_pos : 0 < total := weighted_height_pos positive nonneg sum
  have term (i : I) : projectiveWeight height weight i * (height i)⁻¹ = weight i / total := by
    change weight i * height i / total * (height i)⁻¹ = weight i / total
    field_simp [(positive i).ne', total_pos.ne']
  funext i
  unfold projectiveWeight
  change (projectiveWeight height weight i * (height i)⁻¹) /
    (∑ j, projectiveWeight height weight j * (height j)⁻¹) = weight i
  simp only [term, ← Finset.sum_div, sum]
  rw [div_div_div_cancel_right₀ total_pos.ne', div_one]

namespace Cap

/-- After normalizing the interpolation, the gnomonic image is the convex
combination of the chart vertices with exactly these rescaled weights. -/
theorem normalize_barycentric_eq_gnomonic (vertex : I → Space) (weight : I → ℝ)
    (upward : ∀ i, 0 < vertex i 2) (nonneg : ∀ i, 0 ≤ weight i)
    (sum : ∑ i, weight i = 1) :
    NormedSpace.normalize (∑ i, weight i • vertex i) =
      gnomonicNormal (∑ i, projectiveWeight (fun j => vertex j 2) weight i •
        ((vertex i 2)⁻¹ • horizontal (vertex i))) := by
  let z := ∑ i, weight i • vertex i
  have height : z 2 = ∑ i, weight i * vertex i 2 := by
    change (EuclideanSpace.proj 2) (∑ i, weight i • vertex i) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  have positive : 0 < z 2 := height.symm ▸ weighted_height_pos upward nonneg sum
  have xy : (z 2)⁻¹ • horizontal z = ∑ i, projectiveWeight (fun j => vertex j 2) weight i •
      ((vertex i 2)⁻¹ • horizontal (vertex i)) := by
    rw [height]
    dsimp only [z]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    unfold projectiveWeight
    field_simp [(upward i).ne', (weighted_height_pos upward nonneg sum).ne']
  change NormedSpace.normalize z = _
  rw [← xy, gnomonicNormal, northLift_slope z positive,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr positive)]

end Cap
end Unfoldings
