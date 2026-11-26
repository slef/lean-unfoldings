module

public import Unfoldings.Roof.OriginalFaceHeight
public import Unfoldings.Roof.ProjectedGermSegments
public import Unfoldings.Geometry.AffineOrientation

/-! The closing ray selects one supporting slope at a regular trimmed endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem inner_sub_slope_eq_zero_of_shared_direction (f g : Face) {p v : Plane}
    (p_f : p ∈ (K.projectedTriangle f).carrier) (p_g : p ∈ (K.projectedTriangle g).carrier)
    {s t : ℝ} (sp : 0 < s) (tp : 0 < t)
    (ray_f : p + s • v ∈ (K.projectedTriangle f).carrier)
    (ray_g : p + t • v ∈ (K.projectedTriangle g).carrier) :
    inner ℝ (K.normalSlope f - K.normalSlope g) v = 0 := by
  let r := min s t
  let q := p + r • v
  have rp : 0 < r := lt_min sp tp
  have shared (i : Face) (p_i : p ∈ (K.projectedTriangle i).carrier)
      {u : ℝ} (up : 0 < u) (ru : r ≤ u) (q_i : p + u • v ∈ (K.projectedTriangle i).carrier) :
      q ∈ (K.projectedTriangle i).carrier := by
    apply (K.projectedTriangle i).convex_carrier.segment_subset p_i q_i
    have eq : AffineMap.lineMap p (p + u • v) (r / u) = q := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ up.ne', add_comm]
    rw [← eq]
    exact lineMap_mem_segment ℝ _ _ ⟨div_nonneg rp.le up.le, (div_le_one up).mpr ru⟩
  have f_p := K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f p_f
  have g_p := K.roofHeight_eq_supportHeight_of_mem_projectedTriangle g p_g
  have f_q := K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f (shared f p_f sp (min_le_left _ _) ray_f)
  have g_q := K.roofHeight_eq_supportHeight_of_mem_projectedTriangle g (shared g p_g tp (min_le_right _ _) ray_g)
  rw [K.supportHeight_difference f p q] at f_q
  rw [K.supportHeight_difference g p q] at g_q
  have eq : q - p = r • v := add_sub_cancel_left _ _
  rw [eq, real_inner_smul_right] at f_q g_q
  rw [inner_sub_left]
  have equality : r * inner ℝ (K.normalSlope f) v = r * inner ℝ (K.normalSlope g) v := by
    linarith only [f_p, g_p, f_q, g_q]
  exact sub_eq_zero.mpr (mul_left_cancel₀ rp.ne' equality)

private theorem eq_of_inner_zero_of_orient_ne {p q u v : Plane} (no : orient 0 u v ≠ 0)
    (hu : inner ℝ (p - q) u = 0) (hv : inner ℝ (p - q) v = 0) : p = q := by
  have d₀ : (p - q) 0 * orient 0 u v = 0 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply] at hu hv
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination v 1 * hu - u 1 * hv
  have d₁ : (p - q) 1 * orient 0 u v = 0 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply] at hu hv
    simp only [orient, PiLp.zero_apply, sub_zero]
    linear_combination u 0 * hv - v 0 * hu
  apply sub_eq_zero.mp
  ext i
  fin_cases i
  · exact (mul_eq_zero.mp d₀).resolve_right no
  · exact (mul_eq_zero.mp d₁).resolve_right no

/-- At a regular trim the closure ray has a unique slope, shared by the
lens face and the corresponding endpoint of the closing trace. -/
theorem normalSlope_eq_of_shared_endpoint_ray (f g : Face) {p u v a b : Plane}
    (noncollinear : orient 0 u v ≠ 0) (tangent : inner ℝ (a - b) u = 0)
    (slope_f : K.normalSlope f = a ∨ K.normalSlope f = b)
    (slope_g : K.normalSlope g = a ∨ K.normalSlope g = b)
    (p_f : p ∈ (K.projectedTriangle f).carrier) (p_g : p ∈ (K.projectedTriangle g).carrier)
    {s t : ℝ} (sp : 0 < s) (tp : 0 < t)
    (ray_f : p + s • v ∈ (K.projectedTriangle f).carrier)
    (ray_g : p + t • v ∈ (K.projectedTriangle g).carrier) :
    K.normalSlope f = K.normalSlope g := by
  have both := K.inner_sub_slope_eq_zero_of_shared_direction f g p_f p_g sp tp ray_f ray_g
  have along : inner ℝ (K.normalSlope f - K.normalSlope g) u = 0 := by
    rcases slope_f with hf | hf <;> rcases slope_g with hg | hg
    · simp [hf, hg]
    · rwa [hf, hg]
    · rw [hf, hg, ← neg_sub, inner_neg_left, tangent, neg_zero]
    · simp [hf, hg]
  exact eq_of_inner_zero_of_orient_ne noncollinear along both

end Unfoldings.ConvexRoof
