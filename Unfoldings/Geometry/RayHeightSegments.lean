module

public import Unfoldings.Geometry.RayStrip
public import Unfoldings.Geometry.HeightSegmentNetwork

/-! Exact ray height graphs cover every intermediate point of a genuine radial network edge. -/

@[expose] public section

namespace Unfoldings.MonotoneHeightGraph

theorem ray_point_eq_smul (p : ℂ) (px : 0 < p.re) (py : 0 < p.im) (h : ℝ) :
    (ray p px py).point h = h • ((p.re + p.im)⁻¹ • p) := by
  apply Complex.ext
  · simp only [point, ray_coordinate, Complex.smul_re, smul_eq_mul]
    ring
  · simp only [point, ray_coordinate, Complex.smul_im, smul_eq_mul]
    field_simp [(add_pos px py).ne']
    ring

theorem ray_point_tip (p : ℂ) (px : 0 < p.re) (py : 0 < p.im) :
    (ray p px py).point (p.re + p.im) = p := by
  rw [ray_point_eq_smul, smul_smul, mul_inv_cancel₀ (add_pos px py).ne', one_smul]

theorem ray_point_smul_tip (p : ℂ) (px : 0 < p.re) (py : 0 < p.im) (r : ℝ) :
    (ray p px py).point ((r • p).re + (r • p).im) = r • p := by
  rw [ray_point_eq_smul]
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_smul]
  have coefficient : (r * p.re + r * p.im) * (p.re + p.im)⁻¹ = r := by
    rw [← mul_add, mul_assoc, mul_inv_cancel₀ (add_pos px py).ne', mul_one]
  rw [coefficient]

theorem ray_point_mem_segment (p : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    {a h b : ℝ} (member : h ∈ Set.Icc a b) :
    (ray p px py).point h ∈
      segment ℝ ((ray p px py).point a) ((ray p px py).point b) := by
  let L := LinearMap.toSpanSingleton ℝ ℂ ((p.re + p.im)⁻¹ • p)
  have inside : h ∈ segment ℝ a b := (segment_eq_Icc (member.1.trans member.2)).symm ▸ member
  have image : L '' segment ℝ a b = segment ℝ (L a) (L b) :=
    image_segment ℝ L.toAffineMap a b
  simpa only [L, LinearMap.toSpanSingleton_apply, ← ray_point_eq_smul p px py] using
    image.subset ⟨h, inside, rfl⟩

end Unfoldings.MonotoneHeightGraph

namespace Unfoldings.HeightSegmentNetwork

variable {ι : Type*} (N : HeightSegmentNetwork ι)

/-- A radial network edge supplies actual coverage of its entire ray height graph. -/
theorem radial_edge_graph_covered (e : ι)
    (px : 0 < (N.last e).re) (py : 0 < (N.last e).im)
    (first_on_ray : (MonotoneHeightGraph.ray (N.last e) px py).point
      (complexDiagonalHeight (N.first e)) = N.first e)
    {h : ℝ} (member : h ∈ Set.Icc (complexDiagonalHeight (N.first e))
      (complexDiagonalHeight (N.last e))) :
    (MonotoneHeightGraph.ray (N.last e) px py).point h ∈ N.carrier := by
  refine Set.mem_iUnion.mpr ⟨e, ?_⟩
  have inside := MonotoneHeightGraph.ray_point_mem_segment (N.last e) px py member
  have tip : (MonotoneHeightGraph.ray (N.last e) px py).point
      (complexDiagonalHeight (N.last e)) = N.last e :=
    MonotoneHeightGraph.ray_point_tip _ _ _
  rwa [first_on_ray, tip] at inside

end Unfoldings.HeightSegmentNetwork
