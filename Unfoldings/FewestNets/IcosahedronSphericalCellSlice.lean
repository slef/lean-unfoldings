module

public import Unfoldings.FewestNets.IcosahedronNormalCellHull
public import Unfoldings.FewestNets.VoronoiNetwork

/-! Height-one scaling maps the actual spherical cell onto the incident facet hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open NormedSpace

theorem inner_siteIncidentNormalSlice_eq_one {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (a : meshSites q) {x : Space} (hx : x ∈ convexHull ℝ (siteIncidentNormalSlice hq a)) :
    inner ℝ x (a : Space) = 1 := by
  have subset : convexHull ℝ (siteIncidentNormalSlice hq a) ⊆
      {x | inner ℝ x (a : Space) = 1} := by
    apply convexHull_min
    · rintro _ ⟨t, rfl⟩
      change inner ℝ (rawFacetNormal hq t.val) (a : Space) = 1
      rw [inner_rawFacetNormal]
      exact (meshGauge_corner_eq_iff qbig hq t.val a).mpr t.property
    · have h := convex_hyperplane (innerSL ℝ (a : Space)).toLinearMap.isLinear (1 : ℝ)
      simpa only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, real_inner_comm] using h
  exact subset hx

theorem inner_pos_of_mem_meshSphericalCell {q : ℕ} (hq : 0 < q)
    (a : meshSites q) {n : Space}
    (hn : n ∈ sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a) :
    0 < inner ℝ n (a : Space) := by
  have unit : ‖n‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hn.2
  obtain ⟨b, positive⟩ := exists_meshSite_inner_pos hq unit
  exact positive.trans_le (hn.1 b)

theorem image_sphericalVoronoiCell_eq_incidentNormalHull {q : ℕ}
    (qbig : 100 ≤ q) (hq : 0 < q) (a : meshSites q) :
    (fun n : Space => (inner ℝ n (a : Space))⁻¹ • n) ''
      sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a =
        convexHull ℝ (siteIncidentNormalSlice hq a) := by
  ext x
  constructor
  · rintro ⟨n, inside, rfl⟩
    exact (mem_normalCone_iff_mem_siteIncidentNormalSlice qbig hq a n
      (inner_pos_of_mem_meshSphericalCell hq a inside)).mp inside.1
  · intro hx
    have height := inner_siteIncidentNormalSlice_eq_one qbig hq a hx
    have ne : x ≠ 0 := by
      intro zero
      rw [zero, inner_zero_left] at height
      exact zero_ne_one height
    let n := normalize x
    have value : inner ℝ n (a : Space) = ‖x‖⁻¹ := by
      dsimp only [n, NormedSpace.normalize]
      rw [real_inner_smul_left, height, mul_one]
    have rescale : (inner ℝ n (a : Space))⁻¹ • n = x := by
      rw [value, inv_inv]
      exact norm_smul_normalize x
    have positive : 0 < inner ℝ n (a : Space) := by
      rw [value]
      exact inv_pos.mpr (norm_pos_iff.mpr ne)
    refine ⟨n, ⟨(mem_normalCone_iff_mem_siteIncidentNormalSlice qbig hq a n positive).mpr
      (rescale.symm ▸ hx), ?_⟩, rescale⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize ne

end Unfoldings.FewestNets.Icosahedron
