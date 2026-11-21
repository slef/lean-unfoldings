module

public import Unfoldings.FewestNets.IcosahedronConvexMesh

/-! The normalized fine triangles cover exactly the frontier of their convex hull. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open Set
open scoped BigOperators

theorem hullGauge_smul {q : ℕ} (hq : 0 < q) {a : ℝ} (ha : 0 ≤ a) (x : Space) :
    hullGauge hq (a • x) = a * hullGauge hq x := by
  obtain ⟨t, ht⟩ := radialMesh_cover hq x
  have in_cone : a • x ∈ radialTriangleCone (inscribedCorners t) := by
    obtain ⟨w, positive, xeq⟩ := ht
    exact ⟨fun k => a * w k, fun k => mul_nonneg ha (positive k), by
      rw [xeq, Finset.smul_sum]
      simp only [smul_smul]⟩
  rw [hullGauge_eq_meshGauge hq t in_cone, hullGauge_eq_meshGauge hq t ht, map_smul, smul_eq_mul]

/-- The frontier lies at level one of the radial gauge. -/
theorem frontier_meshHull_eq_level {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    frontier (meshHull q) = {x | hullGauge hq x = 1} := by
  have isclosed : IsClosed (meshHull q) := by
    rw [meshHull_eq_sublevel qbig hq]
    exact isClosed_le (continuous_hullGauge hq) continuous_const
  ext x
  rw [frontier, isclosed.closure_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨inHull, notInside⟩
    have le : hullGauge hq x ≤ 1 := by
      rw [meshHull_eq_sublevel qbig hq] at inHull
      exact inHull
    refine le_antisymm le (le_of_not_gt fun strict => notInside ?_)
    have sub : {y | hullGauge hq y < 1} ⊆ meshHull q := by
      rw [meshHull_eq_sublevel qbig hq]
      exact fun _ (hy : hullGauge hq _ < 1) => hy.le
    exact interior_maximal sub (isOpen_lt (continuous_hullGauge hq) continuous_const) strict
  · intro (level : hullGauge hq x = 1)
    refine ⟨(meshHull_eq_sublevel qbig hq).symm ▸ level.le, fun inside => ?_⟩
    have x_ne : x ≠ 0 := by
      intro zero
      rw [zero, hullGauge_zero] at level
      norm_num at level
    obtain ⟨ε, eps, ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp inside)
    let t := ε / (2 * ‖x‖)
    have normpos := norm_pos_iff.mpr x_ne
    have tp : 0 < t := div_pos eps (by positivity)
    have inBall : (1 + t) • x ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos tp]
      dsimp only [t]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * ‖x‖)]
      nlinarith only [mul_pos eps normpos]
    have le : hullGauge hq ((1 + t) • x) ≤ 1 := by
      have member := ball inBall
      rw [meshHull_eq_sublevel qbig hq] at member
      exact member
    rw [hullGauge_smul hq (by positivity : 0 ≤ 1 + t), level, mul_one] at le
    linarith only [tp, le]

/-- The normalized grid faces are a closed cover of the boundary of the actual inscribed hull. -/
theorem frontier_meshHull_eq_triangles {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q) :
    frontier (meshHull q) = ⋃ t : MeshFace q, convexHull ℝ (Set.range (inscribedCorners t)) := by
  rw [frontier_meshHull_eq_level qbig hq]
  ext x
  constructor
  · intro (level : hullGauge hq x = 1)
    obtain ⟨t, ht⟩ := radialMesh_cover hq x
    rw [hullGauge_eq_meshGauge hq t ht] at level
    obtain ⟨w, positive, xeq⟩ := ht
    have total : ∑ k, w k = 1 := by
      rw [xeq, map_sum] at level
      simpa only [map_smul, meshGauge_corner, smul_eq_mul, mul_one] using level
    exact Set.mem_iUnion.mpr ⟨t, mem_convexHull_of_exists_fintype w _ positive total
      (fun k => Set.mem_range_self k) xeq.symm⟩
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    obtain ⟨w, positive, total, xeq⟩ := TriangleGrid.exists_weights_of_mem_convexHull_range _ ht
    change hullGauge hq x = 1
    rw [hullGauge_eq_meshGauge hq t ⟨w, positive, xeq.symm⟩, ← xeq, map_sum]
    simpa only [map_smul, meshGauge_corner, smul_eq_mul, mul_one] using total

end Unfoldings.FewestNets.Icosahedron
