module

public import Unfoldings.FewestNets.VoronoiNetwork
public import Unfoldings.Polyhedron.GaussianExactFrontier

/-! The Voronoi walls of an inscribed convex triangulation are its dual seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open FewestNets Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- If the origin is interior to the hull, some site is in every open hemisphere. -/
theorem exists_hullSite_inner_pos
    (origin : 0 ∈ interior F.vertexHull) {x : Space} (unit : ‖x‖ = 1) :
    ∃ i : F.hullSites, 0 < inner ℝ x (i : Space) := by
  obtain ⟨r, rpos, inside⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp origin)
  let z := (r / 2) • x
  have member : z ∈ F.vertexHull := inside (by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r / 2), unit, mul_one]
    linarith)
  by_contra! h
  have contain : F.vertexHull ⊆ {y | inner ℝ x y ≤ 0} := by
    rw [F.vertexHull_eq_convexHull_sites]
    exact convexHull_min (fun y hy => h ⟨y, hy⟩)
      (convex_halfSpace_le (innerSL ℝ x).toLinearMap.isLinear 0)
  have low := contain member
  change inner ℝ x ((r / 2) • x) ≤ 0 at low
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, unit, one_pow, mul_one] at low
  linarith

/-- An inscribed site is itself in the strict part of its normal cone. -/
theorem hullSite_mem_interior_gaussianCone
    (inscribed : ∀ i : F.hullSites, ‖(i : Space)‖ = 1) (i : F.hullSites) :
    (i : Space) ∈ interior (F.gaussianCone i) := by
  apply (mem_interior_finiteHullNormalCone_iff Subtype.val_injective i).mpr
  intro j diff
  have nonzero : (i : Space) - (j : Space) ≠ 0 :=
    sub_ne_zero.mpr (fun h => diff (Subtype.ext h.symm))
  have positive := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr nonzero)
  rw [norm_sub_pow_two_real, inscribed i, inscribed j] at positive
  rw [real_inner_self_eq_norm_sq, inscribed i]
  linarith

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- Every tie of inscribed hull sites belongs to a minor arc dual to an
actual seam, and every point of such an arc is a tie. -/
theorem voronoiWalls_eq_iUnion_dual_seams
    (inscribed : ∀ i : F.hullSites, ‖(i : Space)‖ = 1)
    (origin : 0 ∈ interior F.vertexHull) :
    voronoiWalls (fun i : F.hullSites => (i : Space)) =
      ⋃ s : C.Seam, closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  ext n
  constructor
  · rintro ⟨n_sphere, i, j, different, hi, hj⟩
    have ki : (i : Space) ∈ interior (F.gaussianCone i) :=
      F.hullSite_mem_interior_gaussianCone inscribed i
    have center : (i : Space) ∈ F.gaussianCell i :=
      ⟨interior_subset ki, by simpa only [Metric.mem_sphere, dist_zero_right] using inscribed i⟩
    have hemisphere : ∀ z ∈ F.gaussianCell i, 0 < inner ℝ (i : Space) z := by
      intro z hz
      have unit_z : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
      obtain ⟨k, positive⟩ := F.exists_hullSite_inner_pos origin unit_z
      rw [real_inner_comm]
      exact positive.trans_le (hz.1 k)
    let L := northFrame (i : Space)
    let x := stereographicCoord (L n)
    have in_i : n ∈ F.gaussianCell i := ⟨hi, n_sphere⟩
    have in_j : n ∈ F.gaussianCell j := ⟨hj, n_sphere⟩
    have unit_n : ‖n‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using n_sphere
    have up : 0 < L n 2 := by
      rw [northFrame_height _ (inscribed i)]
      exact hemisphere _ in_i
    have inv_eq : inverseStereographic x = L n :=
      inverseStereographic_stereographicCoord ((L.norm_map n).trans unit_n) (by linarith)
    have image : L.symm (inverseStereographic x) = n := by rw [inv_eq, L.symm_apply_apply]
    have frontier_i : x ∈ frontier (F.gaussianChartRegion i (i : Space)) :=
      F.mem_frontier_gaussianChartRegion_of_mem_cell_inter i j different.symm center ki hemisphere
        (image.symm ▸ ⟨in_i, in_j⟩)
    let v := P.vertexEquivGaussianSite.symm i
    have at_v : F.gaussianSiteOfVertex v = i := P.vertexEquivGaussianSite.apply_symm_apply i
    have frontier_v : x ∈ frontier (F.gaussianChartRegion (F.gaussianSiteOfVertex v) (i : Space)) :=
      by rwa [at_v]
    obtain ⟨s, _, on_arc⟩ :=
      P.exists_incident_seam_of_mem_gaussianChart_frontier N v (i : Space) frontier_v
    exact Set.mem_iUnion.mpr ⟨s, image ▸ on_arc⟩
  · intro mem
    obtain ⟨s, on_arc⟩ := Set.mem_iUnion.mp mem
    have cells := (P.gaussianCell_inter_seam_eq_normal_arc N s).symm ▸ on_arc
    refine ⟨cells.1.2, _, _, ?_, cells.1.1, cells.2.1⟩
    exact fun eq => gaussianSiteOfVertex_seam_ne s (congrArg Subtype.val eq)

end ConvexBoundary
end Unfoldings.SpatialFolding
