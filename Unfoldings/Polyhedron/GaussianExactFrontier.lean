module

public import Unfoldings.Polyhedron.GaussianChartBoundary
public import Unfoldings.Polyhedron.GaussianSideDisjoint
public import Unfoldings.Polyhedron.GaussianExtremeCells

/-! A strictly centered Gaussian frontier is exactly the union of its actual incident dual arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- A Gaussian direction shared by two sites lies on the boundary in a
strictly centered stereographic chart of either cell. -/
theorem mem_frontier_gaussianChartRegion_of_mem_cell_inter (i j : F.hullSites)
    (different : j ≠ i) {q : Space} (in_cell : q ∈ F.gaussianCell i)
    (strict : q ∈ interior (F.gaussianCone i))
    (hemisphere : ∀ z ∈ F.gaussianCell i, 0 < inner ℝ q z)
    {x : Plane}
    (present : (northFrame q).symm (inverseStereographic x) ∈ F.gaussianCell i ∩ F.gaussianCell j) :
    x ∈ frontier (F.gaussianChartRegion i q) := by
  let L := northFrame q
  let z := L.symm (inverseStereographic x)
  let normal := L ((i : Space) - (j : Space))
  have unit : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using in_cell.2
  have up : 0 < normal 2 := by
    change 0 < northFrame q ((i : Space) - (j : Space)) 2
    rw [northFrame_height q unit, inner_sub_right, sub_pos]
    exact (mem_interior_finiteHullNormalCone_iff Subtype.val_injective i).mp strict j different
  have chart := F.gaussianChartRegion_properties i in_cell hemisphere
  have in_chart : x ∈ F.gaussianChartRegion i q := by
    intro a
    have h := F.mem_gaussianCone_iff_inner_sub.mp present.1.1 a
    change 0 ≤ inner ℝ ((i : Space) - (a : Space)) z at h
    rw [← L.inner_map_map ((i : Space) - (a : Space)) z, L.apply_symm_apply] at h
    exact h
  have tight : inner ℝ normal (inverseStereographic x) = 0 := by
    have a := F.mem_gaussianCone_iff_inner_sub.mp present.1.1 j
    have b := F.mem_gaussianCone_iff_inner_sub.mp present.2.1 i
    change 0 ≤ inner ℝ ((i : Space) - (j : Space)) z at a
    change 0 ≤ inner ℝ ((j : Space) - (i : Space)) z at b
    have zero : inner ℝ ((i : Space) - (j : Space)) z = 0 := by
      rw [inner_sub_left] at a b ⊢
      linarith only [a, b]
    rw [← L.inner_map_map ((i : Space) - (j : Space)) z, L.apply_symm_apply] at zero
    exact zero
  have on_sphere := (inverseStereographic_support_zero_iff_dist_eq normal up x).mp tight
  have subset : F.gaussianChartRegion i q ⊆
      Metric.closedBall ((normal 2)⁻¹ • horizontal normal) (‖normal‖ / normal 2) := by
    rw [← inverseStereographic_hemisphere_eq_closedBall normal up]
    exact fun y hy => hy j
  have normal_ne : normal ≠ 0 := by
    intro h
    rw [h] at up
    exact (lt_irrefl 0) up
  have radius : 0 < ‖normal‖ / normal 2 := div_pos (norm_pos_iff.mpr normal_ne) up
  rw [chart.1.isClosed.frontier_eq]
  refine ⟨in_chart, fun interior_x => ?_⟩
  have ball := interior_mono subset interior_x
  rw [interior_closedBall _ radius.ne', Metric.mem_ball, on_sphere] at ball
  exact (lt_irrefl _) ball

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- The entire stereographic frontier maps to exactly the actual dual arcs
of the original seams incident to the vertex. -/
theorem inverseStereographic_image_gaussianChart_frontier
    (v : C.Vertex Set.univ) {q : Space}
    (in_cell : q ∈ F.gaussianCell (F.gaussianSiteOfVertex v))
    (strict : q ∈ interior (F.gaussianCone (F.gaussianSiteOfVertex v)))
    (hemisphere : ∀ z ∈ F.gaussianCell (F.gaussianSiteOfVertex v), 0 < inner ℝ q z) :
    inverseStereographic '' frontier (F.gaussianChartRegion (F.gaussianSiteOfVertex v) q) =
      northFrame q '' ⋃ s : {s : C.Seam // v = C.seamVertex s false ∨ v = C.seamVertex s true},
        closedMinorArc (N.normal (C.left s.val).face) (N.normal (C.right s.val).face) := by
  let L := northFrame q
  ext n
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, incident, on_arc⟩ := P.exists_incident_seam_of_mem_gaussianChart_frontier N v q hx
    exact ⟨L.symm (inverseStereographic x), Set.mem_iUnion.mpr ⟨⟨s, incident⟩, on_arc⟩,
      L.apply_symm_apply _⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨s, on_arc⟩ := Set.mem_iUnion.mp hu
    have cells := (P.gaussianCell_inter_seam_eq_normal_arc N s.val).symm ▸ on_arc
    obtain ⟨w, different, two⟩ :
        ∃ w : C.Vertex Set.univ, F.gaussianSiteOfVertex w ≠ F.gaussianSiteOfVertex v ∧
          u ∈ F.gaussianCell (F.gaussianSiteOfVertex v) ∩
            F.gaussianCell (F.gaussianSiteOfVertex w) := by
      rcases s.property with incident | incident
      · refine ⟨C.seamVertex s.val true, ?_, ⟨?_, cells.2⟩⟩
        · intro eq
          have same := congrArg Subtype.val (eq.trans (congrArg F.gaussianSiteOfVertex incident))
          exact gaussianSiteOfVertex_seam_ne s.val same.symm
        · exact incident.symm ▸ cells.1
      · refine ⟨C.seamVertex s.val false, ?_, ⟨?_, cells.1⟩⟩
        · intro eq
          have same := congrArg Subtype.val (eq.trans (congrArg F.gaussianSiteOfVertex incident))
          exact gaussianSiteOfVertex_seam_ne s.val same
        · exact incident.symm ▸ cells.2
    have unit_u : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using two.1.2
    have unit_q : ‖q‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using in_cell.2
    have up : 0 < L u 2 := by
      change 0 < northFrame q u 2
      rw [northFrame_height q unit_q]
      exact hemisphere _ two.1
    let x := stereographicCoord (L u)
    have inverse : inverseStereographic x = L u :=
      inverseStereographic_stereographicCoord ((L.norm_map u).trans unit_u) (by linarith)
    refine ⟨x, F.mem_frontier_gaussianChartRegion_of_mem_cell_inter _ _
      different in_cell strict hemisphere ?_, inverse⟩
    rw [inverse, L.symm_apply_apply]
    exact two

end ConvexBoundary
end Unfoldings.SpatialFolding
