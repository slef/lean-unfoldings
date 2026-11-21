module

public import Unfoldings.Polyhedron.GaussianBoundaryCover
public import Unfoldings.Geometry.StereographicArea

/-! Actual original seam arcs cover Gaussian frontiers in the stereographic charts used in the
two-side bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

open Filter Topology Cap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

/-- Changing from a stereographic chart to a gnomonic chart preserves the
frontier wherever the Gaussian cell is contained in the gnomonic hemisphere. -/
theorem exists_gnomonic_frontier_of_stereographic_frontier (i : F.hullSites) {q r : Space}
    (unit : ‖r‖ = 1) (hemisphere : ∀ n ∈ F.gaussianCell i, 0 < inner ℝ r n)
    {x : Plane} (on_frontier : x ∈ frontier (F.gaussianChartRegion i q)) :
    ∃ p ∈ frontier (gnomonicRegion (northFrame r '' F.gaussianCell i)),
      gnomonicNormal p = northFrame r ((northFrame q).symm (inverseStereographic x)) := by
  let Q := northFrame q
  let R := northFrame r
  let n (y : Plane) := Q.symm (inverseStereographic y)
  let rotated (y : Plane) := R (n y)
  let height (y : Plane) := rotated y 2
  let coord (y : Plane) := (height y)⁻¹ • horizontal (rotated y)
  let G := gnomonicRegion (R '' F.gaussianCell i)
  have closed_chart : IsClosed (F.gaussianChartRegion i q) := by
    rw [show F.gaussianChartRegion i q = ⋂ j : F.hullSites,
      {y | 0 ≤ inner ℝ (Q ((i : Space) - j)) (inverseStereographic y)} by
        ext y
        simp only [gaussianChartRegion, Q, Set.mem_ofPred_eq, Set.mem_iInter]]
    exact isClosed_iInter fun j => isClosed_le continuous_const
      (continuous_const.inner continuous_inverseStereographic)
  have charts (y : Plane) : y ∈ F.gaussianChartRegion i q ↔ n y ∈ F.gaussianCell i := by
    have Qn : Q (n y) = inverseStereographic y := Q.apply_symm_apply _
    have unit_n : ‖n y‖ = 1 := (Q.symm.norm_map _).trans (inverseStereographic_unit y)
    have sphere_n : n y ∈ Metric.sphere 0 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using unit_n
    constructor
    · intro h
      refine ⟨F.mem_gaussianCone_iff_inner_sub.mpr (fun j => ?_), sphere_n⟩
      rw [← Q.inner_map_map ((i : Space) - j) (n y), Qn]
      exact h j
    · intro h j
      have test := F.mem_gaussianCone_iff_inner_sub.mp h.1 j
      rwa [← Q.inner_map_map ((i : Space) - j) (n y), Qn] at test
  rw [closed_chart.frontier_eq] at on_frontier
  have present := (charts x).mp on_frontier.1
  have up : 0 < height x := by
    change 0 < northFrame r (n x) 2
    rw [northFrame_height r unit]
    exact hemisphere _ present
  have point_eq (y : Plane) (positive : 0 < height y) :
      gnomonicNormal (coord y) = rotated y := by
    have unit_y : ‖rotated y‖ = 1 := (R.norm_map _).trans
      ((Q.symm.norm_map _).trans (inverseStereographic_unit y))
    exact gnomonicNormal_slope _ unit_y positive
  have coord_in : coord x ∈ G := by
    change gnomonicNormal (coord x) ∈ R '' F.gaussianCell i
    rw [point_eq x up]
    exact Set.mem_image_of_mem _ present
  have not_interior : coord x ∉ interior G := by
    intro in_interior
    have rotated_cont : Continuous rotated :=
      R.continuous.comp (Q.symm.continuous.comp continuous_inverseStereographic)
    have height_cont : Continuous height := (EuclideanSpace.proj 2).continuous.comp rotated_cont
    have coord_cont : ContinuousAt coord x :=
      (height_cont.continuousAt.inv₀ up.ne').smul
        (horizontalCLM.continuous.comp rotated_cont).continuousAt
    have nearby_up : ∀ᶠ y in 𝓝 x, 0 < height y :=
      height_cont.continuousAt.eventually (lt_mem_nhds up)
    have nearby_chart : ∀ᶠ y in 𝓝 x, coord y ∈ G :=
      coord_cont (mem_interior_iff_mem_nhds.mp in_interior)
    have original_chart : F.gaussianChartRegion i q ∈ 𝓝 x := by
      filter_upwards [nearby_up, nearby_chart] with y h_up h_chart
      change gnomonicNormal (coord y) ∈ R '' F.gaussianCell i at h_chart
      rw [point_eq y h_up] at h_chart
      exact (charts y).mpr (R.injective.mem_set_image.mp h_chart)
    exact on_frontier.2 (mem_interior_iff_mem_nhds.mpr original_chart)
  have closed_gnomonic : IsClosed G := Cap.isClosed_gnomonicRegion
    ((F.isCompact_gaussianCell i).image R.continuous).isClosed
  exact ⟨coord x, closed_gnomonic.frontier_eq.symm ▸ ⟨coord_in, not_interior⟩, point_eq x up⟩

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- Every frontier point of the actual stereographic Gaussian chart comes
from an original incident dual arc. -/
theorem exists_incident_seam_of_mem_gaussianChart_frontier
    (v : C.Vertex Set.univ) (q : Space) {x : Plane}
    (on_frontier : x ∈ frontier (F.gaussianChartRegion (F.gaussianSiteOfVertex v) q)) :
    ∃ s : C.Seam, (v = C.seamVertex s false ∨ v = C.seamVertex s true) ∧
      (northFrame q).symm (inverseStereographic x) ∈
        closedMinorArc (N.normal (C.left s).face) (N.normal (C.right s).face) := by
  obtain ⟨r, unit, hemisphere, cover⟩ :=
    P.exists_gaussian_frontier_incident_seam_cover N v
  obtain ⟨p, hp, equal⟩ :=
    F.exists_gnomonic_frontier_of_stereographic_frontier _ unit hemisphere on_frontier
  obtain ⟨s, incident, on_arc⟩ := cover p hp
  rw [equal, (northFrame r).symm_apply_apply] at on_arc
  exact ⟨s, incident, on_arc⟩

end ConvexBoundary
end Unfoldings.SpatialFolding
