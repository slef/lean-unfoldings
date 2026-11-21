module

public import Unfoldings.FewestNets.MeshChartIsometry
public import Unfoldings.FewestNets.IcosahedronRealizedCellSupport

/-! The model chart is a physical choice of north frame for the actual roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open MeshStar

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M) (hq : 0 < q)
  (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)

/-- Take the actual site to the north pole using the certificate's two tangent axes. -/
def certificateNorthFrame : Space ≃ₗᵢ[ℝ] Space :=
  R.frame.symm.trans (chartSpatialFrame (R.direction_unit hq) genuine)

theorem certificateNorthFrame_height (N : Space) :
    R.certificateNorthFrame hq genuine N 2 = inner ℝ N (a : Space) := by
  change chartSpatialFrame (R.direction_unit hq) genuine (R.frame.symm N) 2 = _
  rw [chartSpatialFrame_height, ← R.frame.inner_map_map, R.frame.apply_symm_apply, R.center]

/-- The normal slope in this spatial frame is precisely the physical model
coordinate, with no additional transformation of the certificate. -/
theorem certificateNorthFrame_slope (N : Space) :
    (R.certificateNorthFrame hq genuine N 2)⁻¹ •
      Cap.horizontal (R.certificateNorthFrame hq genuine N) =
      R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N) := by
  rw [R.certificateNorthFrame_height]
  change (inner ℝ N (a : Space))⁻¹ •
    Cap.horizontal (chartSpatialFrame (R.direction_unit hq) genuine (R.frame.symm N)) =
      chartPoint M.direction (R.frame.symm ((inner ℝ N (a : Space))⁻¹ • N) - M.direction)
  rw [chartSpatialFrame_horizontal, map_smul]
  let chart := chartPointLinear M.direction
  change (inner ℝ N (a : Space))⁻¹ • chart (R.frame.symm N) =
    chart ((inner ℝ N (a : Space))⁻¹ • R.frame.symm N - M.direction)
  rw [map_sub, map_smul]
  rw [show chart M.direction = 0 from chartPoint_site_eq_zero (R.direction_unit hq) genuine, sub_zero]

/-- Every genuine spherical cell becomes the physical slope polygon in the
north frame used to build its upper roof. -/
theorem image_certificateNorthFrame_slope_eq_physicalPolygon (qbig : 100 ≤ q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    (fun N : Space => (R.certificateNorthFrame hq genuine N 2)⁻¹ •
      Cap.horizontal (R.certificateNorthFrame hq genuine N)) ''
        sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a =
        convexHull ℝ (Set.range M.physicalVertex) := by
  simp_rw [R.certificateNorthFrame_slope hq genuine]
  exact R.image_sphericalVoronoiCell_eq_physicalPolygon qbig hq outward

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
