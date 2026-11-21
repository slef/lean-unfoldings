module

public import Unfoldings.FewestNets.IcosahedronSphericalCellSlice
public import Unfoldings.FewestNets.IcosahedronRealizedStar
public import Unfoldings.FewestNets.MeshCornerTransport
public import Unfoldings.FewestNets.MeshChartNormals
public import Unfoldings.Geometry.GnomonicMinorArc

/-! The physical model polygon is exactly the image of the actual spherical cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

theorem heightOne_facetNormal_eq_rawFacetNormal {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (a : meshSites q) (t : MeshFace q) (mem : (a : Space) ∈ Set.range (inscribedCorners t)) :
    (inner ℝ (facetNormal hq t) (a : Space))⁻¹ • facetNormal hq t = rawFacetNormal hq t := by
  rw [inner_facetNormal, (meshGauge_corner_eq_iff qbig hq t a).mpr mem, one_div,
    inv_inv, facetNormal, NormedSpace.norm_smul_normalize]

private theorem meshGnomonic_facetNormal_eq_raw_sub {q : ℕ} (qbig : 100 ≤ q) (hq : 0 < q)
    (a : meshSites q) (t : MeshFace q) (mem : (a : Space) ∈ Set.range (inscribedCorners t)) :
    meshGnomonic (a : Space) (facetNormal hq t) = rawFacetNormal hq t - (a : Space) := by
  rw [meshGnomonic, real_inner_comm (facetNormal hq t) (a : Space),
    heightOne_facetNormal_eq_rawFacetNormal qbig hq a t mem]

namespace MeshStarRealization

variable {q n : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M)

/-- Apply the model's tangent frame to a normal in the height-one affine plane. -/
def siteChartMap : Space →ᵃ[ℝ] Plane where
  toFun := fun x => MeshStar.chartPoint M.direction (R.frame.symm x - M.direction)
  linear := (MeshStar.chartPointLinear M.direction).comp R.frame.symm.toLinearMap
  map_vadd' p v := by
    let chart := MeshStar.chartPointLinear M.direction
    change chart (R.frame.symm (v + p) - M.direction) =
      chart (R.frame.symm v) + chart (R.frame.symm p - M.direction)
    rw [map_add, add_sub_assoc, map_add]

theorem siteChartMap_rawFacetNormal_eq (qbig : 100 ≤ q) (hq : 0 < q)
    (k : Fin (n + 1)) (outward : 0 < inner ℝ M.direction (M.dual k)) :
    R.siteChartMap (rawFacetNormal hq (R.face k)) = M.physicalVertex k := by
  have model : R.frame (M.gnomonicVertex k) =
      rawFacetNormal hq (R.face k) - (a : Space) := by
    rw [M.gnomonicVertex_eq_meshGnomonic_dualDirection k outward, ← meshGnomonic_map,
      R.center, ← R.facetNormal_eq hq k outward,
      meshGnomonic_facetNormal_eq_raw_sub qbig hq a _ (R.site_mem_face k)]
  have a_map : R.frame.symm (a : Space) = M.direction :=
    R.frame.symm_apply_eq.mpr R.center.symm
  have translated : R.frame.symm (rawFacetNormal hq (R.face k)) - M.direction =
      M.gnomonicVertex k := by
    rw [← a_map, ← map_sub, ← model, R.frame.symm_apply_apply]
  change MeshStar.chartPoint M.direction
    (R.frame.symm (rawFacetNormal hq (R.face k)) - M.direction) =
      MeshStar.chartPoint M.direction (M.gnomonicVertex k)
  rw [translated]

theorem image_siteIncidentNormalSlice_eq (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    R.siteChartMap '' siteIncidentNormalSlice hq a =
      Set.range M.physicalVertex := by
  ext p
  constructor
  · rintro ⟨_, ⟨⟨t, mem⟩, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := R.complete t mem
    exact ⟨k, (R.siteChartMap_rawFacetNormal_eq qbig hq k (outward k)).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨rawFacetNormal hq (R.face k), ⟨⟨R.face k, R.site_mem_face k⟩, rfl⟩,
      R.siteChartMap_rawFacetNormal_eq qbig hq k (outward k)⟩

/-- The model vertices generate the whole gnomonic cell, including all its boundary. -/
theorem image_sphericalVoronoiCell_eq_physicalPolygon (qbig : 100 ≤ q) (hq : 0 < q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k)) :
    (fun N : Space => R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N)) ''
      sphericalVoronoiCell (fun s : meshSites q => (s : Space)) a =
        convexHull ℝ (Set.range M.physicalVertex) := by
  rw [← Set.image_image, image_sphericalVoronoiCell_eq_incidentNormalHull qbig hq a,
    AffineMap.image_convexHull, R.image_siteIncidentNormalSlice_eq qbig hq outward]

/-- In the certificate chart, the actual cyclic side is the complete straight
segment between the two physical model vertices. -/
theorem image_meshSide_eq_segment (qbig : 100 ≤ q) (hq : 0 < q)
    (k : Fin (n + 1)) (pred_ne : k ≠ k - 1)
    (outward : ∀ l, 0 < inner ℝ M.direction (M.dual l)) :
    (fun N : Space => R.siteChartMap ((inner ℝ N (a : Space))⁻¹ • N)) ''
        networkEdge (meshEndpoint hq) (edgeOpposite hq (R.face k) (R.index k 2)) =
      segment ℝ (M.physicalVertex k) (M.physicalVertex (k - 1)) := by
  have carrier : networkEdge (meshEndpoint hq) (edgeOpposite hq (R.face k) (R.index k 2)) =
      closedMinorArc (facetNormal hq (R.face k)) (facetNormal hq (R.face (k - 1))) := by
    rw [← R.adjacentFace_pred qbig hq k pred_ne, closedMinorArc_facetNormal_adjacent qbig hq]
    rfl
  have height (l : Fin (n + 1)) : 0 < inner ℝ (facetNormal hq (R.face l)) (a : Space) := by
    have same : inscribedCorners (R.face l) (R.index l 0) = (a : Space) :=
      (R.corner_eq l 0).trans R.center
    exact Eq.mp (congrArg (fun w : Space => 0 < inner ℝ (facetNormal hq (R.face l)) w) same)
      (inner_facetNormal_corner_pos hq (R.face l) (R.index l 0))
  rw [carrier, ← Set.image_image,
    image_heightOne_closedMinorArc (facetNormal_unit hq _) (facetNormal_unit hq _)
      (height k) (height (k - 1)),
    image_segment,
    heightOne_facetNormal_eq_rawFacetNormal qbig hq a _ (R.site_mem_face k),
    heightOne_facetNormal_eq_rawFacetNormal qbig hq a _ (R.site_mem_face (k - 1)),
    R.siteChartMap_rawFacetNormal_eq qbig hq k (outward k),
    R.siteChartMap_rawFacetNormal_eq qbig hq (k - 1) (outward (k - 1))]

end MeshStarRealization
end Unfoldings.FewestNets.Icosahedron
